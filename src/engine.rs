// The Salewski Chess Engine -- ported from Nim to Rust as a tiny excercise while learning the Rust language
// v 0.2 -- 26-JAN-2024
// (C) 2015 - 2032 Dr. Stefan Salewski
// All rights reserved.
//
// Initially developed from scratch, based on the fundamental ideas of alpha-beta-prunning only.
// The move generation is based on old ideas of precalculation, similar as it was done
// in early GNU-Chess engines in the late 1980's.
//
// TODO:
// create a real GUI
// avoid global variables, make board a parameter of abeta() // Done in Rust port
// make transposition table size configurable?
// make aggression configurable
// make aggression depending on winning/loosing
// add optional random noise

// #![allow(dead_code)]
// #![allow(non_camel_case_names)]
// #![allow(non_snake_case)]
// #![allow(non_upper_case_globals)]

use bit_set::BitSet;
use core::ops::Range;
use std::cmp::{max, min};
use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::time::{Duration, Instant};

fn print_variable_type<K>(_: &K) {
    println!("{}", std::any::type_name::<K>())
}

// #[allow(non_camel_case_types)]

// #[derive(Default)]
// #[derive(Debug)]
pub struct Game {
    table_put: i64, // some fields like this are only for statistics and debugging
    table_col: i64,
    ab_call: i64,
    score_hash_succ: i64,
    floor_hash_succ: i64,
    hash_succ: i64,
    null_move_succ_1: i64,
    null_move_succ_2: i64,
    re_eval_skip: i64,
    max_delta_len: i64,
    is_endgame: bool,
    cut_time: std::time::Duration,
    start_time: std::time::Instant,
    tt: Vec<TTE>,
    debug_list: Vec<String>,
    history: HashMap<BitBuffer192, i32>,
    board: Board,
    has_moved: HasMoved,
    pawn_march: PawnMarch,
    freedom: Freedom,
    pawn_path: [Path; 2],
    knight_path: Path,
    bishop_path: Path,
    rook_path: Path,
    king_path: Path,
    pjm: i64,
}

const CORE_BIT_BUFFER_SIZE: usize = 24; // size with huffman compression
const HASH_BIT_BUFFER_SIZE: usize = 32; // plus 8 bytes for hash when debugging
const BIT_BUFFER_SIZE: usize = bit_buffer_size();

const fn bit_buffer_size() -> usize {
    #[cfg(not(feature = "salewskiChessDebug"))]
    {
        CORE_BIT_BUFFER_SIZE
    }
    #[cfg(feature = "salewskiChessDebug")]
    {
        HASH_BIT_BUFFER_SIZE
    }
}

// this syntas is also possible
const JUST_TEST: usize = if cfg!(feature = "salewskiChessDebug") {
    2
} else {
    7
};

pub fn new_game() -> Game {
    // default options
    if cfg!(debug_assertions) {
        println!("compiled in debug mode");
    }
    #[cfg(debug_assertions)]
    {
        println!("compiled in debug mode");
    }

    // cargo run --features=salewskiChessDebug
    if cfg!(feature = "salewskiChessDebug") {
        println!("salewskiChessDebug");
    }
    #[cfg(feature = "salewskiChessDebug")]
    {
        println!("salewskiChessDebug2");
    }

    let mut g = Game {
        table_put: 0,
        table_col: 0,
        ab_call: 0,
        score_hash_succ: 0,
        floor_hash_succ: 0,
        hash_succ: 0,
        null_move_succ_1: 0,
        null_move_succ_2: 0,
        re_eval_skip: 0,
        max_delta_len: 0,
        is_endgame: false,
        cut_time: Duration::new(0, 0),
        start_time: Instant::now(),
        tt: Vec::with_capacity(TTE_SIZE),
        debug_list: Vec::new(),
        history: HashMap::new(),
        board: SETUP,
        has_moved: BitSet::new(),
        pawn_march: core::array::from_fn(|_| BitSet::new()),
        freedom: [[0; 64]; 13],
        pawn_path: [[[Gnu {
            pos: 0,
            nxt_dir_idx: 0,
        }; 64]; 64]; 2],
        knight_path: [[Gnu {
            pos: 0,
            nxt_dir_idx: 0,
        }; 64]; 64],
        bishop_path: [[Gnu {
            pos: 0,
            nxt_dir_idx: 0,
        }; 64]; 64],
        rook_path: [[Gnu {
            pos: 0,
            nxt_dir_idx: 0,
        }; 64]; 64],
        king_path: [[Gnu {
            pos: 0,
            nxt_dir_idx: 0,
        }; 64]; 64],
        pjm: -1,
    };
    g.tt.resize(TTE_SIZE, Default::default());
    init_pawn(&mut g, COLOR_WHITE as i64);
    init_pawn(&mut g, COLOR_BLACK as i64);
    init_bishop(&mut g);
    init_knight(&mut g);
    init_king(&mut g);
    init_rook(&mut g);
    g
}

fn reset_statistics(g: &mut Game) {
    g.table_put = 0;
    g.table_col = 0;
    g.ab_call = 0;
    g.score_hash_succ = 0;
    g.floor_hash_succ = 0;
    g.hash_succ = 0;
    g.null_move_succ_1 = 0;
    g.null_move_succ_2 = 0;
    g.re_eval_skip = 0;
    g.max_delta_len = 0;
}

fn write_statistics(g: &Game) {
    println!("ab_call: {}", g.ab_call);
    println!("score_hash_succ: {}", g.score_hash_succ);
    println!("floor_hash_succ: {}", g.floor_hash_succ);
    println!("hash_succ: {}", g.hash_succ);
    println!("table_put: {}", g.table_put);
    println!("table_col: {}", g.table_col);
    println!("null_move_succ_1: {}", g.null_move_succ_1);
    println!("null_move_succ_2: {}", g.null_move_succ_2);
    println!("re_eval_skip: {}", g.re_eval_skip);
    println!("max_delta_len: {}", g.max_delta_len);
}

type BitBuffer192 = [u8; bit_buffer_size()];

const MAX_DEPTH: usize = 15; // other values should work as well

const VOID_ID: i64 = 0;
const PAWN_ID: i64 = 1;
const KNIGHT_ID: i64 = 2;
const BISHOP_ID: i64 = 3;
const ROOK_ID: i64 = 4;
const QUEEN_ID: i64 = 5;
const KING_ID: i64 = 6;
const ARRAY_BASE_6: i64 = 6;
const W_PAWN: i64 = PAWN_ID;
const W_KNIGHT: i64 = KNIGHT_ID;
const W_BISHOP: i64 = BISHOP_ID;
const W_ROOK: i64 = ROOK_ID;
const W_QUEEN: i64 = QUEEN_ID;
const W_KING: i64 = KING_ID;
const B_PAWN: i64 = -PAWN_ID;
const B_KNIGHT: i64 = -KNIGHT_ID;
const B_BISHOP: i64 = -BISHOP_ID;
const B_ROOK: i64 = -ROOK_ID;
const B_QUEEN: i64 = -QUEEN_ID;
const B_KING: i64 = -KING_ID;

const FORWARD: i32 = 8;
const SIDEWARD: i32 = 1;
const S: i32 = FORWARD;
const O: i32 = SIDEWARD;
const N: i32 = -S;
const W: i32 = -O;
const NO: i32 = N + O;
const SO: i32 = S + O;
const NW: i32 = N + W;
const SW: i32 = S + W;

const PAWN_DIRS_WHITE: [i32; 4] = [
    FORWARD - SIDEWARD,
    FORWARD + SIDEWARD,
    FORWARD,
    FORWARD + FORWARD,
];
const BISHOP_DIRS: [i32; 4] = [NO, SO, NW, SW];
const ROOK_DIRS: [i32; 4] = [N, O, S, W];
const KNIGHT_DIRS: [i32; 8] = [
    N + NO,
    N + NW,
    W + NW,
    W + SW,
    O + NO,
    O + SO,
    S + SO,
    S + SW,
];
const KING_DIRS: [i32; 8] = [N, O, S, W, NO, SO, NW, SW]; // KING_DIRS = BISHOP_DIRS + ROOK_DIRS

//Agility = [0, 4, 6, 5, 3, 2, 1] // Pawn .. King, how often is that piece used in smart average game play.

// we try to keep all the values small to fit in two bytes
const AB_INF: i32 = 32000; // more than the summed value of all pieces
const VOID_VALUE: i32 = 0;
const PAWN_VALUE: i32 = 100;
const KNIGHT_VALUE: i32 = 300;
const BISHOP_VALUE: i32 = 300;
const ROOK_VALUE: i32 = 500;
const QUEEN_VALUE: i32 = 900;
pub const KING_VALUE: i32 = 18000; // more than the summed value of all other pieces
pub const KING_VALUE_DIV_2: i32 = KING_VALUE / 2;
pub const SURE_CHECKMATE: i32 = KING_VALUE / 2; // still more than the summed value of all other pieces, but less than value of a king

const FIGURE_VALUE: [i32; KING_ID as usize + 1] = [
    VOID_VALUE,
    PAWN_VALUE,
    KNIGHT_VALUE,
    BISHOP_VALUE,
    ROOK_VALUE,
    QUEEN_VALUE,
    KING_VALUE,
];

const SETUP: [i64; 64] = [
    W_ROOK, W_KNIGHT, W_BISHOP, W_KING, W_QUEEN, W_BISHOP, W_KNIGHT, W_ROOK, W_PAWN, W_PAWN,
    W_PAWN, W_PAWN, W_PAWN, W_PAWN, W_PAWN, W_PAWN, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, B_PAWN, B_PAWN, B_PAWN, B_PAWN, B_PAWN, B_PAWN,
    B_PAWN, B_PAWN, B_ROOK, B_KNIGHT, B_BISHOP, B_KING, B_QUEEN, B_BISHOP, B_KNIGHT, B_ROOK,
];

// the traditional row and column designators -- B prefix for Board
const BA: i32 = 7;
const BB: i32 = 6;
const BC: i32 = 5;
const BD: i32 = 4;
const BE: i32 = 3;
const BF: i32 = 2;
const BG: i32 = 1;
const BH: i32 = 0;
const B1: i32 = 0;
const B2: i32 = 1;
const B3: i32 = 2;
const B4: i32 = 3;
const B5: i32 = 4;
const B6: i32 = 5;
const B7: i32 = 6;
const B8: i32 = 7;

const POS_RANGE: Range<i8> = 0..64;

type Color = i64;
const COLOR_BLACK: i32 = -1;
const COLOR_WHITE: i32 = 1;
type ColorIndex = i8; //0 .. 1
type Position = i8; //0 .. 63
type Col = i8; //0 .. 7
type Row = i8; //0 .. 7
type FigureID = i64;
//#[derive(Clone, Copy)]
pub type Board = [FigureID; 64];
type Freedom = [[i64; 64]; 13]; // VOID_ID..KING_ID; Maybe we should call it happyness

const WR0: i32 = 0; // initial positions of King and Rook for castling tests
const WK3: i32 = 3;
const WR7: i32 = 7;
const BR56: i32 = 56;
const BK59: i32 = 59;
const BR63: i32 = 63;

type ChessSquare = i8; // range[0 .. 63];
type ChessSquares = BitSet; // set[ChessSquare];
type HasMoved = BitSet; //set[ChessSquare];
type PawnMarch = [ChessSquares; 4 + 32 + 1]; // array[-4 .. 32, ChessSquares];

#[derive(Copy, Clone)]
struct Gnu {
    // move precalculation is based on old gnuchess ideas...
    pos: i8,
    nxt_dir_idx: i64,
}

type Path = [[Gnu; 64]; 64];

const IGNORE_MARKER_LOW_INT16: i16 = i16::MIN;
const INVALID_SCORE: i16 = i16::MIN;
const LOWEST_SCORE: i16 = -i16::MAX; // allows inverting the sign

pub type State = i32;
const STATE_PLAYING: i32 = 0;
const STATE_STALEMATE: i32 = 1;
const STATE_CHECKMATE: i32 = 2;
const STATE_NO_VALID_MOVE: i32 = 3;
const STATE_CAN_CAPTURE_KING: i32 = 4;

#[derive(Copy, Clone, Debug, Default)]
pub struct KK {
    // source figure, destination figure, source index, destination index
    s: i16, // score
    sf: i8,
    df: i8,
    si: i8,
    pub di: i8,
    eval_depth: i8,
    promote_to: i8, // we may use this to indicate pawn to queen/knight promotion
}

type KKS = Vec<KK>;

#[derive(Copy, Clone, Default)]
struct Guide1 {
    // size is 5 byte -- not that nice
    s: i16,
    si: i8,
    di: i8,
    promote_to: i8,
}

#[derive(Copy, Clone, Default)]
struct Guide2 {
    s: i16,
}

type HashLine1 = [Guide1; MAX_DEPTH + 1];
type HashLine2 = [Guide2; MAX_DEPTH + 1];

#[derive(Default, Clone)]
struct HashResult {
    score: HashLine1, // exact values
    floor: HashLine2, // lower bounds
    kks: KKS,
    kks_high: i64,
    pri: i64,
    king_pos: i64,
    pop_cnt: i64,
    control: ChessSquares,
    state: State,
    in_check: bool,
}

#[derive(Default, Clone)]
struct TTE {
    res: HashResult,
    key: BitBuffer192,
}

//template `>=!`(a: var SomeNumber; b: SomeNumber) =
//  if a < b: a = b

fn lift(a: &mut i64, b: i64) {
    if *a < b {
        *a = b
    }
}

const TTE_SIZE: usize = 1024 * 1024 * 2; // must be a power of 2
const TT_TRY: i32 = 5;

//template umod8(i: typed): untyped = i and 7

//template udiv8(i: typed): untyped = i shr 3

fn odd(i: i8) -> bool {
    (i & 1) != 0
}

fn even(i: i8) -> bool {
    (i & 1) == 0
}

fn sign(x: i64) -> i64 {
    (x > 0) as i64 - (x < 0) as i64
}

fn same_sign(a: i64, b: i64) -> bool {
    (a ^ b) >= 0
}

fn sqr(i: i64) -> i64 {
    i * i
}

fn is_a_pawn(i: i8) -> bool {
    i == W_PAWN as i8 || i == B_PAWN as i8
}

fn is_a_king(i: i8) -> bool {
    i == W_KING as i8 || i == B_KING as i8
}

fn col_idx(c: Color) -> ColorIndex {
    (c as i8 + 1) >> 1
}

fn is_white(c: Color) -> bool {
    c == COLOR_WHITE as i64
}

fn is_black(c: Color) -> bool {
    c == COLOR_BLACK as i64
}

fn opp_color(c: Color) -> Color {
    (-c as i64) as Color
}

fn col(p: Position) -> Col {
    p % 8
}

fn row(p: Position) -> Row {
    p / 8
}

fn base_row(p: Position) -> bool {
    p < 8 || p > 55
}

fn rows_to_go(p: Position, c: Color) -> i8 {
    if c == (COLOR_BLACK as i64) {
        row(p)
    } else {
        7 - row(p)
    }
}

fn board_hash(b: Board) -> u64 {
    let mut hasher = DefaultHasher::new();
    Hash::hash_slice(&b, &mut hasher);
    hasher.finish()
}

fn bit_buffer_hash(key: &BitBuffer192) -> u64 {
    let mut hasher = DefaultHasher::new();
    Hash::hash_slice(&key[0..CORE_BIT_BUFFER_SIZE], &mut hasher);
    hasher.finish()
}

fn get_tte<'a>(g: &'a mut Game, key: BitBuffer192) -> isize {
    debug_assert!(g.tt.len() == TTE_SIZE);
    let h0 = bit_buffer_hash(&key);
    for i in 0..(TT_TRY + 1) {
        let h = (h0.wrapping_add(i as u64)) as usize & ((TTE_SIZE - 1) as usize);
        if g.tt[h].key[0..CORE_BIT_BUFFER_SIZE] == key[0..CORE_BIT_BUFFER_SIZE] {
            if BIT_BUFFER_SIZE == HASH_BIT_BUFFER_SIZE {
                let bh = board_hash(g.board).to_le_bytes();
                debug_assert!(key[CORE_BIT_BUFFER_SIZE..HASH_BIT_BUFFER_SIZE] == bh);
                debug_assert!(g.tt[h].key[CORE_BIT_BUFFER_SIZE..HASH_BIT_BUFFER_SIZE] == bh);
            }
            return h as isize;
        }
    }
    return -1;
}

fn debug_inc(x: &mut i64) {
    if cfg!(feature = "salewskiChessDebug") {
        *x += 1;
    }
}

fn put_tte(g: &mut Game, key: BitBuffer192, mut res: HashResult, pri: i64, hash_pos: isize) {
    debug_assert!(g.tt.len() == TTE_SIZE);
    debug_inc(&mut g.table_put);
    if hash_pos >= 0 {
        res.pri = pri;
        g.tt[hash_pos as usize].res = res;
        return;
    }
    let h0 = bit_buffer_hash(&key);
    for i in 0..(TT_TRY + 1) {
        let h = (h0.wrapping_add(i as u64)) as usize & ((TTE_SIZE - 1) as usize);
        if g.tt[h].res.pri < pri {
            res.pri = pri;
            g.tt[h].res = res;
            g.tt[h].key = key;
            return;
        }
    }
    debug_inc(&mut g.table_col);
}

const HASH_RESULT_ALL_ZERO: HashLine1 = [Guide1 {
    s: INVALID_SCORE,
    si: 0,
    di: 0,
    promote_to: 0,
}; MAX_DEPTH + 1];

fn init_hr(hr: &mut HashResult) {
    hr.score = HASH_RESULT_ALL_ZERO;
    for mut el in hr.floor {
        el.s = INVALID_SCORE;
    }
    hr.state = STATE_PLAYING;
}

static FIGURES: [&str; 13] = [
    unsafe { std::str::from_utf8_unchecked(&[0xe2, 0x99, 0x9a]) },
    unsafe { std::str::from_utf8_unchecked(&[0xe2, 0x99, 0x9B]) },
    unsafe { std::str::from_utf8_unchecked(&[0xe2, 0x99, 0x9C]) },
    unsafe { std::str::from_utf8_unchecked(&[0xe2, 0x99, 0x9D]) },
    unsafe { std::str::from_utf8_unchecked(&[0xe2, 0x99, 0x9E]) },
    unsafe { std::str::from_utf8_unchecked(&[0xe2, 0x99, 0x9F]) },
    unsafe { std::str::from_utf8_unchecked(&[0x20]) },
    unsafe { std::str::from_utf8_unchecked(&[0xe2, 0x99, 0x99]) },
    unsafe { std::str::from_utf8_unchecked(&[0xe2, 0x99, 0x98]) },
    unsafe { std::str::from_utf8_unchecked(&[0xe2, 0x99, 0x97]) },
    unsafe { std::str::from_utf8_unchecked(&[0xe2, 0x99, 0x96]) },
    unsafe { std::str::from_utf8_unchecked(&[0xe2, 0x99, 0x95]) },
    unsafe { std::str::from_utf8_unchecked(&[0xe2, 0x99, 0x94]) },
];

fn p(b: Board) {
    //#[cfg(feature = "salewskiChessDebug")]
    {
        for (i, c) in b.iter().enumerate() {
            print!("{}", FIGURES[(6 + *c) as usize]);
            if (i + 1) % 8 == 0 {
                println!("")
            }
        }
    }
}

fn pf(b: Board) {
    #[cfg(feature = "salewskiChessDebug")]
    {
        for (i, c) in b.iter().enumerate() {
            print!(" {} ", c);
            if (i + 1) % 8 == 0 {
                println!("")
            }
        }
    }
}

fn is_void_at(g: &Game, p: Position) -> bool {
    g.board[p as usize] == VOID_ID
}

fn is_a_pawn_at(g: &Game, p: Position) -> bool {
    sqr(g.board[p as usize]) == PAWN_ID
}

fn is_a_king_at(g: &Game, p: Position) -> bool {
    sqr(g.board[p as usize]) == KING_ID * KING_ID
}

fn check(g: &Game) {
    let mut p: i64 = 0;
    for i in g.board {
        if i != VOID_ID {
            p += 1;
        }
    }
    debug_assert!(p <= 32);
}

/*
fn simpleWriteToBitBuffer(g: &Game, c: Color) -> BitBuffer192 {
    let mut result: BitBuffer192 = [0; 32];
    debug_assert!(std::mem::size_of_val(&result) == 32);
    let mut empty: u8 = KING_ID as u8;
    if c == COLOR_BLACK as i64 {
        // encode the color of active player in empty squares
        empty = 15
    }
    for i in (0..=31).rev() {
        //.step_by(1) {
        let mut a = (g.board[i] + KING_ID) as u8; // a non negative value now, so we can use bit masking
        let mut b = (g.board[i + 32] + KING_ID) as u8;
        if a == KING_ID as u8 {
            a = empty
        }
        if b == KING_ID as u8 {
            b = empty
        }
        debug_assert!(a >= 0 && a <= 15);
        debug_assert!(b >= 0 && b <= 15);
        result[i] = (a << 4) | b;
    }
    result
}
*/

// experimental huffman-like compression
// needed bytes = (4*6+3*2*2*5+8*2*3+32 + 3)/8.0 = 20.875
// so 22 bytes should be enough even for an additional queen. But we might use 24 bytes.
fn much_faster_write_to_bit_buffer(g: &Game, c: Color) -> BitBuffer192 {
    const L: [usize; 13] = [6, 6, 5, 5, 5, 3, 1, 3, 5, 5, 5, 6, 6]; // the number of bits
    const CODE: [u64; 13] = [
        0b111100, 0b111101, 0b11000, 0b11001, 0b11010, 0b100, 0b0, 0b101, 0b11011, 0b11100,
        0b11101, 0b111110, 0b111111,
    ]; // the huffman bit pattern
    let mut collector: [u8; 4 * 8] = [0; 32];
    let mut result: BitBuffer192 = [0; BIT_BUFFER_SIZE];
    let mut buf: u64 = 0;
    let mut shift: usize = 0;
    let mut bpos: usize = 0; // bype position in collector
    let mut bp; // board position
    debug_assert!(std::mem::size_of_val(&result) == BIT_BUFFER_SIZE); // 24 byte size should be enough

    // for color encoding, we assume a board position (-1), which is empty for white and has a pawn for black.
    if c == COLOR_WHITE as i64 {
        shift = 1;
    } else {
        shift = 3;
        buf = 0b101
    }
    for i in 0..4 {
        for q in 0..2 {
            bp = i + 4 * q;
            for _ in 0..8 {
                let f = (ARRAY_BASE_6 + g.board[bp]) as usize; // figure
                bp += 8; // next (row) board position
                let newbits: u64 = CODE[f];
                buf = buf | (newbits << shift);
                shift += L[f];
            }
            collector[bpos..(bpos + 8)].copy_from_slice(&buf.to_le_bytes());
            debug_assert!(bpos + 8 <= collector.len());
            bpos += shift / 8;
            let r = shift & (!7);
            buf = buf >> r;
            shift &= 7; // shift -= r;
        }
    }
    result[0..CORE_BIT_BUFFER_SIZE].copy_from_slice(&collector[0..CORE_BIT_BUFFER_SIZE]);
    debug_assert!(result[22] == 0);
    debug_assert!(result[23] == 0);
    if BIT_BUFFER_SIZE == HASH_BIT_BUFFER_SIZE {
        result[24..HASH_BIT_BUFFER_SIZE].copy_from_slice(&board_hash(g.board).to_le_bytes());
    } // sanity check with hash
    result
}

fn encode_board(g: &Game, c: Color) -> BitBuffer192 {
    //return simpleWriteToBitBuffer(g, c);
    return much_faster_write_to_bit_buffer(g, c);
}

fn off_board_64(dst: Position) -> bool {
    dst < 0 || dst > 63
}

// do we not cross the border of the board when figure is moved in a regular way
pub fn move_is_valid(src: Position, dst: Position) -> bool {
    !off_board_64(dst) && (col(src) - col(dst)).abs() <= 1
}

fn knightmove_is_valid(src: Position, dst: Position) -> bool {
    !off_board_64(dst) && (col(src) - col(dst)).abs() <= 2
}

fn pawnmove_is_valid(c: Color, src: Position, dst: Position) -> bool {
    let mut result = move_is_valid(src, dst);
    if result && (src - dst).abs() == 16 {
        result = if is_white(c) {
            row(src) == B2 as i8
        } else {
            row(src) == B7 as i8
        }
    }
    return result;
}

fn init_rook(g: &mut Game) {
    for src in POS_RANGE {
        let mut i = 0;
        for d in ROOK_DIRS {
            let mut pos = src;
            loop {
                let dst = pos + d as i8;
                if !move_is_valid(pos, dst) {
                    break;
                }
                g.rook_path[src as usize][i].pos = if pos == src { -dst as i8 } else { dst as i8 }; // mark start pos for this dir
                i += 1;
                pos = dst;
            }
        }
        let mut nxt_dir_start = i; // index of the last terminal node
        g.rook_path[src as usize][i].pos = -1; // terminator
        while i > 0 {
            i -= 1;
            g.rook_path[src as usize][i].nxt_dir_idx = nxt_dir_start as i64;
            if g.rook_path[src as usize][i].pos < 0 {
                nxt_dir_start = i;
                g.rook_path[src as usize][i].pos *= -1;
            }
        }
    }
}

fn init_bishop(g: &mut Game) {
    for src in POS_RANGE {
        let mut i = 0;
        for d in BISHOP_DIRS {
            let mut pos = src;
            loop {
                let dst = pos + d as i8;
                if !move_is_valid(pos, dst) {
                    break;
                }
                g.bishop_path[src as usize][i].pos =
                    if pos == src { -dst as i8 } else { dst as i8 };
                i += 1;
                pos = dst;
            }
        }
        let mut nxt_dir_start = i;
        g.bishop_path[src as usize][i].pos = -1;
        g.freedom[(ARRAY_BASE_6 + W_BISHOP) as usize][src as usize] = ((i as i32 - 10) * 4) as i64; // range -12..12 // abs val is big enough, so exchange of a
        g.freedom[(ARRAY_BASE_6 + W_QUEEN) as usize][src as usize] = ((i as i32 - 10) * 4) as i64; // range -12..12 // pawn for very good position may occur
        g.freedom[(ARRAY_BASE_6 + B_BISHOP) as usize][src as usize] = ((i as i32 - 10) * 4) as i64;
        g.freedom[(ARRAY_BASE_6 + B_QUEEN) as usize][src as usize] = ((i as i32 - 10) * 4) as i64;
        while i > 0 {
            i -= 1;
            g.bishop_path[src as usize][i].nxt_dir_idx = nxt_dir_start as i64;
            if g.bishop_path[src as usize][i].pos < 0 {
                nxt_dir_start = i;
                g.bishop_path[src as usize][i].pos *= -1;
            }
        }
    }
}

fn init_knight(g: &mut Game) {
    for src in POS_RANGE {
        let mut i = 0;
        for d in KNIGHT_DIRS {
            if knightmove_is_valid(src, src + d as i8) {
                g.knight_path[src as usize][i].pos = (src + d as i8) as i8;
                g.knight_path[src as usize][i].nxt_dir_idx = (i + 1) as i64; // not really needed
                i += 1;
            }
        }
        g.knight_path[src as usize][i].pos = -1;
        g.freedom[(ARRAY_BASE_6 + W_KNIGHT) as usize][src as usize] = ((i as i32 - 5) * 4) as i64; // range -12..12
        g.freedom[(ARRAY_BASE_6 + B_KNIGHT) as usize][src as usize] = ((i as i32 - 5) * 4) as i64;
    }
}

fn init_king(g: &mut Game) {
    for src in POS_RANGE {
        let mut i = 0;
        for d in KING_DIRS {
            if move_is_valid(src, src + d as i8) {
                g.king_path[src as usize][i].pos = (src + d as i8) as i8;
                g.king_path[src as usize][i].nxt_dir_idx = (i + 1) as i64;
                i += 1;
            }
        }
        g.king_path[src as usize][i].pos = -1;
        if src == 0 || src == 7 || src == 56 || src == 63 {
            g.freedom[(ARRAY_BASE_6 + W_KING) as usize][src as usize] = -16;
            g.freedom[(ARRAY_BASE_6 + B_KING) as usize][src as usize] = -16;
        }
    }
}

// the first two moves are possible captures or -1 if at the border of the board
fn init_pawn(g: &mut Game, color: Color) {
    for src in POS_RANGE {
        let mut i = 0;
        for d in PAWN_DIRS_WHITE {
            g.pawn_path[col_idx(color) as usize][src as usize][i].pos =
                if pawnmove_is_valid(color, src, (src as i32 + d * color as i32) as i8) {
                    (src as i8 + (d * (color as i32)) as i8) as i8
                } else {
                    -1
                };
            g.pawn_path[col_idx(color) as usize][src as usize][i].nxt_dir_idx = i as i64 + 1; // not really needed
            i += 1;
        }
        g.pawn_path[col_idx(color) as usize][src as usize][i as usize].pos = -1;
    }
}

// delete seq entries with score s == IGNORE_MARKER_LOW_INT16
fn fast_del_invalid(a: &mut Vec<KK>) {
    let mut i = 0; //a.low
    while i < a.len() && a[i].s != IGNORE_MARKER_LOW_INT16 {
        i += 1;
    }
    let mut j = i; // j is the source index
    while j < a.len() {
        if a[j].s != IGNORE_MARKER_LOW_INT16 {
            a[i] = a[j];
            i += 1;
        }
        j += 1;
    }
    a.truncate(a.len() - (j - i));
}

// https://rosettacode.org/wiki/Sorting_algorithms/Insertion_sort#Rust
// fn insertion_sort<T: std::cmp::Ord>(arr: &mut [T]) {
// must be a stable sort!
fn ixsort(arr: &mut Vec<KK>, high: usize) {
    //debug_assert!(high > 0);
    for i in 1..(high + 1) {
        let mut j = i;
        while j > 0 && arr[j].s > arr[j - 1].s {
            arr.swap(j, j - 1);
            j = j - 1;
        }
    }
    fast_del_invalid(arr); // we can delete them, or just skip them
}

fn is_sorted(a: &Vec<KK>, high: usize) -> bool {
    let mut i = high;
    while i > 0 && a[i].s <= a[i - 1].s {
        i -= 1;
    }
    return i <= 0;
}

fn capture(kk: KK) -> bool {
    kk.sf * kk.df < 0
}

fn valid(kk: KK) -> bool {
    kk.sf * kk.df <= 0
}

// caution, this is used for in_check() test too.
fn wanted(kk: KK) -> bool {
    kk.sf * kk.df < (kk.s > 0) as i8
}

fn walk_rook(g: &Game, kk: KK, s: &mut KKS) {
    let mut i: i64 = 0;
    let mut kk = kk;
    while {
        kk.di = g.rook_path[kk.si as usize][i as usize].pos;
        kk.di
    } >= 0
    {
        if {
            kk.df = g.board[kk.di as usize] as i8;
            kk.df
        } == 0
        {
            i += 1;
        } else {
            i = g.rook_path[kk.si as usize][i as usize].nxt_dir_idx;
        }
        if wanted(kk) {
            s.push(kk)
        }
    }
}

fn walk_bishop(g: &Game, kk: KK, s: &mut KKS) {
    let mut i: i64 = 0;
    let mut kk = kk;
    while {
        kk.di = g.bishop_path[kk.si as usize][i as usize].pos;
        kk.di
    } >= 0
    {
        if {
            kk.df = g.board[kk.di as usize] as i8;
            kk.df
        } == 0
        {
            i += 1
        } else {
            i = g.bishop_path[kk.si as usize][i as usize].nxt_dir_idx
        }
        if wanted(kk) {
            s.push(kk)
        };
    }
}

fn walk_king(g: &Game, kk: KK, s: &mut KKS) {
    let mut kk = kk;
    for i in 0..(7 + 1) {
        if {
            kk.di = g.king_path[kk.si as usize][i as usize].pos;
            kk.di
        } < 0
        {
            break;
        }
        kk.df = g.board[kk.di as usize] as i8;
        if wanted(kk) {
            s.push(kk);
        }
    }
}

fn walk_knight(g: &Game, kk: KK, s: &mut KKS) {
    let mut kk = kk;
    for i in 0..(7 + 1) {
        if {
            kk.di = g.knight_path[kk.si as usize][i as usize].pos;
            kk.di
        } < 0
        {
            break;
        }
        kk.df = g.board[kk.di as usize] as i8;
        if wanted(kk) {
            s.push(kk);
        }
    }
}

// now we generate all possible ep captures -- before performing the actual move, we have to check ep_pos value
fn walk_pawn(g: &Game, kk: KK, s: &mut KKS) {
    let mut kk = kk;
    let col_idx = (kk.sf + 1) / 2;
    for i in 0..2 {
        if {
            kk.di = g.pawn_path[col_idx as usize][kk.si as usize][i].pos;
            kk.di
        } >= 0
        {
            kk.df = g.board[kk.di as usize] as i8;
            let c: Color;
            if kk.sf == W_PAWN as i8 {
                c = COLOR_WHITE as Color
            } else {
                c = COLOR_BLACK as Color
            };
            debug_assert!(c == (kk.sf) as Color);
            if rows_to_go(kk.si, c) == 3
                && kk.df == VOID_ID as i8
                && g.board[(kk.di + kk.sf * 8) as usize] == -kk.sf as i64
            {
                // possible ep capture
                s.push(kk);
            } else if capture(kk) {
                if base_row(kk.di) {
                    kk.promote_to = kk.sf * KNIGHT_ID as i8;
                    s.push(kk);
                    kk.promote_to = kk.sf * QUEEN_ID as i8;
                    s.push(kk);
                } else {
                    s.push(kk);
                }
            }
        }
    }
    if kk.s >= 0 {
        for i in 2..4 {
            if {
                kk.di = g.pawn_path[col_idx as usize][kk.si as usize][i as usize].pos;
                kk.di
            } >= 0
            {
                if {
                    kk.df = g.board[kk.di as usize] as i8;
                    kk.df
                } == 0
                {
                    if base_row(kk.di) {
                        kk.promote_to = kk.sf * KNIGHT_ID as i8;
                        s.push(kk);
                        kk.promote_to = kk.sf * QUEEN_ID as i8;
                        s.push(kk);
                    } else {
                        s.push(kk);
                    }
                } else {
                    break;
                }
            }
        }
    }
}

#[derive(Debug, Default)]
pub struct Move {
    pub src: i64,
    pub dst: i64,
    pub score: i64,
    control: ChessSquares,
    promote_to: i64,
    state: State,
}

// result is for White
fn plain_evaluate_board(g: &Game) -> i64 {
    let mut result: i64 = 0;
    for (p, f) in g.board.iter().enumerate() {
        // if f != VOID_ID -- does not increase performance
        result += (FIGURE_VALUE[f.abs() as usize] + g.freedom[(6 + *f) as usize][p as usize] as i32)
            as i64
            * (sign(*f));
    }
    result
}

/*
discard """
https://chessprogramming.wikispaces.com/Alpha-Beta
i64 alphaBeta( i64 alpha, i64 beta, i64 depthleft ) {
   if( depthleft == 0 ) return quiesce( alpha, beta );
   for ( all moves) {
      score = -alphaBeta( -beta, -alpha, depthleft - 1 );
      if( score >= beta )
         return beta; // fail hard beta-cutoff
      if( score > alpha )
         alpha = score; // alpha acts like max in MiniMax
   }
   return alpha;
}
"""
*/

fn in_check(g: &Game, si: i64, col: Color) -> bool {
    let mut kk: KK = KK {
        s: 0,
        sf: 0,
        df: 0,
        si: 0,
        di: 0,
        eval_depth: 0,
        promote_to: 0,
    };
    let mut s: Vec<KK> = Vec::with_capacity(8);
    kk.si = si as i8;
    kk.sf = sign(col as i64) as i8;
    debug_assert!(kk.sf == col as i8);
    kk.s = -1; // only captures
    s.clear();
    walk_bishop(g, kk, &mut s);
    if s.iter()
        .into_iter()
        .find(|&it| it.df.abs() == BISHOP_ID as i8 || it.df.abs() == QUEEN_ID as i8)
        .is_some()
    {
        return true;
    }
    s.clear();
    walk_rook(g, kk, &mut s);
    if s.iter()
        .into_iter()
        .find(|&it| it.df.abs() == ROOK_ID as i8 || it.df.abs() == QUEEN_ID as i8)
        .is_some()
    {
        return true;
    }
    s.clear();
    walk_knight(g, kk, &mut s);
    if s.iter()
        .into_iter()
        .find(|&it| it.df.abs() == KNIGHT_ID as i8)
        .is_some()
    {
        return true;
    }
    s.clear();
    walk_pawn(g, kk, &mut s);
    if s.iter()
        .into_iter()
        .find(|&it| it.df.abs() == PAWN_ID as i8)
        .is_some()
    {
        return true;
    }
    s.clear();
    walk_king(g, kk, &mut s);
    s.iter()
        .into_iter()
        .find(|&it| it.df.abs() == KING_ID as i8)
        .is_some()
}

fn king_pos(g: &Game, c: Color) -> Position {
    let k = KING_ID * c as i64;
    for (i, f) in g.board.iter().enumerate() {
        if *f == k {
            return i as Position;
        }
    }
    debug_assert!(false);
    0
}

const V_RATIO: i32 = 8;

const SELECT_EXTEND: bool = false; // depth extend based on source and destination pieces
const CAPTURE_EXTEND: bool = false; // depth extend for captures
const EQUAL_CAPTURE_EXTEND: bool = false; // depth extend for captures of pieces with similar value

const LARGE_CAPTURE_EXTEND: bool = false; // i.e. pawn captures knight
const PAWN_MARCH_EXTEND: bool = false; // successive pawn moves of a single pawn, to gain nconversion to queen
const CHECK_EXTEND: bool = false; // depth extend when we are in check (only supported for first 3 plys)
const NO_EXTEND_AT_ALL: bool = true; // avoid depth entends for now

// for endgame, to get a correct value for "moves to mate"
// "moves to mate" is calculated from score and value of cup counter
/*
fn `+-?`(a, b: i64) -> i64  {
  if a > KING_VALUE_DIV_2:
    result = a + b
  elif a < -KING_VALUE_DIV_2:
    result = a - b
  else:
    result = a
}
*/

// plus minus questionmark
fn pmq(a: i64, b: i64) -> i64 {
    if a > KING_VALUE_DIV_2 as i64 {
        return a + b;
    } else if a < -KING_VALUE_DIV_2 as i64 {
        return a - b;
    } else {
        return a;
    }
}

// color: White or Black, color of active player
// v_depth: search depth, as a multiply of V_RATIO
// v_depth is the virtual search depth, it is a multiple of real search depth to allow a more
// fine grained search depth extension.
// v_depth starts with a multiple of V_RATIO (n * VRation + V_RATIO div 2), and generally decreases by
// V_RATIO for each recursive call of abeta(). For special very important moves it may decrease less,
// i.e. if we are in check. Real depth is always v_depth div V_RATIO.
// v_depth may even increase in rare cases!
// cup: plain recursion depth counter counting upwards starting at zero, depth indication
// alpha_0, beta: the search window for prunning
// old_list_len: estimation of the number of moves that the opponent can do
// ep_pos: if not -1, it indicates the position of the en pasant square
// for en passant capture, i.e. after pawn move e2 e4 ep_pos is e3.
// Result: Currently we return a value object. We may change that to a reference type, that
// would allow changing moves and displaying whole move sequences. Maybe a bit slower.
// Board: Currently we use a global board variable, but we may change that to pass
// the board as first parameter as in OOP style. By using a non var board parameter,
// we can avoid reseting the state -- we have to test the performace.
//
fn abeta(
    g: &mut Game,
    color: Color,
    v_depth: i64,
    cup: i64,
    alpha_0: i64,
    beta: i64,
    old_list_len: i64,
    ep_pos: i64,
) -> Move {
    debug_assert!(alpha_0 < beta);
    debug_inc(&mut g.ab_call);
    debug_assert!(MAX_DEPTH == 15);
    debug_assert!(V_RATIO == 8);
    let depth_0 = min(max(v_depth / V_RATIO as i64, 0), MAX_DEPTH as i64) as usize; // starting at depth_0 == 0 we do only captures
    debug_assert!(cup >= 0);
    //debug_assert!(depth_0 >= 0);
    debug_assert!(std::mem::size_of::<KK>() == 8);
    debug_assert!(old_list_len >= 0);
    debug_assert!((-1..63).contains(&ep_pos));
    let mut hash_res: HashResult;
    let mut sdi: [i64; 7] = [0; 7];
    let mut ddi: [i64; 7] = [0; 7];
    let mut nep_pos: i64;
    let mut v_depth_inc: i64 = 0;
    let mut eval_cnt: i64 = 0;
    let mut alpha: i64 = alpha_0;
    let mut valid_move_found: bool = false;
    let back: Board;
    //if cfg!(debug_assertions) {
      back = g.board; // test board integrity
    //}
    let mut result: Move = Default::default();
    result.state = STATE_NO_VALID_MOVE;
    let v_depth = v_depth - V_RATIO as i64;
    let encoded_board = encode_board(&g, color);
    let hash_pos = get_tte(g, encoded_board);
    if hash_pos >= 0 {
        hash_res = g.tt[hash_pos as usize].res.clone();
        //debug_assert!(hash_res.kks.len() > 0);
        // we have the list of moves, and maybe the exact score, or a possible beta cutoff
        debug_inc(&mut g.hash_succ);
        for i in (depth_0..(MAX_DEPTH + 1) as usize).rev() {
            if hash_res.score[i].s != INVALID_SCORE {
                // we have the exact score, so return it
                if i == depth_0
                    || hash_res.score[i].s.abs() < KING_VALUE_DIV_2 as i16
                    || hash_res.score[i].s.abs() >= KING_VALUE as i16
                {
                    // use of deeper knowledge in endgame can give wrong moves to mate reports
                    // or generate repeated moves.
                    result.score = pmq(hash_res.score[i].s as i64, -cup);
                    result.src = hash_res.score[i].si as i64; // these details are currently only needed for cup == 0
                    result.dst = hash_res.score[i as usize].di as i64;
                    result.promote_to = hash_res.score[i].promote_to as i64;
                    result.state = hash_res.state;
                    debug_inc(&mut g.score_hash_succ);
                } else if pmq(hash_res.score[i].s as i64, -cup) >= beta {
                    // at least we can use the score for a beta cutoff
                    result.score = beta;
                }
                return result;
            }
            if pmq(hash_res.floor[i].s as i64, -cup) >= beta {
                // a beta cutoff
                result.score = beta;
                debug_inc(&mut g.floor_hash_succ);
                return result;
            }
        }
        lift(&mut g.tt[hash_pos as usize].res.pri, depth_0 as i64); // avoid that this entry in tt is overwritten by recursive abeta() calls!
    } else {
        // we have to create the move list
        hash_res = HashResult::default();
        init_hr(&mut hash_res);
    }

    //when false: // possible, but makes not much sense
    /*
    if false {
        if hash_pos < 0 && depth_0 > 3 {
            // fast movelist ordering
            abeta(
                g,
                color,
                v_depth - 2 * V_RATIO as i64,
                cup,
                alpha_0,
                beta,
                old_list_len,
                -1,
            );
            hash_pos = get_tte(&g, encoded_board, &mut hash_res);
        }
    }
    */

    let mut evaluation: i64 = LOWEST_SCORE as i64;
    if depth_0 == 0 {
        // null move estimation for quiescence search
        evaluation = plain_evaluate_board(&g) * color as i64;
        if evaluation >= beta + 64 {
            // +64 for max. difference in number of possible moves of both sides
            result.score = beta;
            debug_inc(&mut g.null_move_succ_1);
            return result;
        }
    }
    if hash_pos < 0 {
        // generate the move list, including possible castlings and en passant moves
        let mut s: Vec<KK> = Vec::with_capacity(63);
        let mut kk: KK = Default::default();
        kk.s = 1; // generate all moves, not only capures
        for (si, sf) in g.board.iter().enumerate() {
            // source index, source figure
            if *sf != VOID_ID {
                hash_res.pop_cnt += 1;
            }
            if sf * color as i64 <= 0 {
                continue;
            }
            kk.si = si as i8;
            kk.sf = *sf as i8;
            match sf.abs() {
                PAWN_ID => walk_pawn(&g, kk, &mut s),
                KNIGHT_ID => walk_knight(&g, kk, &mut s),
                BISHOP_ID => walk_bishop(&g, kk, &mut s),
                ROOK_ID => walk_rook(&g, kk, &mut s),
                QUEEN_ID => {
                    walk_bishop(&g, kk, &mut s);
                    walk_rook(&g, kk, &mut s)
                }
                KING_ID => {
                    walk_king(&g, kk, &mut s);
                    hash_res.king_pos = kk.si as i64
                }
                _ => {}
            }
        }
        debug_assert!(hash_res.pop_cnt <= 32); // for regular games
        if cup < 3 {
            hash_res.in_check = in_check(&g, hash_res.king_pos, color); // this field is optional information
        }
        for el in &s {
            if !is_a_pawn(el.sf) || odd(el.si - el.di) {
                hash_res.control.insert(el.di as usize); // attacked positions
            }
        }
        kk.df = VOID_ID as i8; // for all 4 types of castling
        if color == COLOR_WHITE as i64 && g.board[3] == W_KING {
            // and 3 notin has_moved and 0 notin has_moved:
            if g.board[0] == W_ROOK && g.board[1] == VOID_ID && g.board[2] == VOID_ID {
                kk.di = 1;
                kk.si = 3;
                kk.sf = W_KING as i8;
                s.push(kk);
            }
            if g.board[7] == W_ROOK
                && g.board[4] == VOID_ID
                && g.board[5] == VOID_ID
                && g.board[6] == VOID_ID
            {
                kk.di = 5;
                kk.si = 3;
                kk.sf = W_KING as i8;
                s.push(kk);
            }
        }
        if color == COLOR_BLACK as i64 && g.board[59] == B_KING {
            // and 59 notin has_moved and 56 notin has_moved:
            if g.board[56] == B_ROOK && g.board[57] == VOID_ID && g.board[58] == VOID_ID {
                kk.di = 57;
                kk.si = 59;
                kk.sf = B_KING as i8;
                s.push(kk);
            }
            if g.board[63] == B_ROOK
                && g.board[60] == VOID_ID
                && g.board[61] == VOID_ID
                && g.board[62] == VOID_ID
            {
                kk.di = 61;
                kk.si = 59;
                kk.sf = B_KING as i8;
                s.push(kk);
            }
        }
        for el in &mut s {
            debug_assert!(g.board[el.si as usize] != 0);
            // guessed ratings of the moves
            el.eval_depth = -1; // mark as unevaluated
                                //when compileOption("assertions"):
            if false {
                if base_row(el.di) && is_a_pawn(el.sf) {
                    //debug_assert!(el.promote_to.abs in [KNIGHT_ID, QUEEN_ID]);
                    debug_assert!(
                        el.promote_to.abs() == KNIGHT_ID as i8
                            || el.promote_to.abs() == QUEEN_ID as i8
                    );
                } else {
                    debug_assert!(el.promote_to == 0);
                }
            }
            el.s = (FIGURE_VALUE[el.promote_to.abs() as usize]
                + FIGURE_VALUE[el.df.abs() as usize]
                + g.freedom[(6 + el.sf) as usize][(0 + el.di) as usize] as i32
                - g.freedom[(6 + el.sf) as usize][(0 + el.si) as usize] as i32)
                as i16;
        }
        let h = s.len() - 1;
        ixsort(&mut s, h); // s.len() - 1);
        debug_assert!(is_sorted(&s, h));
        s.shrink_to_fit();
        hash_res.kks = s;
        debug_assert!(hash_res.kks.len() > 0);
    }
    if depth_0 == 0 {
        // // more detailed null move estimation for quiescence search
        evaluation += hash_res.kks.len() as i64 - old_list_len as i64; // we may do a more fine grained board control evaluation?
                                                                       //when compileOption("assertions"):
        if cfg!(feature = "salewskiChessDebug") {
            lift(
                &mut g.max_delta_len,
                (hash_res.kks.len() as i64 - old_list_len).abs(),
            );
        }
        if evaluation >= beta {
            result.score = beta;
            debug_inc(&mut g.null_move_succ_2);
            return result;
        }
        lift(&mut alpha, evaluation);
    }
    result.control = hash_res.control.clone();
    hash_res.kks_high = -1; // the number of newly evaluated positions, we sort only this range.
    result.score = evaluation; // LOWEST_SCORE for depth_0 > 0
    debug_assert!(depth_0 == 0 || result.score == LOWEST_SCORE as i64);
    debug_assert!(hash_res.score[depth_0].s == INVALID_SCORE);
    let hash_res_kks_len = hash_res.kks.len() as i64;
    if hash_res.kks.len() == 0 {
        println!("*****************");
    }
    debug_assert!(hash_res.kks.len() > 0);
    for el in &mut hash_res.kks {
        if el.s == IGNORE_MARKER_LOW_INT16 {
            //debug_assert!(false); // we actually delete invalid entries, so nothing to skip
            continue;
        }
        debug_assert!(el.s != IGNORE_MARKER_LOW_INT16);
        debug_assert!(g.board[el.si as usize] != VOID_ID); // issue TODO
        hash_res.kks_high += 1; // the number of up to date positions, which we have to sort later
        if depth_0 == 0 && el.df == VOID_ID as i8 {
            // skip non-captures in quiescence search
            continue;
        }
        if cup == 0 {
            //debugEcho ":", (getMonoTime() - start_time).inNanoSeconds.float / 1e9 , " ", hash_res.kks.len
            //if eval_cnt > 1 && Instant::now() > g.cut_time as Instant {
            if eval_cnt > 1 && g.start_time.elapsed() > g.cut_time {
                //debugEcho "break", eval_cnt, " ", hash_res.kks_high
                println!("cut_timeBreak{} {}", eval_cnt, hash_res.kks_high);
                if cfg!(feature = "salewskiChessDebug") {
                    println!("{:?}", hash_res.kks);
                }
                break;
            }
        }
        let mut m: Move = Move {
            src: 0,
            dst: 0,
            score: 0,
            control: BitSet::new(),
            promote_to: 0,
            state: 0,
        };
        if el.eval_depth >= depth_0 as i8 {
            // this move was already evaluated, but was not good enough, no beta cutoff
            valid_move_found = true; // list contains only valid moves, as we delete or skip the invalid ones
            debug_inc(&mut g.re_eval_skip);
            m.score = pmq(el.s as i64, -cup) as i64;
            debug_assert!(m.score < beta);
        } else {
            // do new evaluation
            eval_cnt += 1; // number of newly evaluated moves
            let is_a_pawnelsf = is_a_pawn(el.sf);
            let is_a_kingelsf = is_a_king(el.sf);
            let elsieldi = el.si - el.di;
            let little_castling = is_a_kingelsf && elsieldi == 2; // castling candidates
            let big_castling = is_a_kingelsf && elsieldi == -2;
            let en_passant = is_a_pawnelsf && el.df == VOID_ID as i8 && odd(elsieldi); // move is an eP capture candidate

            if little_castling
                && (g.has_moved.contains(el.si as usize)
                    || g.has_moved.contains(el.si as usize - 3))
            {
                // we always generate castling moves but
                continue;
            }
            if big_castling
                && (g.has_moved.contains(el.si as usize)
                    || g.has_moved.contains(el.si as usize + 4))
            {
                // skip them when not allowed.
                continue;
            }
            if en_passant && el.di != ep_pos as i8 {
                // skip en pasant move
                continue;
            }
            // does such extents make any sense? We can do it, but we have to be careful and test.
            //when SELECT_EXTEND:
            if SELECT_EXTEND {
                if !g.is_endgame {
                    // makes no sense in endgame
                    sdi = [0, 0, 0, 0, 0, 0, 2]; // source figure depth increase // increase depth when king is moved
                    ddi = [0, 0, 2, 2, 2, 2, 0]; // destination figure depth increase // increase depth for capture
                }
            }
            if CAPTURE_EXTEND || EQUAL_CAPTURE_EXTEND || LARGE_CAPTURE_EXTEND {
                if el.df != VOID_ID as i8 {
                    if CAPTURE_EXTEND {
                        v_depth_inc = 2;
                    }
                    if EQUAL_CAPTURE_EXTEND || LARGE_CAPTURE_EXTEND {
                        let immediate_gain =
                            FIGURE_VALUE[el.df.abs() as usize] - FIGURE_VALUE[el.sf.abs() as usize];
                        if LARGE_CAPTURE_EXTEND {
                            if immediate_gain > PAWN_VALUE {
                                v_depth_inc = 4;
                            }
                        }
                        if EQUAL_CAPTURE_EXTEND {
                            if immediate_gain.abs() < 10 {
                                v_depth_inc = 2;
                            }
                        }
                    }
                }
            }
            if PAWN_MARCH_EXTEND {
                if is_a_pawnelsf && hash_res.pop_cnt < 32 - 6 {
                    let rows_to_go = rows_to_go(el.si, color);
                    g.pawn_march[cup as usize].insert(el.di as usize);
                    if g.pawn_march[cup as usize - 2].contains(el.si as usize) {
                        // pawn just moved to this location
                        debug_assert!(rows_to_go < 7);
                        if rows_to_go == 6 && (elsieldi == 8 || elsieldi == -8) {
                        }
                        //discard // last was one step from base row
                        else if hash_res.pop_cnt < 32 - 12 {
                            v_depth_inc = 4;
                        } else {
                            v_depth_inc = 2;
                        }
                    }
                }
            }
            if CHECK_EXTEND {
                if hash_res.in_check {
                    v_depth_inc = 2;
                }
            }
            if NO_EXTEND_AT_ALL {
                v_depth_inc = 0;
            }
            if g.is_endgame {
                // better no extents in endgame
                v_depth_inc = 0;
            }
            if is_a_king(el.df) {
                result.state = STATE_CAN_CAPTURE_KING; // the other result fields are not really used/needed
                result.score = KING_VALUE as i64; // + 1 // or high(int16)
                hash_res.state = STATE_CAN_CAPTURE_KING;
                hash_res.score[MAX_DEPTH as usize].s = result.score as i16; // MAX_DEPTH, as it is the final score
                debug_assert!(hash_pos < 0); // once stored, we just retrieve it
                                       //put_tte(g, encoded_board, hash_res, depth_0 as i64, hash_pos); // store this for a fast return next time
                return result;
            }
            g.board[el.si as usize] = VOID_ID; // the basic movement
            g.board[el.di as usize] = el.sf as i64;
            let hmback = g.has_moved.clone(); // backup
            g.has_moved.insert(el.si as usize); // may be a king or rook move, so castling is forbidden
            if little_castling {
                // small rochade
                g.board[el.di as usize + 1] = g.board[el.di as usize - 1];
                g.board[el.di as usize - 1] = VOID_ID;
                g.has_moved.insert(el.di as usize - 1);
            } else if big_castling {
                // big rochade
                g.board[el.di as usize - 1] = g.board[el.di as usize + 2];
                g.board[el.di as usize + 2] = VOID_ID;
                g.has_moved.insert(el.di as usize + 2);
            } else if en_passant {
                g.board[el.di as usize - color as usize * 8] = VOID_ID;
            } else if is_a_pawnelsf && base_row(el.di) {
                g.board[el.di as usize] = el.promote_to as i64;
            }
            let pawn_jump = is_a_pawnelsf && (elsieldi == 16 || elsieldi == -16);
            if pawn_jump {
                nep_pos = (el.si + el.di) as i64 / 2; // fast unsigned div
            } else {
                nep_pos = -1;
            }
            // if is_a_pawnelsf or el.df != VOID_ID: // handle draw by repetitions. As rep. test is a bit expensive, we do not
            if cup > 5 || hash_res.pop_cnt > 20 || is_a_pawnelsf || el.df != VOID_ID as i8 {
                // test dense populated board or deeper plys.
                m = abeta(
                    g,
                    opp_color(color),
                    v_depth + v_depth_inc + sdi[el.sf.abs() as usize] + ddi[el.df.abs() as usize],
                    cup + 1,
                    -beta,
                    -alpha,
                    hash_res_kks_len,
                    nep_pos,
                );
            } else {
                // deal with repetive positions
                let new_state = encode_board(&g, color); // this is the new board state after a piece is moved
                if g.history[&new_state] >= 2 {
                    // this will be the third repetition, so draw can be requested
                    m.score = 0; // draw
                } else {
                    g.history.insert(new_state, 1);
                    //*counts.entry(word).or_insert(0) += 1;
                    m = abeta(
                        g,
                        opp_color(color),
                        v_depth
                            + v_depth_inc
                            + sdi[el.sf.abs() as usize]
                            + ddi[el.df.abs() as usize],
                        cup + 1,
                        -beta,
                        -alpha,
                        hash_res_kks_len,
                        nep_pos,
                    );
                    *g.history.get_mut(&new_state).unwrap() -= 1;
                }
            }
            m.score *= -1;
            if cfg!(feature = "salewskiChessDebug") {
                if cup == 0 {
                    println!("********{}", m.score);
                }
            }
            if m.state == STATE_CAN_CAPTURE_KING {
                el.s = IGNORE_MARKER_LOW_INT16; // mark for deletion
            } else {
                valid_move_found = true;
                el.s = (pmq(m.score, cup)) as i16; // caution due to cutoff score might be not correct. For stable sorting of movelist there should be no problems!
                if m.score > alpha && m.score < beta {
                    // otherwise our abeta() call did a beta cutoff, so we have no real score
                    el.eval_depth = depth_0 as i8;
                } else {
                    el.eval_depth = -1; // mark as unevaluated
                }
            }
            g.has_moved = hmback; // reset board state
            g.pawn_march[cup as usize].remove(el.di as usize);
            g.board[el.di as usize] = el.df as i64;
            g.board[el.si as usize] = el.sf as i64;
            if en_passant {
                g.board[el.di as usize - color as usize * 8] = -el.sf as i64;
            }
            if little_castling {
                // small rochade
                g.board[el.di as usize - 1] = g.board[el.di as usize + 1];
                g.board[el.di as usize + 1] = VOID_ID;
                // g.has_moved.excl(el.di - 1) // use backup instead
                let mut h: BitSet = Default::default();
                h.insert(el.si as usize);
                h.insert(el.si as usize - 1);
                h.insert(el.di as usize);
                if !m.control.is_disjoint(&h) {
                    el.s = IGNORE_MARKER_LOW_INT16; // mark for deletion or ignore
                    continue; // was illegal, so ignore
                }
            } else if big_castling {
                // big rochade
                g.board[el.di as usize + 2] = g.board[el.di as usize - 1];
                g.board[el.di as usize - 1] = VOID_ID;
                // g.has_moved.excl(el.di + 2)
                let mut h: BitSet = Default::default();
                h.insert(el.si as usize);
                h.insert(el.si as usize + 1);
                h.insert(el.di as usize);
                if !m.control.is_disjoint(&h) {
                    el.s = IGNORE_MARKER_LOW_INT16;
                    continue; // was illegal, so ignore
                }
            }
            if m.score >= beta {
                // debug_assert!(is_sorted2(hash_res.kks, hash_res.kks_high + 1, hash_res.kks.high)) // no, can be more than one partition
                ixsort(&mut hash_res.kks, hash_res.kks_high as usize);
                //debug_assert!(is_sorted(&hash_res.kks, hash_res.kks_high as usize));
                //debug_assert!(hash_res.floor[depth_0 as usize].s < m.score as i16); // always true, due to beta cutoff test at top of proc
                hash_res.floor[depth_0].s = pmq(m.score, cup) as i16;
                put_tte(g, encoded_board, hash_res, depth_0 as i64, hash_pos);
                result.score = beta;
                return result;
            }
        }
        lift(&mut alpha, m.score);
        if m.score > result.score {
            result.score = m.score;
            result.src = el.si as i64;
            result.dst = el.di as i64;
            result.promote_to = el.promote_to as i64;
        }
    }
    if depth_0 > 0 && !valid_move_found {
        if in_check(&g, hash_res.king_pos, color) {
            result.state = STATE_CHECKMATE;
            result.score = -KING_VALUE as i64 + cup as i64 - 1;
        } else {
            result.score = 0;
            result.state = STATE_STALEMATE;
        }
    } else {
        result.state = STATE_PLAYING;
    }

    debug_assert!(hash_res.score[depth_0].s == INVALID_SCORE);
    //debug_assert!(hash_res.kks_high == hash_res.kks.high) // not always, due to cut_time break for cup == 0
    ixsort(&mut hash_res.kks, hash_res.kks_high as usize);
    if result.score > alpha_0 || result.state == STATE_CHECKMATE || result.state == STATE_STALEMATE
    {
        // otherwise our abeta() call did a beta cutoff, so we have no real score
        debug_assert!(
            depth_0 == 0
                || alpha > alpha_0
                || result.state == STATE_CHECKMATE
                || result.state == STATE_STALEMATE
        );
        hash_res.score[depth_0].s = pmq(result.score, cup) as i16;
        hash_res.score[depth_0].si = result.src as i8;
        hash_res.score[depth_0].di = result.dst as i8;
    }
    hash_res.state = result.state;
    if cfg!(feature = "salewskiChessDebug") {
        if cup == 0 {
            println!("{:?}", hash_res.kks);
        }
    }
    if hash_res.kks.len() == 0 {
        println!("hash_res.kks.len() == 0");
        put_tte(g, encoded_board, hash_res, depth_0 as i64, hash_pos);
    } else {
        put_tte(g, encoded_board, hash_res, depth_0 as i64, hash_pos);
    }
    if cfg!(debug_assertions) {
        //when compileOption("assertions"):
        debug_assert!(back == g.board);
        //println!("");
    }
    result
}

fn str_2_board_pos(s: String) -> Position {
    debug_assert!(s.len() == 2);
    let s0 = s.as_bytes()[0] as char;
    let s0 = s0.to_ascii_lowercase();
    let s1 = s.as_bytes()[1];
    //debug_assert!(s0 in {'a' .. 'h'})
    //debug_assert!(s1 in {'1' .. '8'})
    let c = 7 - (s0 as i8 - 'a' as i8);
    let r = s1 as i8 - '1' as i8;
    return c + r * 8;
}

fn check_mate_in(score: i64) -> i64 {
    if score > KING_VALUE_DIV_2 as i64 {
        KING_VALUE as i64 - score
    } else {
        -1
    }
}

fn alphabeta(g: &mut Game, color: Color, depth: i64, ep_pos: i64) -> Move {
    g.cut_time = Duration::from_millis(1_700);
    g.start_time = Instant::now();
    reset_statistics(g);
    let result = abeta(
        g,
        color,
        depth * V_RATIO as i64 + V_RATIO as i64 / 2,
        0,
        -AB_INF as i64,
        AB_INF as i64,
        20,
        ep_pos,
    );
    //when defined(salewskiChessDebug):
    if true {
        if cfg!(feature = "salewskiChessDebug") {
            write_statistics(&g);
        }
        //echo result
    }
    result
}

//type Flag* {.pure.} = enum
//  plain, capture, ep, promotion, procap

const FLAG_PLAIN: i32 = 0;
const FLAG_CAPTURE: i32 = 1;
const FLAG_EP: i32 = 2;
const FLAG_PROMOTION: i32 = 3;
const FLAG_PROCAP: i32 = 4;

pub fn do_move(g: &mut Game, p0: Position, p1: Position, silent: bool) -> i32 {
    p(g.board);
    let mut result: i32 = 0;
    if !is_void_at(&g, p1) {
        result = FLAG_CAPTURE;
    }
    if !silent {
        g.has_moved.insert(p0 as usize);
        g.pjm = -1;
        if is_a_pawn_at(&g, p0) && (p0 - p1).abs() == 16 {
            g.pjm = (p0 + p1) as i64 / 2;
        }
    }
    if (p1 - p0).abs() == 2 && is_a_king_at(&g, p0) {
        if col(p1) == 1 {
            g.board[p0 as usize - 1] = g.board[p0 as usize - 3];
            g.board[p0 as usize - 3] = VOID_ID;
        } else {
            g.board[p0 as usize + 1] = g.board[p0 as usize + 4];
            g.board[p0 as usize + 4] = VOID_ID;
        }
    } else if base_row(p1) && is_a_pawn_at(&g, p0) {
        g.board[p0 as usize] *= QUEEN_ID;
        result = if result == FLAG_CAPTURE {
            FLAG_PROCAP
        } else {
            FLAG_PROMOTION
        }
    } else if is_a_pawn_at(&g, p0) && is_void_at(&g, p1) && odd(p1 - p0) {
        result = FLAG_EP;
        g.board[p1 as usize - g.board[p0 as usize] as usize * 8] = VOID_ID;
    }
    g.board[p1 as usize] = g.board[p0 as usize];
    g.board[p0 as usize] = VOID_ID;
    if !silent {
        if is_a_pawn_at(&g, p1) || result != FLAG_PLAIN {
            g.history = HashMap::new();
        } else {
            let new_state = encode_board(&g, sign(g.board[p1 as usize]) as Color);
            *g.history.entry(new_state).or_insert(0) += 1;
        }
    }
    //when defined(salewskiChessDebug):
    if false {
        if !silent {
            g.debug_list.push(move_to_str(&g, p0, p1, result));
            println!("--");
            //for el in debug_list: echo el
        }
    }
    p(g.board);
    result
}

pub fn tag(g: &mut Game, si: i64) -> KKS {
    let mut kk: KK = Default::default();
    kk.sf = g.board[si as usize] as i8;
    let color = sign(kk.sf as i64) as Color;
    kk.si = si as i8;
    kk.s = 1; // generate all moves, not only captures
    let mut s: Vec<KK> = Vec::with_capacity(32);
    match kk.sf.abs() as i64 {
        PAWN_ID => walk_pawn(&g, kk, &mut s),
        KNIGHT_ID => walk_knight(&g, kk, &mut s),
        BISHOP_ID => walk_bishop(&g, kk, &mut s),
        ROOK_ID => walk_rook(&g, kk, &mut s),
        QUEEN_ID => {
            walk_bishop(&g, kk, &mut s);
            walk_rook(&g, kk, &mut s)
        }
        KING_ID => walk_king(&g, kk, &mut s),
        _ => {}
    }
    if si == 3 || si == 3 + 7 * 8 {
        const // king, void, void, void, rook, kingDelta, rookDelta -- rookDelta is unused!
      Q: [[i32; 7]; 2] = [[3, 2, 1, 1, 0, -2, 2], [3, 4, 5, 6, 7, 2, -3]];
        let k = W_KING * color as i64;
        let r = W_ROOK * color as i64;
        for i in 0..(1 + 1) {
            // castlings both sides
            let mut q = Q[i];
            if color == COLOR_BLACK as i64 {
                for j in 0..(4 + 1) {
                    q[j as usize] += 7 * 8;
                }
            }
            if g.board[q[0] as usize] == k
                && g.board[q[1] as usize] == 0
                && g.board[q[2] as usize] == 0
                && g.board[q[3] as usize] == 0
                && g.board[q[4] as usize] == r
                && !g.has_moved.contains(q[0] as usize)
                && !g.has_moved.contains(q[4] as usize)
            {
                if !(in_check(&g, q[1] as i64, color) || in_check(&g, q[2] as i64, color)) {
                    kk.di = (q[0] + q[5]) as i8;
                    s.push(kk);
                }
            }
        }
    }
    let backup = g.board;
    for el in &mut s {
        do_move(g, si as i8, el.di, true);
        if in_check(&g, king_pos(&g, color) as i64, color) {
            el.s = 0
        }
        g.board = backup;
    }
    s.retain(|&el| el.s != 0);
    return s;
}

pub fn move_is_valid2(g: &mut Game, si: i64, di: i64) -> bool {
    sign(g.board[si as usize]) as Color == COLOR_WHITE as i64
        && tag(g, si)
            .iter()
            .into_iter()
            .find(|&it| it.di == di as i8)
            .is_some()
}

const FIG_STR: [&str; 7] = ["  ", "  ", "N_", "B_", "R_", "Q_", "K_"];

fn col_str(c: Col) -> char {
    char::from_u32('H' as u32 - c as u32).unwrap()
}

fn row_str(c: Col) -> char {
    char::from_u32('1' as u32 + c as u32).unwrap()
}

pub fn get_board(g: &Game) -> Board {
    return g.board;
}

// call this after do_move()
pub fn move_to_str(g: &Game, si: Position, di: Position, flag: i32) -> String {
    //when true: // move_is_valid(si, di): // avoid unnecessary expensive test
    let mut result: String;
    if true {
        if g.board[di as usize].abs() == KING_ID && (di - si).abs() == 2 {
            result = String::from(if col(di) == 1 { "o-o" } else { "o-o-o" });
        } else {
            result = String::from(FIG_STR[g.board[di as usize].abs() as usize]);
            result.push(col_str(col(si)));
            result.push(row_str(row(si)));
            result.push(if flag == FLAG_CAPTURE || flag == FLAG_PROCAP {
                'x'
            } else {
                '-'
            });
            result.push(col_str(col(di)));
            result.push(row_str(row(di)));
            if flag == FLAG_EP || flag == FLAG_PROCAP {
                result.push_str(" e.p.");
            }
        }
        if in_check(
            &g,
            king_pos(&g, (-sign(g.board[di as usize])) as Color) as i64,
            (-sign(g.board[di as usize])) as Color,
        ) {
            result.push_str(" +");
        }
    } else {
        result = String::from("invalid move");
    }
    result
}

pub fn m_2_str(g: &Game, si: Position, di: Position) -> String {
    let mut result: String;
    let mut flag: i32 = 0;
    if !is_void_at(&g, di) {
        flag = FLAG_CAPTURE;
    }
    if base_row(di) && is_a_pawn_at(&g, si) {
        flag = if flag == FLAG_CAPTURE {
            FLAG_PROCAP
        } else {
            FLAG_PROMOTION
        }
    } else if is_a_pawn_at(&g, si) && is_void_at(&g, di) && odd(di - si) {
        flag = FLAG_EP
    }
    if true {
        // move_is_valid(si, di): // avoid unnecessary expensive test
        if g.board[di as usize].abs() == KING_ID && (di - si).abs() == 2 {
            result = String::from(if col(di) == 1 { "o-o" } else { "o-o-o" });
        } else {
            result = String::from(FIG_STR[g.board[si as usize].abs() as usize]);
            result.push(col_str(col(si)));
            result.push(row_str(row(si)));
            result.push(if flag == FLAG_CAPTURE || flag == FLAG_PROCAP {
                'x'
            } else {
                '-'
            });
            result.push(col_str(col(di)));
            result.push(row_str(row(di)));
            if flag == FLAG_EP || flag == FLAG_PROCAP {
                result.push_str(" e.p.");
            }
            // works only after doing the move
            //if in_check(king_pos((-sign(board[di])).Color), (-sign(board[di])).Color):
            //  result.add(" +")
        }
    } else {
        result = String::from("invalid move");
    }
    result
}

// Endgame = no pawns, weaker side has no queen, no rook and not two bishops.
fn setup_endgame(g: &mut Game) -> bool {
    let mut p: [i64; 13] = [0; 13];
    let mut h: [i64; 3] = [0; 3]; //array[-1..1, i64] // total number of pieces
    let mut b: [i64; 3] = [0; 3]; //array[-1..1, i64] // single bishop position
    for (i, f) in g.board.iter().enumerate() {
        p[(ARRAY_BASE_6 + *f) as usize] += 1;
        h[(1 + sign(*f)) as usize] += 1;
        if f.abs() == BISHOP_ID {
            b[(1 + sign(*f as i64)) as usize] = i as i64
        }
    }
    if p[(ARRAY_BASE_6 + W_PAWN as i64) as usize] + p[(ARRAY_BASE_6 + B_PAWN as i64) as usize] > 0 {
        return false;
    }
    if h[0] > 3 || h[2] > 3 {
        return false;
    }
    for i in B_KING..(W_KING + 1) {
        for j in POS_RANGE {
            g.freedom[i as usize][j as usize] = 0
        }
    }
    for s in [-1, 1] {
        // black, white -- set the hunting matrix for opposite king
        if p[(ARRAY_BASE_6 + QUEEN_ID) as usize * s as usize]
            + p[(ARRAY_BASE_6 + ROOK_ID) as usize * s as usize]
            == 0
            && p[(ARRAY_BASE_6 + BISHOP_ID) as usize * s as usize]
                + p[(ARRAY_BASE_6 + KNIGHT_ID) as usize * s as usize]
                < 2
        {
            continue; // of course with only two knights it is hard, but one may try.
        }
        let opp_king = -s * KING_ID;
        for i in POS_RANGE {
            if p[(ARRAY_BASE_6 + QUEEN_ID) as usize * s as usize]
                + p[(ARRAY_BASE_6 + ROOK_ID) as usize * s as usize]
                == 0
                && p[BISHOP_ID as usize * s as usize] < 2
            {
                // chase to selected corner
                if odd(col(b[(s + 1) as usize] as i8) as i8) != odd(row(b[(s + 1) as usize] as i8))
                {
                    g.freedom[opp_king as usize][i as usize] =
                        -sqr(row(i) as i64 - col(i) as i64) as i64; // sqr may be better than abs when both sites are
                } else {
                    // struggling, i.e. K + B + B vs K + B
                    g.freedom[opp_king as usize][i as usize] =
                        -sqr(row(i) as i64 + col(i) as i64 - 7) as i64;
                }
            } else {
                // chase to border and/or arbitrary corner
                g.freedom[opp_king as usize][i as usize] =
                    -sqr((2 * row(i) - 7).abs() as i64 + (2 * col(i) - 7).abs() as i64 / 2);
            }
        }
        //if s == -1: echo "White King" else: echo "Black King"
        //for i, f in board:
        //  if i mod 8 == 0: echo("")
        //  write(stdout, $freedom[opp_king][i]); write(stdout, " ");
        //echo ""
    }
    return true;
}

pub fn reply(g: &mut Game) -> Move {
    let mut result: Move = Move {
        src: 0,
        dst: 0,
        score: 0,
        control: BitSet::new(),
        promote_to: 0,
        state: 0,
    };

    //println!("{:?}", g.freedom);
    if cfg!(feature = "salewskiChessDebug") {
        for i in 0..13 {
            println!("");
            pf(g.freedom[i]);
        }
    }

    let time = Duration::from_millis(1_300);
    let mut depth = 0;

    let start_time = Instant::now(); // cpuTime();
    if setup_endgame(g) {
        if !g.is_endgame {
            g.is_endgame = true;
        }
    }
    //debugEcho(GC_getStatistics()
    for el in &mut g.tt {
        el.res.pri = i64::MIN
    }
    while depth < MAX_DEPTH {
        depth += 1;
        println!("Depth:  {}", depth);
        result = alphabeta(g, COLOR_BLACK as i64, depth as i64, g.pjm);
        //debugEcho result.score
        println!(":::{}", result.score);
        println!(
            "score: {}{}{}{}{}{}",
            result.score, "(", result.src, "-", result.dst, ")"
        );
        if result.score.abs() > SURE_CHECKMATE as i64 {
            break;
        }
        if start_time.elapsed() > time {
            //debugEcho "Time: ", cpuTime() - start_time
            println!(
                "timebreak: {}",
                start_time.elapsed().as_millis() as f64 * 1e-3
            );
            break;
        }
    }
    return result;
}

fn set_board(g: &mut Game, f: FigureID, c: Position, r: Position) {
    g.board[c as usize + r as usize * 8] = f
}

fn set_board_from_string(g: &mut Game, f: FigureID, s: String) {
    debug_assert!(s.len() == 2);
    debug_assert!(f.abs() <= KING_ID);
    let s0 = s.as_bytes()[0].to_ascii_lowercase();
    let s1 = s.as_bytes()[1];
    //debug_assert!(s0 in {'a' .. 'h'})
    //debug_assert!(s1 in {'1' .. '8'})
    let c = 7 - (s0 as i32 - 'a' as i32);
    let r = s1 as i32 - '1' as i32;
    g.board[c as usize + r as usize * 8] = f;
}

fn print(g: &Game) {
    for (p, f) in g.board.iter().enumerate() {
        if p % 8 == 0 {
            println!("");
        }
        if *f >= 0 {
            print!("{}", ' ');
        }
        print!("{}{}{}{}", f, "|", p, ' ');
        if p < 10 {
            print!("{}", ' ')
        }
    }
    println!("");
}

/*

when defined(salewskiChessDebug):
  print()

//set_board(B_KING, BC, B4)
//set_board(W_KING, BD, B5)
//set_board(B_BISHOP, BD, B4)
//set_board(B_KNIGHT, BD, B3)
//set_board(W_KNIGHT, BA, B2)
//set_board(W_BISHOP, BG, B3)

when false:
  set_board(B_KING, BC, B3)
  set_board(W_KING, BA, B1)
  set_board(B_BISHOP, BC, B2)
  set_board(B_PAWN, BE, B6)

when false:
  set_board(B_KING, BC, B3)
  set_board(W_KING, BA, B1)
  set_board(B_KNIGHT, BC, B2)
  set_board(B_BISHOP, BE, B5)

when false:
  set_board(B_KING, BC, B3)
  set_board(W_KING, BA, B1)
  set_board(B_BISHOP, BC, B2)
  set_board(B_BISHOP, BE, B5)

when false:
  set_board(B_KING, BC, B4)
  set_board(W_KING, BC, B3)
  set_board(B_KNIGHT, BD, B4)
  set_board(B_BISHOP, BD, B3)

when false:
  set_board(B_KING, BD, B3)
  set_board(W_KING, BD, B5)
  //set_board(B_QUEEN, BE, B3)
  set_board(B_QUEEN, "E3")
//set_board(B_BISHOP, BD, B3)

when false:
  set_board(B_KING, BD, B5)
  set_board(W_KING, BC, B7)
  set_board(B_QUEEN, "E8")

when false:
  set_board(B_KING, BC, B4)
  set_board(W_KING, BD, B6)
  set_board(B_QUEEN, "E8")

when false:
  set_board(B_KING, BC, B4)
  set_board(W_KING, BC, B7)
  //set_board(B_QUEEN, BE, B3)
  set_board(B_QUEEN, "E3")

when false:
  set_board(B_KING, BD, B3)
  set_board(W_KING, BD, B5)
  set_board(B_QUEEN, "E3")

*/
// 2246 lines 443 as
