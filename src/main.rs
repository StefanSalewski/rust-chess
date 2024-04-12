// Plain GTK4 frontend for the tiny Salewski chess engine
// v 0.2 -- 12-APR-2024
// (C) 2015 - 2032 Dr. Stefan Salewski
// All rights reserved.

use gtk::gdk;
use gtk::glib::SignalHandlerId;
use gtk::prelude::*;
use gtk::{gio, Application, ApplicationWindow, DrawingArea, GestureClick};
//use pangocairo::functions::create_layout;
use std::cell::RefCell;
use std::rc::Rc;

mod engine;

// these will become Rust enums later...
const STATE_U0: i32 = 0;
const STATE_U1: i32 = 1;

struct ChessBoard {
    game: engine::Game,
    tagged: engine::Board,
    press: GestureClick,
    darea: DrawingArea,
    button_handler_id: Option<SignalHandlerId>,
    state: engine::State,
    p0: i32,
}

fn _print_variable_type<K>(_: &K) {
    println!("{}", std::any::type_name::<K>())
}

fn rot_180(b: engine::Board) -> engine::Board {
    let mut result: engine::Board = [0; 64];
    for (i, f) in b.iter().enumerate() {
        result[63 - i] = *f;
    }
    result
}

fn on_draw_event(
    widget: &DrawingArea,
    cr: &gtk::cairo::Context,
    width: i32,
    height: i32,
    data: &Rc<RefCell<ChessBoard>>,
) {
    const FIGURES: [&str; 13] = [
        "♚", "♛", "♜", "♝", "♞", "♟", "", "♙", "♘", "♗", "♖", "♕", "♔",
    ];
    const FONT: &str = "Sans 64";
    assert_eq!(width, widget.width());
    assert_eq!(height, widget.height());
    let w8 = width / 8;
    let h8 = height / 8;
    let board = rot_180(engine::get_board(&data.borrow().game));
    for (i, t) in data.borrow().tagged.iter().enumerate() {
        let h: f64;
        if *t == 2 {
            h = 0.1;
        } else if *t == 1 {
            h = 0.2;
        } else {
            h = 0.0;
        }
        if i % 2 != (i / 8) % 2 {
            cr.set_source_rgba(0.9, 0.9, 0.9 - h, 1.0);
        } else {
            cr.set_source_rgba(1.0, 1.0, 1.0 - h, 1.0);
        }
        cr.rectangle(
            ((i % 8) * w8 as usize) as f64,
            ((i / 8) * h8 as usize) as f64,
            w8 as f64,
            h8 as f64,
        );
        let _ = cr.fill();
    }
    let layout: gtk::pango::Layout = pangocairo::functions::create_layout(cr);
    let mut desc: gtk::pango::FontDescription = gtk::pango::FontDescription::from_string(FONT);
    desc.set_absolute_size((core::cmp::min(width, height) / 8 * gtk::pango::SCALE) as f64);
    layout.set_font_description(Some(&desc));
    for (i, f) in board.iter().enumerate() {
        if data.borrow().tagged[i] < 0 {
            cr.set_source_rgba(0.0, 0.0, 0.0, 0.5);
        } else {
            cr.set_source_rgba(0.0, 0.0, 0.0, 1.0);
        }
        layout.set_text(FIGURES[(*f + 6) as usize]);
        pangocairo::functions::update_layout(&cr, &layout);
        let (w, h) = layout.size();
        cr.move_to(
            ((i % 8) as i32 * w8 + w8 / 2 - w / 2 / gtk::pango::SCALE) as f64,
            ((i / 8) as i32 * h8 + h8 / 2 - h / 2 / gtk::pango::SCALE) as f64,
        );
        pangocairo::functions::show_layout(&cr, &layout);
    }
}

fn idle_func(data: &fragile::Fragile<Rc<RefCell<ChessBoard>>>) {
    data.get()
        .borrow()
        .press
        .block_signal(&data.get().borrow().button_handler_id.as_ref().unwrap());
    let m = engine::reply(&mut data.get().borrow_mut().game);
    // for mut i in data.get().borrow_mut().tagged {
    for i in &mut data.get().borrow_mut().tagged {
        *i = 0
    }
    data.get().borrow_mut().tagged[63 - m.src as usize] = 2;
    data.get().borrow_mut().tagged[63 - m.dst as usize] = 2;
    let flag = engine::do_move(
        &mut data.get().borrow_mut().game,
        m.src as i8,
        m.dst as i8,
        false,
    );
    let mut msg = engine::move_to_str(
        &mut data.get().borrow_mut().game,
        m.src as i8,
        m.dst as i8,
        flag,
    ) + &format!(" (score: {})", m.score);
    if m.score == engine::KING_VALUE as i64 {
        msg.push_str(" Checkmate, game terminated!");
    } else if m.score > engine::KING_VALUE_DIV_2 as i64 {
        msg.push_str(&format!(
            " Checkmate in {}",
            (engine::KING_VALUE as i64 - m.score) / 2
        ));
    }
    //let window: gtk::Root = data.get().borrow().darea.root().unwrap();
    let window = data
        .get()
        .borrow()
        .darea
        .root()
        .and_downcast::<gtk::Window>()
        .unwrap();
    window.set_title(Some(&msg));
    data.get()
        .borrow()
        .darea
        .set_cursor_from_name(Some("default"));
    data.get().borrow().darea.queue_draw();
    if m.score != engine::KING_VALUE as i64 {
        data.get()
            .borrow()
            .press
            .unblock_signal(&data.get().borrow().button_handler_id.as_ref().unwrap());
    }
}

fn pressed(
    _gesture: &GestureClick,
    _n_press: i32,
    xf: f64,
    yf: f64,
    data: &Rc<RefCell<ChessBoard>>,
) {
    let data_clone = fragile::Fragile::new(data.clone());
    //let _window: gtk::Root = data.borrow().darea.root().unwrap();
    let parent_window = data
        .borrow()
        .darea
        .root()
        .and_downcast::<gtk::Window>()
        .unwrap();
    data.borrow_mut().tagged = [0; 64];
    let x = xf as i32 / (data.borrow().darea.width() / 8);
    let y = yf as i32 / (data.borrow().darea.height() / 8);
    if data.borrow().state == STATE_U0 {
        data.borrow_mut().p0 = 63 - (x + y * 8);
        let h = data.borrow().p0 as i64;
        let mut hhh = data.borrow_mut();
        for i in engine::tag(&mut hhh.game, h) {
            hhh.tagged[63 - i.di as usize] = 1;
        }
        hhh.tagged[63 - h as usize] = -1;
    } else if data.borrow().state == STATE_U1 {
        let p1 = 63 - (x + y * 8);
        let h = data.borrow_mut().p0;
        {
            let mut hhh = data.borrow_mut();
            if h == p1 || !engine::move_is_valid2(&mut hhh.game, h as i64, p1 as i64) {
                if h != p1 {
                    parent_window.set_title(Some("invalid move, ignored."));
                }
                let h = hhh.p0 as usize;
                hhh.tagged[63 - h] = 0;
                hhh.tagged[63 - p1 as usize] = 0;
                hhh.darea.queue_draw(); // actually just a data.borrow().
                hhh.state = STATE_U0;
                return;
            }
        }
        let flag = engine::do_move(&mut data.borrow_mut().game, h as i8, p1 as i8, false);
        data.borrow_mut().tagged[63 - h as usize] = 2;
        data.borrow_mut().tagged[63 - p1 as usize] = 2;
        let h = data.borrow().p0 as i8;
        parent_window.set_title(Some(
            &(engine::move_to_str(&data.borrow().game, h, p1 as i8, flag)
                + " ... one moment please, reply is:"),
        ));
        data.borrow()
            .darea
            .set_cursor_from_name(Some("not-allowed"));
        gtk::glib::idle_add(move || {
            idle_func(&data_clone);
            gtk::glib::ControlFlow::Break
        });
    }
    if data.borrow().state == STATE_U1 {
        data.borrow_mut().state = STATE_U0;
    } else {
        data.borrow_mut().state += 1;
    }
    data.borrow().darea.queue_draw();
}

fn activate(app: &Application) {
    let board: ChessBoard = ChessBoard {
        game: engine::new_game(),
        tagged: [0; 64],
        press: GestureClick::new(),
        p0: -1,
        state: 0,
        darea: DrawingArea::new(),
        button_handler_id: None,
    };
    board.darea.add_controller(board.press.clone());
    board.press.set_button(gdk::BUTTON_PRIMARY);
    let window = ApplicationWindow::new(app);
    window.set_child(Some(&board.darea));
    let boardref: Rc<RefCell<ChessBoard>> = Rc::new(RefCell::new(board));
    let boardref_clone = boardref.clone();
    let boardref_clone2 = boardref.clone();
    let boardref_clone3 = boardref.clone();
    let boardref_clone4 = boardref.clone();
    boardref_clone
        .borrow()
        .darea
        .set_draw_func(move |w, cr, width, height| {
            on_draw_event(w, cr, width, height, &boardref_clone2);
        });
    let _tagged: Vec<i32> = vec![1, 2];
    //let _taggedref: Rc<RefCell<Vec<i32>>> = Rc::new(RefCell::new(tagged));
    let button_handler_id = Some(boardref_clone4.borrow().press.connect_pressed(
        move |pre, n_press, xf, yf| {
            pressed(pre, n_press, xf, yf, &boardref_clone);
        },
    ));
    boardref_clone3.borrow_mut().button_handler_id = button_handler_id;
    window.set_default_size(800, 800);
    window.set_title(Some(
        "Tiny chess engine demo, GTK4 GUI with Unicode chess pieces, ported from Nim to Rust",
    ));
    window.present();
}

const APP_ID: &str = "org.gtk.example";

fn main() {
    let app = Application::new(Some(APP_ID), gio::ApplicationFlags::empty());
    app.connect_activate(activate);
    app.run();
}
// 269 lines
