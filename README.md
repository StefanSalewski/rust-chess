# rust-chess
Rust version of salewski-chess, just as a learning excercise.

![Alt text](http://ssalewski.de/tmp/salewski_chess.png)

The Rust code avoids the use of global variables and has some bug fixes and
improvements compared to the initial Nim version.

Unfortunately the code of the Rust GTK GUI is very ugly and the GUI itself is very restricted.
Perhaps we will make a Xilem GUI later.

To allow replaying a game, we have recently added a way to print the move list: Double
click on an empty chess square, and the movelist is printed in the terminal.

A version with a simple egui GUI and a few configuration options should be soon available.

```
git clone https://github.com/stefansalewski/rust-chess.git
cd rust-chess
cargo run --release
```

