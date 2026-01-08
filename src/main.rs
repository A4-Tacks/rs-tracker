use std::{env::args, io::{self, Write, stdin}, process::{Command, Stdio, exit}};

use getopts_macro::getopts_options;
use rs_tracker::{Config, Debug, edits};

fn main() {
    let options = getopts_options! {
        -n, --no-debug      "not print return value debug";
        -a, --expand-debug  "use `{:#?}` print";
        -e, --stderr        "use eprintln output";
        -s, --label-stmts   "insert label before statements";
        -i, --indent        "indent function name";
        -d, --delete        "delete mode, delete generated _track";
        -p, --program=PATH  "rust-analyzer path";
        -h, --help          "show help messages";
        -v, --version       "show version";
    };
    let matched = match options.parse(args().skip(1)) {
        Ok(x) => x,
        Err(e) => {
            eprintln!("{e}");
            exit(2)
        },
    };
    if matched.opt_present("help") {
        let brief = options.short_usage(args().next().as_deref().unwrap_or("?"));
        let usage = options.usage(&brief);
        println!("{}", usage.trim_end());
        return;
    }
    if matched.opt_present("version") {
        let v = env!("CARGO_PKG_VERSION");
        println!("{v}");
        return;
    }
    if let Some(arg) = matched.free.first() {
        eprintln!("Excess argument: {arg:?}");
        exit(2)
    }

    let mut debug = if !matched.opt_present("no-debug") { Debug::Inline } else { Debug::Disable };
    if matched.opt_present("expand-debug") {
        debug = Debug::Expand;
    }
    let config = Config {
        debug,
        stderr:         matched.opt_present("stderr"),
        label_stmt:     matched.opt_present("label-stmts"),
        indent_name:    matched.opt_present("indent"),
    };
    let program = matched.opt_str("program").unwrap_or("rust-analyzer".to_owned());

    let mut src = match io::read_to_string(stdin().lock()) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{e}");
            exit(1)
        },
    };
    let mut child = Command::new(program)
        .arg("parse")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("cannot start rust-analyzer");
    child.stdin.take()
        .expect("cannot init piped stdin")
        .write_all(src.as_bytes())
        .expect("write to rust-analyzer error");

    let r_a_out = child.wait_with_output().expect("cannot take rust-analyzer outputs");
    if !r_a_out.status.success() {
        eprintln!("rust-analyzer exit code fail");
        exit(r_a_out.status.code().unwrap_or(128))
    }
    let rowan = String::from_utf8_lossy(&r_a_out.stdout);

    let node = rs_tracker::make(&rowan);
    if !matched.opt_present("delete") {
        let inserts = rs_tracker::term_expr_inserts(&node, &src, config);
        edits::apply_inserts(inserts, &mut src);
    } else {
        let deletes = rs_tracker::remove_tracks(&node, &src);
        edits::apply_deletes(deletes, &mut src);
    }
    println!("{}", src.trim_end());
}
