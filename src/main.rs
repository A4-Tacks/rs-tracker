use std::{env::args, io::{self, Write, stdin}, process::{Command, Stdio, exit}};

use getopts_macro::getopts_options;
use rs_tracker::{Config, Debug, edits};

fn parse_source(program: &str, src: &str) -> rs_tracker::Node {
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
    rs_tracker::make(&rowan)
}

fn main() {
    let options = getopts_options! {
        -n, --no-debug      "not print return value debug";
        -N, --no-newline    "not insert newline before some tracks";
        -a, --expand-debug  "use `{:#?}` print";
        -e, --stderr        "use eprintln output";
        -s, --label-stmts   "insert label before statements";
        -l, --label-lets    "insert label after let statements";
        -i, --indent        "indent function name";
        -t, --trim-closures "trim closure labels, only track functions";
        -d, --delete        "delete mode, delete generated _track";
        -D, --delete-loop   "like --delete, but delete until source unchanged";
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
        let desc = env!("CARGO_PKG_DESCRIPTION");
        let brief = options.short_usage(args().next().as_deref().unwrap_or("?"));
        let usage = options.usage(&format!("{brief} [FILE]\n{desc}"));
        println!("{}", usage.trim_end());
        return;
    }
    if matched.opt_present("version") {
        let v = env!("CARGO_PKG_VERSION");
        println!("{v}");
        return;
    }

    let mut debug = if !matched.opt_present("no-debug") { Debug::Inline } else { Debug::Disable };
    if matched.opt_present("expand-debug") {
        debug = Debug::Expand;
    }
    let config = Config {
        debug,
        inline:         matched.opt_present("no-newline"),
        stderr:         matched.opt_present("stderr"),
        label_stmt:     matched.opt_present("label-stmts"),
        label_lets:     matched.opt_present("label-lets"),
        indent_name:    matched.opt_present("indent"),
        only_fn:        matched.opt_present("trim-closures"),
    };
    let program = matched.opt_str("program").unwrap_or("rust-analyzer".to_owned());

    if let Some(arg) = matched.free.get(1) {
        eprintln!("Excess argument: {arg:?}");
        exit(2)
    }
    let edit_path = matched.free.first().filter(|it| *it != "-");
    let src = edit_path
        .map(|path| fs_err::read_to_string(path).map_err(|e| e.to_string()))
        .unwrap_or_else(|| io::read_to_string(stdin().lock()).map_err(|e| e.to_string()));
    let mut src = match src {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{e}");
            exit(1)
        },
    };

    let mut node = parse_source(&program, &src);
    if matched.opt_present("delete-loop") {
        let mut prev_len = src.len();
        for _ in 0..50 {
            let deletes = rs_tracker::remove_tracks(&node, &src);
            edits::apply_deletes(deletes, &mut src);

            if std::mem::replace(&mut prev_len, src.len()) == src.len() {
                break
            }
            node = parse_source(&program, &src);
        }
    } else if matched.opt_present("delete") {
        let deletes = rs_tracker::remove_tracks(&node, &src);
        edits::apply_deletes(deletes, &mut src);
    } else {
        let inserts = rs_tracker::term_expr_inserts(&node, &src, config);
        edits::apply_inserts(inserts, &mut src);
    }
    match edit_path {
        Some(path) => fs_err::write(path, &src).unwrap(),
        None => println!("{}", src.trim_end()),
    }
}
