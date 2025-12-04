use std::{env::args, io::{self, stdin}, process::exit};

use getopts_macro::getopts_options;
use rs_tracker::Config;

fn main() {
    let options = getopts_options! {
        -n, --no-debug      "not print return value debug";
        -e, --stderr        "use eprintln output";
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
    let config = Config {
        debug: !matched.opt_present("no-debug"),
        stderr: matched.opt_present("stderr"),
    };

    let src = match io::read_to_string(stdin().lock()) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("{e}");
            exit(1)
        },
    };
    let node = rs_tracker::make_node(&src);
    let inserts = rs_tracker::term_expr_inserts(&node, config);
    let mut out = node.to_string();
    rs_tracker::apply_inserts(inserts, &mut out);
    println!("{}", out.trim_end());
}
