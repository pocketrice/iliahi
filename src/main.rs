use std::env;
use iliahi::{to_clipboard, MarkdownDoc};

fn main() {
    let args: Vec<String> = env::args().collect();
    let md = MarkdownDoc::new(&args[1]);
    let tex = md.compile();
    to_clipboard(&tex);
}
