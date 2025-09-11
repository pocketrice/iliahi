use std::env;
use iliahi::MarkdownDoc;

fn main() {
    let args: Vec<String> = env::args().collect();
    let md = MarkdownDoc::new(&args[1]);
    let tex = md.compile();
    println!("{}", tex);
}
