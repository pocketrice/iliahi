use std::env;
use std::error::Error;
use std::fs::File;
use iliahi::{scan_lhi, to_clipboard, MarkdownDoc};

fn main() -> Result<(), Box<dyn Error>>{
    let args: Vec<String> = env::args().collect();
    scan_lhi(&File::open("req.lhi")?);
    let md = MarkdownDoc::new(&args[1]);
    let tex = md.compile();
    to_clipboard(&tex);

    Ok(())
}
