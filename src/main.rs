use anyhow::Error;
use iliahi::{export_overleaf, scan_lhi, MarkdownDoc, Identifier, to_clipboard};
use std::env;
use std::fs::File;

fn main() -> Result<(), Error>{
    let args: Vec<String> = env::args().collect();
    scan_lhi(&File::open("req.lhi")?);
    let md = MarkdownDoc::new(&args[1]);
    let tex = md.compile();
    to_clipboard(&*tex);

    Ok(())
}
