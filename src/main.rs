use anyhow::Error;
use iliahi::Identifier;
use iliahi::{export_overleaf, scan_lhis, MarkdownDoc, Promise};
use std::path::Path;
use std::{env, fs};

fn main() -> Result<(), Error>{
    let args: Vec<String> = env::args().collect();
    scan_lhis()?;

    let (md, title) = {
        let path = Path::new(&args[1]);
        (path, path.file_stem().unwrap().display().to_string())
    };

    let doc = MarkdownDoc::from(md);
    let tex = doc.compile();

    let pr_tex = Promise::only_wish("Writing TeX");
    fs::write(Path::new(&format!("{}.tex", title)), &tex)?;
    pr_tex.fulfill(true);

    let expo = export_overleaf(tex, true)?;
    open::that_detached(expo.compile());
    Ok(())
}