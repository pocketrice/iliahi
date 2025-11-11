use std::fmt::{Display, Formatter};
use anyhow::{anyhow, Error};
use clap::{Parser, ArgAction, Command, Arg, CommandFactory};
use clap_derive::Parser;
use iliahi::{regextract_n, Identifier, FMT_ANCHOR};
use iliahi::{export_overleaf, scan_lhis, MarkdownDoc, Promise};
use std::path::{Path, PathBuf};
use std::fs;
use clap::error::ErrorKind;
use fancy_regex::Regex;
use lazy_static::lazy_static;

static CLI_ARG_COLOR: AnsiColor = AnsiColor::YELLOW;

lazy_static! {
    static ref RE_INPUT: Regex = Regex::new(r"^(.*\/)?(?<basename>[^\/^.]+)\.(?<extension>[a-zA-z0-9]+)$").unwrap();
}

#[derive(Clone)]
pub enum AnsiColor {
    BLACK,
    RED,
    GREEN,
    YELLOW,
    BLUE,
    PURPLE,
    CYAN,
    WHITE,
    RESET
}

impl AnsiColor {
    pub fn apply(&self, target: &str) -> String {
        format!("{}{}{}", self, target, AnsiColor::RESET)
    }

    pub fn str(&self) -> &str {
        match &self {
            AnsiColor::BLACK => "\x1b[0;30m",
            AnsiColor::RED => "\x1b[0;31m",
            AnsiColor::GREEN => "\x1b[0;32m",
            AnsiColor::YELLOW => "\x1b[0;33m",
            AnsiColor::BLUE => "\x1b[0;34m",
            AnsiColor::PURPLE => "\x1b[0;35m",
            AnsiColor::CYAN => "\x1b[0;36m",
            AnsiColor::WHITE => "\x1b[0;37m",
            AnsiColor::RESET => "\x1b[0;0m"
        }
    }

    /// Blindly formats the given string for [`FMT_ANCHOR`](iliahi::FMT_ANCHOR), replacing
    /// left and right with color and reset respectively.
    ///
    /// # Caveats
    /// It is not possible to escape chars reserved by the anchor currently,
    /// so refrain from using any of the two reserved chars if needed as plain chars.
    pub fn paint(&self, fmstr: &str) -> String {
        let (l,r) = {
            let mut chars = FMT_ANCHOR.chars();
            (chars.next().unwrap(), chars.next().unwrap())
        }; // assured that `FMT_ANCHOR` is ≥2 chars

        (&fmstr.replace(l, self.str())).replace(r, AnsiColor::RESET.str())
    }
}

impl Display for AnsiColor {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.str())
    }
}

#[derive(Ord, PartialOrd, Eq, PartialEq, Debug)]
enum FileState { // greatest to lowest
    MD(String),
    LHO(String),
    TEX(String),
    PDF(String),
}
impl FileState {
    fn from(str: &str) -> Result<FileState, Error> {
        if let [Some(name), Some(ext)] = regextract_n(&RE_INPUT, str, ["basename", "extension"]) { // <-- per unzip's behavior, respect working directory by placing output there regardless of original's dir
            match ext.as_str() {
                "pdf" => Ok(FileState::PDF(name)),
                "tex" => Ok(FileState::TEX(name)),
                "lho" => Ok(FileState::LHO(name)),
                "md" => Ok(FileState::MD(name)),
                _ => Err(anyhow!("Invalid file type"))
            }
        } else {
            Err(anyhow!("Invalid file name"))
        }
    }
}

impl Display for FileState {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            FileState::MD(_) => ".MD",
            FileState::LHO(_) => ".LHO",
            FileState::TEX(_) => ".TEX",
            FileState::PDF(_) => ".PDF"
        })
    }
}

/// Returns true if for every nth cond that is true, 0..n-1 conds are true; false otherwise.
/// This is reminiscent to a lower triangular matrix, hence "wedge-shaped".
#[inline(always)]
fn condwedge<const N: usize>(conds: [bool; N]) -> bool {
    for i in 0..N {
        if !conds[0..i].iter().all(|c| *c) { return false }
    }

    true
}


// macro_rules! condwedge {
//     ( $( $cond:expr ),+ ) =>
//         {
//             let conds = [$($cond,)+];
//
//             true for i in conds.len() {
//                 || (true for j in 0..i {
//                     && conds[j]
//                 })
//             }
//         }
// }

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Converts any directly to .pdf
    #[arg(short, long, action,
        conflicts_with_all(&["obj", "tex", "pdf"]),
    )]
    xpress: bool,

    /// Converts .md to .lho; stage 1
    #[arg(short, long, action)]
    obj: bool,

    /// Converts .lho to .tex; stage 2
    #[arg(short, long, action)]
    tex: bool,

    /// Converts .tex to .pdf; stage 3
    #[arg(short, long, action)]
    pdf: bool,

    /// Retain residual files from lualatex (e.g. .aux)
    #[arg(short, long, action)]
    residuals: bool,

    /// Exports to Overleaf via proxy host
    #[arg(short, long, action)]
    export: bool,

    /// Import decls from input .lhi
    #[arg(short, long, action,
        conflicts_with_all(&["xpress", "obj", "tex", "pdf", "residuals", "export"])
    )]
    import: bool,

    /// decl files to import OR files to process
    inputs: Vec<PathBuf>,
}

// iliahi a16.[EXT]          ... a16.[nth EXT] -> a16.[n+1th EXT]
// iliahi -o a16.md          ... a16.md -> a16.lho
// iliahi -o a16.md a17.md   ... (a16.md -> a16.lho, a17.md -> a17.lho)
// iliahi -t a16.lho         ... a16.lho -> a16.tex
// iliahi -p a16.tex         ... a16.tex -> a16.pdf
// iliahi -pr a16.tex        ... a16.tex -> [residuals] -> a16.pdf
// iliahi -pe a16.tex        ... a16.tex -> a16.pdf -> export
// iliahi -opre a16.md       ... a16.md -> a16.lho -> a16.tex -> [residuals] -> a16.pdf
// iliahi -x a16.md          ... a16.md/lho/tex -> a16.pdf
// iliahi -xe a16.md         ... a16.md/lho/tex -> a16.pdf -> export
// iliahi +i

fn main() -> Result<(), Error>{
    let Args { xpress, obj, tex, pdf, residuals, export, import, inputs }  = Args::parse();
    let mut cmd = Args::command();
    let is_auto = !(xpress || obj || tex || pdf || export || import);

    // post-parse validation
    // * determine lowest common filetype; all ops must overcompensate rather than under (i.e. ops skip if succeeding but fail if preceding)
    // * filetype and valid args (-n...)
    // * residuals REQ xpress || pdf
    let mut ftypes = (&inputs).into_iter()
        .map(|i| FileState::from(&i.display().to_string()))
        .filter_map(|r| r.ok())
        .collect::<Vec<FileState>>();
    ftypes.sort();


    if let Some(lcf) = ftypes[..].get(0) {
        let mut conds: Vec<(&str, bool)> = vec![("--obj", obj), ("--tex", tex), ("--pdf", pdf), ("--export", export), ("--xpress", xpress)];

        let subp = {
            let rng = match lcf {
                FileState::MD(_) => 0..5,
                FileState::LHO(_) => 1..5,
                FileState::TEX(_) => 2..5,
                FileState::PDF(_) => 3..4 // ..exclude -x
            };

            conds[rng].to_owned()
        };

        // Subspace of entire space to search (while individually may not be applicable, exists some combo that is applicable)
        // `miss` must only contain items from the subspace, `invs` must only contain items not from subspace. Simple as a clam!
        let (miss, invs) = {
            let (mut s1, s2): (Vec<_>, Vec<_>) = conds.into_iter().partition(|c| { subp.contains(c) });
            // let i = conds.iter_mut().partition_in_place(|c| { subp.contains(c) }); <-- great idea but sadly `pip` clobbers ordering!!
            // let (s1, s2) = conds.split_at_mut(i);

            // a clever trick that minimizes iter time(?) and gets all the holes (clamped left!)
            s1.dedup_by(|(_, a), (_, b)| *a && *b);
            while let Some(_) = s1.pop_if(|(_, c)| !*c) {};

            (s1.into_iter()
                 .filter(|(_, c)| !*c)
                 .map(|(p, _)| p)
                 .collect::<Vec<&str>>(),
             s2.into_iter()
                 .filter(|(_, c)| *c)
                 .map(|(p, _)| p)
                 .collect::<Vec<&str>>()
            )
        };

        match (miss.len(), invs.len()) {
            _ if residuals && is_auto && !matches!(lcf, FileState::TEX(_)) => cmd.error(ErrorKind::ArgumentConflict, CLI_ARG_COLOR.paint(&format!("auto mode with {{{}}} incompatible with {{--residual}}", lcf))).exit(),
            _ if residuals && !(pdf || xpress) => cmd.error(ErrorKind::MissingRequiredArgument, CLI_ARG_COLOR.paint("use of {--residual} requires either {--pdf}, {--xpress}, or auto mode with {.TEX}")).exit(),
            (0, 0) => (),
            (_, 0) => cmd.error(ErrorKind::MissingRequiredArgument, CLI_ARG_COLOR.paint(&format!("operation requires {{{}}}", miss.join(",")))).exit(),
            (0, _) => cmd.error(ErrorKind::ArgumentConflict, CLI_ARG_COLOR.paint(&format!("file type {{{}}} incompatible with {{{}}}", lcf, invs.join(",")))).exit(),
            (_, _) => cmd.error(ErrorKind::ArgumentConflict, CLI_ARG_COLOR.paint(&format!("file type {{{}}} incompatible with {{{}}} and operation requires {{{}}}", lcf, invs.join(","), miss.join(",")))).exit(),
        }
    } else {
        cmd.error(
            ErrorKind::InvalidValue, CLI_ARG_COLOR.paint("no valid file types found, must be {.(MD|LHO|TEX|PDF)}"),
        ).exit();
    }


    // match lcf {
    //     _ if xpress => {
    //
    //     },
    //
    //     Some(FileState::MD(_)) =>
    //         if !(!object || condwedge([object, pdf, export])) {
    //             cmd.error(
    //                 ErrorKind::MissingRequiredArgument, format!("file type {} is incompatible with the given flags", AnsiColor::YELLOW.apply(".md")),
    //             ).exit();
    //         },
    //     Some(FileState::LHO(_)) =>
    //         if !condwedge([object, pdf, export]) {
    //            cmd.error(
    //                ErrorKind::MissingRequiredArgument, format!("file type {} is incompatible with the given flags", AnsiColor::YELLOW.apply(".lho")),
    //            ).exit();
    //         },
    //     Some(FileState::TEX(_)) =>
    //         if !condwedge([pdf, export]) {
    //             cmd.error(
    //                 ErrorKind::MissingRequiredArgument, format!("file type {} is incompatible with the given flags", AnsiColor::YELLOW.apply(".tex")),
    //             ).exit();
    //         },
    //     Some(FileState::PDF(_)) =>
    //         if !export {
    //             cmd.error(
    //                 ErrorKind::MissingRequiredArgument, format!("file type {} is incompatible with the given flags", AnsiColor::YELLOW.apply(".pdf")),
    //             ).exit();
    //         },
    //     _ => {
    //
    //     }
    // }


    scan_lhis()?;



    // let (md, title) = {
    //     let path = &args.inputs[0];
    //     (path, path.file_stem().unwrap().display().to_string())
    // };
    //
    // let doc = MarkdownDoc::from(md);
    // let tex = doc.compile();
    //
    // let pr_tex = Promise::only_wish("Writing TeX");
    // fs::write(Path::new(&format!("{}.tex", title)), &tex)?;
    // pr_tex.fulfill(true);
    //
    // let expo = export_overleaf(tex, true)?;
    // open::that_detached(expo.compile());
    Ok(())
}