#![feature(portable_simd, vec_into_raw_parts, if_let_guard)]

use either::{Either, Left, Right};
use std::alloc::{alloc_zeroed, Layout};
use std::fs::{File, OpenOptions};
use std::io::{stdin, stdout, BufRead, BufReader, Write};
use std::{fs, ptr};
use chrono::{Datelike, Local};
use fancy_regex::{Captures, Regex};
use std::iter::{Peekable};
use std::ops::{RangeBounds};
use std::process::{Command, Stdio};
use std::simd::{LaneCount, Mask, Simd, SupportedLaneCount};
use std::simd::prelude::{SimdInt, SimdPartialOrd};
use std::slice::SliceIndex;
use std::string::FromUtf8Error;
use std::time::Instant;
use yaml_rust::{yaml, Yaml, YamlEmitter, YamlLoader};

type TeXContent = String;
type URL = String;
type Fmtr<'a> = &'a str;


static VERSION_NUM: &str = "0.1.0";
static VERSION_BRANCH: &str = "stable";


static FMT_ANCHOR: &str = "{}";
static REGEX_META_NCAP: &str = r".*\(\?P<(?P<ncap>.+)>.*\).*"; // <-- note, this means only limited to one named capture group for regmerge!
static REGEX_SEG_D1: &str = r"\*\*(?P<eid>.+)\.\*\*";
static REGEX_SEG_D2: &str = r"\*\((?P<eid>.+)\)\*";
static REGEX_SEG_ANY: &str = r"^((\*)|(\*\*))(?(2)\(|)(?P<eid>[a-zA-Z0-9]+)(?(2)\)\*|\.\*\*)$"; // <-- requires use of fancy-regex;
static REGEX_DECL_VALID: &str = r"\\newcommand\{\\(?P<id>[a-z]+)}(\[(?P<pc>\d+)])?\{(?P<macro>.*)}";
static REGEX_DECL_INVALID: &str = r"\\newcommand\{\\(?P<id>.+)}(\[(?P<pc>.+)])?\{(?P<macro>.*)}";
static REGEX_DECL_ID: &str = r"\\newcommand\{\\(?P<id>[a-z]+)}(\[\d+])?\{.*}";
static REGEX_USES_FINAL: &str = r".*(\\finalans\{.+\}).*";
static REGEX_USES_QQ: &str = r"((\\(q+|[;,>:]|(hspace)))*)(?<nq>.+)";
static REGEX_COMMS: &str = "%{2}.*?%{2}";
static REGEX_PREPROC_DEFINE: &str = r"^DEFINE *\( *(?<ident>.+?) *, *(?<value>.*? *)\)$";
static REGEX_PREPROC_INCLUDE: &str = r"^INCLUDE *\( *(?<ident>.+?)\.lhi *\)$";

// static REGEX_QQ: &str = r"(\\(q+|[;,>:]|(hspace)))";

//static REGEX_EID_LAYERS: [&str; 3] = [r"(?P<eid>\d+\.", r"\((?P<eid>[a-z]+))", r"\((?P<eid>["]

// static REGEX_LHI_COMMENT: &str = r"^(\#\#).*"; <-- replaced with str::starts_with() for now but for semantics may want to replace with pattern match

static CLASS_DEFAULT: &str = "Math 3345";
static META_DEFAULT: &str = "MWF 1:50-2:45, Katz";
static AUTHOR_DEFAULT: &str = "Lucas Xie";
static PATH_DB: &str = "db.yaml";
static PATH_TEMPLATE: &str = "template.tex";
static NO_MATCH: &str = "";
static LINE_BREAK: &str = "<hr>";
static FINAL_FMT: Fmtr = r"\finalans{}";
static PROMISE_FMT: Fmtr = "{}... ";
static PROMISE_OK: &str = "OK";
static OVERLEAF_URL: Fmtr = "https://www.overleaf.com/docs?snip_uri[]=data:application/x-tex;base64,{}";
static BASE64_VECTOR_SIZE: usize = 64; // <-- 2024 standard is AVX-512 (512b) or SVE2 (128-1024b in 128b incr); using Assigments 1-9 avg=4620c, stdev=2085c. Using 1024b/128B would be most optimal but seems like 512b/64B is safer.
//static BASE64_VECTOR_OFFS: [i8; 5] = [b'A' as i8, (b'a' - 26) as i8, (52 - b'0') as i8, (62 - b'+') as i8, (63 - b'/') as i8]; // <-- add these to 6-bit value to receive the base64 representation!

// raws         maps      ascii
// 0..=25  ->   A-Z   -> +65
// 26..=51 ->   a-z   -> +97
// 52..=61 ->   0-9   -> +48
// 62      ->    +    -> +43
// 63      ->    /    -> +47

// static EID_LAYERS: (char, char, char) = ('1', 'a', 'i') <-- TODO i increments by roman numeral instead...

/// Representation and destructuring of Assignment Markdown (AMD)
/// in preparation for compilation to pure TeX.
pub struct MarkdownDoc {
    title: String,
    decls: Vec<String>,
    segs: Vec<Segment>, // assume (1)...($LEN), bound by bold TODO [Segment] should be more performant as on stack (esp. for arr of arr)
    cache: Option<u8> // TODO make this (Sized) byte array
}

// macro_rules! tex_decl { <-- relic of using technique of actually replacing placeholders in content... no need!
//
// }

/// Matches n elements against item.
/// This is redundant as you may actually pass & and | notation into `matches!`.
/// So, simply some macro-writing practice!
#[deprecated]
macro_rules! matches_n {
    // ▼ item to match against
    // ▼                   ▼ matchers to try
    ( $target:expr, $( $cand:pat ),+ ) => //$( $cand:pat $(if $:expr)? $(,)?),+ ) => {
        {
            $(
                matches!($target, $cand) |
            )+

            true
        }
}

/// Representation of a preprocessor directive containing a basic
/// constructive behavior applied either globally or locally.
///
/// The use of `PreprocessorDirective`s produces a standard .pli preprocessed file.
pub enum PreprocessorDirective {
    TrimComms,
    MarkFinal,
    Define(String, String),
    Include(String), // <-- purposefully doesn't abide by IgnoreDecls if you want to selectively append and remove things :)
    IgnoreDecls, // <-- note, this may seem useless but if you're just using default decl lib then this saves parsing decls!
    EnforceSpacing,
    FlatSegs,
}

impl PreprocessorDirective {
    /// Creates new instance from string representation.
    ///
    /// # Caveats
    /// Note that `directive` will be in the form of "(.*)"; note
    /// the lack of both directive indicator and newline char.
    pub fn from(directive: &str) -> Result<PreprocessorDirective, ()> {
        let (re_def, re_incl) = (Regex::new(REGEX_PREPROC_DEFINE).unwrap(), Regex::new(REGEX_PREPROC_INCLUDE).unwrap());

        match directive {
            "TRIM_COMM" => Ok(PreprocessorDirective::TrimComms),
            "IGNORE_DECLS" => Ok(PreprocessorDirective::IgnoreDecls),
            "MARK_FINAL" => Ok(PreprocessorDirective::MarkFinal),
            "ENFORCE_SPACING" => Ok(PreprocessorDirective::EnforceSpacing),
            "FLAT_SEGS" => Ok(PreprocessorDirective::FlatSegs),
            d if let (Some(ident), Some(value)) = regextract_n(&re_def, d, &["ident", "value"]).iter().take(2).collect() => Ok(PreprocessorDirective::Define(*ident, *value)),
            d if let Some(ident) = regextract(&re_incl, d, "ident") => Ok(PreprocessorDirective::Include(ident)), // <-- you could technically throw a fit here for nonexistant lib, but better to save until parse-time anyway. Plus, the mere existence of a directive does not constitute validity.
            _ => Err(()),
        }
    }

    /// Preprocesses the given content.
    ///
    /// # Caveats
    /// Note that this was originally designed not to fully process an entire batch of lines but instead individually,
    /// performance-wise it would be per-line anyway and this allows for parallelizing a batch of
    /// directives simultaneously instead of sequentially reprocessing every batch.
    ///
    /// This does mean that no relative operations/optimizations are possible
    /// (e.g. `PreprocessorDirective::IgnoreDecls` using decls locality to shortcut).
    pub fn preprocess(directives: &Vec<PreprocessorDirective>, content: &mut Vec<String>) {
        let (dirs_global, dirs_local): (Vec<_>, Vec<_>) = directives.iter().partition(|&d| matches!(d, PreprocessorDirective::Include(_) | PreprocessorDirective::MarkFinal | PreprocessorDirective::IgnoreDecls));

        for dir in dirs_global {
            match dir {
                PreprocessorDirective::Include(ident) => { // <-- #include are injected blindly to the top of the file for the sake of speed.
                    let lhi = File::open(&ident).expect(&format!("The include file, {}, does not exist or could not be opened", &ident));
                    let mut num_decl = 0usize;
                    let decls = fs::read_to_string(&ident)
                        .expect(&format!("The include file, {}, could not be read", &ident))
                        .split("\n")
                        .for_each(|d| {
                            content.push(String::from(d));
                            num_decl += 1;
                        });

                    content.rotate_right(num_decl); // <-- pushing to tail of vec then single memory realloc feels more performant than individually shifting all contents one-by-one...


                },
                PreprocessorDirective::MarkFinal => {
                    let (re_qq, re_final, re_seg) = (Regex::new(REGEX_USES_QQ).unwrap(), Regex::new(REGEX_USES_FINAL).unwrap(), Regex::new(REGEX_SEG_ANY).unwrap());
                    let fmst = FmtStr::from(FINAL_FMT).unwrap();

                    // A story in three parts :)
                    //
                    // (i)
                    // I thought mut `slice::windows` could work but it also hinted that `windows_mut` behavior may be emulated using `as_slice_of_cells` but as String is ?Sized
                    // you only have access to `get_mut` which kind of gets messy.
                    //
                    // (ii)
                    // Hmm... perhaps yoinking indices to later modify in-place works? Ah, XOR trick might work!
                    // 0
                    // 0 ^ c[1] ^ c[3] <-- 0 ^ n = n
                    // c[1] ^ c[3] // <-- these are non-hit indices
                    //
                    // c[1] ^ c[3] (^ c[1] ^ c[2] ^ c[3] ^ c[4]) // <-- xor all elements in set
                    // c[2] ^ c[4] // <-- voila, hit indices!
                    //
                    // ...the problem is unless you're dealing with 1-2 items extracting values from this XOR
                    //    lump takes a lot more work. ah.
                    //
                    //
                    // (iii)
                    // ...turns out this wasn't a tradeoff at all, I can just use some clever indexing lol
                    // take that bchk!!! >:)

                    for i in 1..(content.len()-2) {
                        let [mut pre, mut curr, peek, ..]= &content[(i-1)..(i+1)];
                        if re_seg.is_match(peek).unwrap() { // <-- final injection should occur on curr or pre... depending on if \n is present before segment identifier
                            let mut target = if curr.is_empty() { pre } else { curr };
                            if re_final.is_match(&target).unwrap() { break };

                            let nq = regextract(&re_qq, &target, "nq").unwrap();
                            segpend(&mut target, (target.len() - nq.len()).., &fmst);
                        }
                    }
                },
                PreprocessorDirective::IgnoreDecls => { //                          <-- although this may technically be "local" rather "global", if decl notation changes and must be inspected relatively this helps.
                    let re_declv = Regex::new(REGEX_DECL_VALID).unwrap();//      additionally, as this is simply a remove operation I feel a simple `retain` may be more performant
                    content.retain(|l| re_declv.is_match(l).unwrap());
                },
                _ => unreachable!()
            }
        }

        let re_seg_d2 = Regex::new(REGEX_SEG_D2).unwrap();
        for line in content {
            for dir in dirs_local {
                match dir {
                    PreprocessorDirective::TrimComms => {
                        let re_comms = Regex::new(REGEX_COMMS).unwrap();
                        re_comms.replace_all(line, "");
                    },
                    PreprocessorDirective::Define(ident, value) => {
                        *line = line.replace(ident, &value);
                    },
                    PreprocessorDirective::EnforceSpacing => {
                        if line.chars().last().is_some_and(|c| c != '\n') {
                            line.push('\n');
                        }
                    },
                    PreprocessorDirective::FlatSegs => {
                        if re_seg_d2.is_match(line).is_ok_and(|m| m) {
                            line.clear();
                        }
                    },
                    _ => unreachable!()
                }
            }
        }
    }

    /// Converts directive into string-form.
    ///
    /// This is identical to how it was initially parsed as, though including the directive indicator (&) but without newline.
    pub fn convert(&self) -> String {
        match &self {
            PreprocessorDirective::TrimComms => String::from("&TRIM_COMM"),
            PreprocessorDirective::MarkFinal => String::from("&FINALIZE"),
            PreprocessorDirective::EnforceSpacing => String::from("&ENFORCE_SPACING"),
            PreprocessorDirective::FlatSegs => String::from("&FLATTEN"),
            PreprocessorDirective::IgnoreDecls => String::from("&IGNORE_DECL"),
            PreprocessorDirective::Define(ident, value) => format!("&DEFINE({}, {})", ident, value).to_string(),
            PreprocessorDirective::Include(ident) => format!("&INCLUDE({})", ident).to_string(),
        }
    }
}

/// An operation segmentator based on wish/fulfill-design.
pub struct Promise {
    ident: String,
    ts: Option<Instant>
}

impl Promise {
    /// Create new promise.
    /// Note that this will timestamp automatically at instantiation time and stop at drop.
    fn new(id: String) -> Promise {
        Promise { ident: FmtStr::only_fmt(PROMISE_FMT, &id).unwrap(), ts: None }
    }

    /// Creates new promise and wishes upon it, returning promise for fulfillment.
    fn only_wish(ident: String) -> Promise {
        let mut pr = Promise::new(ident);
        pr.wish();
        pr
    }

    /// Wishes the promise, expecting fulfillment.
    fn wish(&mut self) {
        self.ts = Some(Instant::now());
        print!("{}", self.ident);
    }

    /// Fulfills the promise, thus closing it.
    fn fulfill(self) { // <-- more behavior can go here if needed (don't touch Drop; may want to allow a cleanup function etc etc.)
        drop(self);
    }
}

impl Drop for Promise {
    fn drop(&mut self) {
        println!("{} ({:.2}ms)", PROMISE_OK, self.ts.and_then(|t| Some(t.elapsed().as_micros() as f32 / 1000.0)).unwrap_or(0.0));
    }
}

pub struct Label { // <-- e.g. (1), ii., <hr>5</hr>
    ident: String,   // raw value; 1
    ornament: FmtStr // outside wrapper; ({})
}

impl Label {
    fn new(ident: String, ornament: String) -> Result<Label, ()> {
        match FmtStr::from(&ornament) {
            Ok(fmts) => Ok(Label { ident, ornament: fmts }),
            Err(_) => Err(()),
        }
    }

    fn from(str: String) -> Result<Label, ()> {
        // note: the label string must distinguish ident and ornament by wrapping ident with {}.
        // e.g.: "({a})" or "{3}."
        // format: [ornament half] { [ident] } [ornament half]

        let spl = str.split(['{', '}']).collect::<Vec<&str>>();
        if let [orna_l, ident, orna_r] = spl[0..3] {
            let ornament: String = format!("{}{{}}{}", orna_l, orna_r);

            Ok(Label::new(ident.to_string(), ornament)?)
        } else {
            Err(())
        }

    }

    fn compile(&self) -> String {
        self.ornament.fmt(&self.ident)
    }
}

pub struct Segment {
    eid: Label,
    content: Either<Vec<Segment>, String>, // assume (a)...(z) then 1. to $LEN., bound by italic
}

impl Segment {
    fn compile(&self) -> String {
        let eid = &self.eid.compile();

        match &self.content {
            Left(segs) => {
                let con = segs.iter()
                    .map(Segment::compile)
                    .collect::<Vec<String>>()
                    .join("\n");

                format!("\\item[{}]\n\\begin{{enumerate}}{}\\end{{enumerate}}\n\\nq", eid, con)
            },
            Right(con) => format!("\\item[{}]\n{}\n\\nq", eid, con)
        }
    }
}

pub struct FmtStr { // <-- called FmtString? FmtStr? temporarily only accepts one anchor b/c format!() exists.
    orna_l: String,
    orna_h: String
}

impl FmtStr {
    pub fn new(left: &str, right: &str) -> FmtStr {
        FmtStr { orna_l: left.to_string(), orna_h: right.to_string() }
    }

    pub fn from(fmt_str: &str) -> Result<FmtStr, ()> {
        if fmt_str.contains(FMT_ANCHOR) {
            let (orna_l, orna_h) = fmt_str.split_once(FMT_ANCHOR).unwrap();
            Ok(FmtStr::new(orna_l, orna_h))
        } else {
            Err(())
        }
    }

    pub fn only_fmt(fmt_str: &str, anchor: &dyn ToString) -> Result<String, ()> { // <-- **NEW** this is a new paradigm I'm designing to signify concise (but expensive) make-and-toss operations... OR shortcutting a single-time operation (like a fuse).
        let fmstr = FmtStr::from(fmt_str);
        fmstr.and_then(|fs| Ok(fs.fmt(anchor)))
    }

    pub fn fmt(&self, anchor: &dyn ToString) -> String {
        let mut res = String::from(&self.orna_l);
        res.push_str(&anchor.to_string());
        res.push_str(&self.orna_h);

        res
    }

    pub fn len(&self) -> usize {
        self.orna_l.len() + self.orna_h.len()
    }

    pub fn raw(&self) -> String {
        let mut res = String::from(&self.orna_l);
        res.push_str(FMT_ANCHOR);
        res.push_str(&self.orna_h);

        res
    }
}

impl MarkdownDoc {
    pub fn new(path: &str) -> Self {
        let (file, title) = (File::open(path).expect("Could not read file"), path.split('.').next().expect("File format bad").to_string());
        let content = BufReader::new(file).lines()
            .filter_map(|l| l.ok().and_then(|s| Some(s.trim().to_string())))
            .collect::<Vec<String>>();

        let pr_prep = Promise::only_wish(String::from("Preprocessing"));

        let mut content = preprocess_content(content)
            .into_iter()
            .peekable();

        pr_prep.fulfill();

        // Note on parsing decls... strips all $ — may be problematic for decl macros that use $$, but obsitex theoretically shouldn't permit it.


        // Take first (and only) document in YAML db.
        let pr_decls = Promise::only_wish(String::from("Injecting decls"));

        let mut doc = open_db();
        let cold_decls = doc["decls"].as_mut_vec().expect("Bad decls array"); // TODO fill hole of expectation sadness

        let decl_ids: Vec<String> = cold_decls.iter().map(|d| {
                d.as_hash().expect("Bad decls YAML")
                    .get(&Yaml::String("id".to_string()))
                    .map(|s| s.as_str().unwrap().to_string())
                    .unwrap()
            }).collect();

        // >NEW< change since a9d665b!
        // Making local decl parsing more forgiving by simply skipping all non-decl content.
        // This is also great for leaving some space for quick notes and things that will not be processed! Win-win!~
        let mut hot_decls = {
            let mut decls: Vec<String> = Vec::new();
            let (re_decl, re_heading) = (Regex::new(REGEX_DECL_VALID).unwrap(), Regex::new(REGEX_SEG_D1).unwrap());

            while let Some(line) = content.next_if(|l| !re_heading.is_match(l).unwrap()) {
                let mod_line = line.replace("$", "");
                if re_decl.is_match(&mod_line).unwrap() {
                    decls.push(mod_line)
                }
            }

            decls
        };

        let re_id = Regex::new(REGEX_DECL_ID).unwrap(); // TODO temp may be better to refactor decl2yaml as decomp_decl and decl2yaml using decomp tuple
        let db_cands: Vec<&String> = hot_decls.iter()
            .filter(|&d| {
                let caps = re_id.captures(d).unwrap().unwrap();
                !decl_ids.contains(&caps["id"].to_string())
            })
            .collect();
        if !db_cands.is_empty() && query(&format!("{} new decls found, add to db? (y/n)", db_cands.len())) == "y" { // <-- note! contingent on short-circuit eval of boolean.
            // let mut dump = String::new(); <-- TODO save mem by reusing same variables, must fix mut rules
            // let mut emitter = YamlEmitter::new(&mut dump);

            for cand in db_cands {
                match decl2yaml(&cand) {
                    Ok(yaml) => {
                        cold_decls.push(yaml);
                        println!("(✔) decl '{}' written", &cand);
                    },
                    Err(msg) => {
                        eprintln!("(X) decl '{}' not written, {}", &cand, msg);
                    }
                }
            }

            write_db(&doc); // <-- write hot decls to db
            hot_decls.clear();                                                            // <-- clear hot decls as already written to database
        }

        pr_decls.fulfill();

        // Parse segments. Depth of 2 for now.
        let pr_segs = Promise::only_wish(String::from("Parsing segments"));

        let mut segs: Vec<Segment> = Vec::new();
        //let (mut eid1, mut eid2) = (1, 'a');
        let (re1, re2, re0) = (Regex::new(REGEX_SEG_D1).unwrap(), Regex::new(REGEX_SEG_D2).unwrap(), Regex::new(REGEX_SEG_ANY).unwrap());

        while let Some(_) = content.peek() {
            let seg = {
                while let Some(_) = content.next_if(|l| !re1.is_match(l).unwrap()) {} // <-- jump until (before) seg depth=1 tag
                let eid1 = Label::from(format!("{{{}}}.", consume_eid(&mut content, &re1).unwrap()));

                // Check if subsegs are present... (a), (b), etc etc
                if re2.is_match(&content.peek().unwrap()).unwrap() {
                    let mut subsegs: Vec<Segment> = Vec::new();

                    while content.peek().is_some_and(|c| !re1.is_match(c).unwrap()) { // <-- must check for EOF!
                        let eid2 = Label::from(format!("({{{}}})", consume_eid(&mut content, &re2).unwrap()));
                        subsegs.push(consume_segment(&mut content, &re0, eid2.unwrap()));
                      //  content.next_if(|l| !re1.is_match(l));
                    }

                    Segment { eid: eid1.unwrap(), content: Left(subsegs) }
                } else {
                    consume_segment(&mut content, &re1, eid1.unwrap())
                }
            };

            segs.push(seg);
        }

        pr_segs.fulfill();

        // TODO image cache
        let cache = None;


        Self { title, decls: hot_decls, segs, cache }
    }
    pub fn compile(&self) -> TeXContent {
        let pr = Promise::only_wish(String::from("Compiling"));

        let doc = open_db();

        let decls = {
            let mut hot = parse_decls(&doc["decls"]);// <-- ...forgive my weird naming it's 00:14 lol
            let cold = &self.decls.join("\n");
            hot.push_str(cold);
            hot
        };
        let statics = parse_statics(&doc["statics"]);

        let mut template = fs::read_to_string(PATH_TEMPLATE).expect("Could not read template");
        let content = self.segs.iter()
            .map(Segment::compile)
            .collect::<Vec<String>>()
            .join("\n");
        let time = {
            let now = Local::now();
            format!("{} {}, {}", monthize(now.month() as u8), ordinize(now.day() as u8), now.year())
        };

        template = template.replace("%VERSION", VERSION_NUM);
        template = template.replace("%BRANCH", VERSION_BRANCH);

        template = template.replace("%STATICS", &statics);
        template = template.replace("%DECLS", &decls);
        template = template.replace("%TITLE", &self.title);
        template = template.replace("%CLASS", CLASS_DEFAULT);
        template = template.replace("%META", META_DEFAULT);
        template = template.replace("%AUTHOR", AUTHOR_DEFAULT);
        template = template.replace("%DATE", &time);
        template = template.replace("%CONTENT", &content);

        pr.fulfill();

        TeXContent::from(template)
    }
}

fn ordinize(ordinal: u8) -> String {
    let fmtr = match ordinal {
        i if i % 10 == 1 => "st",
        i if i % 10 == 2 => "nd",
        i if i % 10 == 3 => "rd",
        _ => "th",
    };

    format!("{}{}", ordinal, fmtr)
}

fn monthize(month: u8) -> String {
    match month {
        1 => "January".to_string(),
        2 => "February".to_string(),
        3 => "March".to_string(),
        4 => "April".to_string(),
        5 => "May".to_string(),
        6 => "June".to_string(),
        7 => "July".to_string(),
        8 => "August".to_string(),
        9 => "September".to_string(),
        10 => "October".to_string(),
        11 => "November".to_string(),
        12 => "December".to_string(),
        _ => unreachable!()
    }
}

fn capitalize(word: &str) -> String {
    let mut new = String::from(word);

    if word.is_empty() {
        // SAFETY: already checked so string must be non-empty!
        unsafe {
            let bytes = new.as_bytes_mut();
            bytes[0] += 32;
        }
    }

    new
}

fn parse_statics(yamls: &Yaml) -> String {
    let statics = yamls.as_vec().expect("Bad statics YAML format");
    statics.iter()
        .map(|s| s.as_str().unwrap().to_string())
        .collect::<Vec<String>>()
        .join("\n")
}

fn parse_decls(yamls: &Yaml) -> String {
    // - entry:
    //     id: ".."
    //     macro: ".."
    //     param: #
    // etc etc

    let entries = yamls.as_vec().expect("Bad decls YAML format");
    let mut decls = String::new();

    for entry in entries {
        if let Yaml::Hash(hash) = entry {
            let id = hash.get(&Yaml::String("id".to_string()))
                .and_then(Yaml::as_str)
                .unwrap_or("ERR");

            let mac = hash.get(&Yaml::String("macro".to_string()))
                .and_then(Yaml::as_str)
                .unwrap_or("ERR");

            let pc = hash.get(&Yaml::String("pc".to_string()))
                .and_then(Yaml::as_i64)
                .unwrap_or(0);

            let decl = if pc == 0 {
                format!("\\newcommand{{\\{}}}{{{}}}\n", id, mac)
            } else {
                format!("\\newcommand{{\\{}}}[{}]{{{}}}\n", id, pc, mac)
            };

            decls.push_str(&decl);
        }
    }

    decls
}

/// Preprocesses (preferably neatened) AMD (Assignment Markdown) content, returning for chaining.
///
/// "Neatened" refers to a prepared iterator that has done all needed file-wise formatting, such as trimming lines of dangling spaces
/// or subbing/stripping disallowed characters. Preprocessing instead performs line-wise formatting, parsed substitution, and the like.
///
/// Note that this purposefully is not optimized as performance not critical for compilation; you can write
/// the output to a separate designated "object" file if you want (e.g. .lho)
pub fn preprocess_content(mut content: Vec<String>) -> Vec<String> {
    // === Trim newlines (>=2 -> 1 \n) ===
    //
    // Old attempt...
    // let trimees = content.windows(2)
    //     .into_iter()
    //     .enumerate()
    //     .filter(|(_,[w0, w1, ..])| w0.is_empty() && w1.is_empty())
    //     .collect::<Vec<(usize, _, _)>>();
    //
    // content.retain(...);
    //
    content.dedup_by(|a, b| a.is_empty() && b.is_empty()); // <-- .o. wowz, turns out this already exists and saves so much time! :D

    // === Parse directives ===
    //
    // Valid ones are:
    // - &IGNORE_DECLS              ... slight speed-up if you know decls are all added
    // - &TRIM_COMMS                ... removes all %%comments%%)
    // - &DEFINE([ident], [value])  ... pre-compilation replaces all values (C-like)
    // - &INCLUDE([lhi])            ... fetches and parses the stored .lhi file
    //
    // Directive should be declared at the top of the file wrapped with separate-line %%...%%, though
    // ultimately the preprocessor just looks for the start and end %% to process so can one-line if needed.
    // You should not do separate %%...%% lines however as that will simply not process the later directives!
    //
    // e.g.
    // %%
    // &IGNORE_DECLS
    // &TRIM_COMMS
    // %%
    //
    // Note that the directive indicator may occur either on first line or second line (rec. for Obsidian)
    //

    // directives must live in the first and commented section, however not necessarily true that they are directives unless prefixed by &.
    // so you can still put a top comment to your file w/out being parsed! this is really just a shortcut to avoid scanning the entire doc
    //
    // ...note that `is_some_and(|[l1, l2, ..]| l1.contains("%%") || l2.contains("%%"))` feels plausible but the compiler
    //    cannot guarantee length of arrays (even if it's [N; 2]!) so refutable closure pattern.
    if content.get(0..=1).is_some_and(|ls| ls[0].contains("%%") || ls[1].contains("%%")) {
        let mut lines = content.iter();
        let mut directives = Vec::<PreprocessorDirective>::new();

        while let Some(line) = lines.nth(0) && !line.contains("%%") {
            if let Ok(dir) = PreprocessorDirective::from(line.trim()) {
                directives.push(dir);
            }
        }

        PreprocessorDirective::preprocess(&directives, &mut content);
    }

    content
}

pub fn send_to_overleaf(tex: TeXContent) -> Result<URL, FromUtf8Error> {
    // Encode into base64 (adapt from https://mcyoung.xyz/2023/11/27/simd-base64/#ascii-to-sextet)
    let tex_b64 = str2base64::<BASE64_VECTOR_SIZE>(&tex);

    // Parse into URL
    tex_b64.and_then(|t| Ok(FmtStr::only_fmt(OVERLEAF_URL, &t).unwrap()))
}

// Note that statics are only declarable in .lhi and some add'l assumptions are made (strip spacing, immediately add all new, etc).
// ...hence why this is not broadened to work for local scan.
pub fn scan_lhi(lhi: &File) {
    let mut buf = BufReader::new(lhi)
        .lines()
        .filter(|l| l.is_ok()) // <-- errs if invalid UTF-8. Also a neat idea, what if you could do "l.is_ok_and(!str::is_empty)"?
        .map(|l| l.unwrap().trim().to_string())
        .filter(|l| !l.is_empty());

    let (mut db_decls, mut db_statics) = {
        let mut doc = open_db();
        let hash = doc.as_mut_hash().unwrap();
        (hash.remove(&to_yaml_str("decls")).unwrap().into_vec().unwrap(), hash.remove(&to_yaml_str("statics")).unwrap().into_vec().unwrap())
    };
    let re_decl = Regex::new(REGEX_DECL_VALID).unwrap();
    let (mut num_decl_new, mut num_decl_rep, mut num_static) = (0usize, 0usize, 0usize);

    while let Some(line) = buf.next() {
        match line {
            // .lhi comment
            l if l.starts_with("##") => {},

            // .lhi decl; replaces if decl ID exists
            l if re_decl.is_match(&line).unwrap() => { // was considering either "_: Ok(id) @ re_decl.captures.name("id")" or "l if let id = re_decl.captures.name("id")" but unfortunately former is not supported and latter is experimental :(
                let caps = re_decl.captures(&l).unwrap().unwrap();
                let id = &caps["id"];
                let decl = assemble_decl(&caps);

                if let Some(old_i) = db_decls.iter().position(|d| d.as_hash().unwrap().get(&Yaml::String("id".to_string())).and_then(Yaml::as_str).unwrap() == id) {
                    num_decl_rep += 1;
                    db_decls.remove(old_i);
                    db_decls.insert(old_i, decl);
                } else {
                    num_decl_new += 1;
                    db_decls.push(decl);
                }
            },

            // .lhi static
            _ => {
                let stat = Yaml::String(line.to_string());

                if !db_statics.contains(&stat) {
                    num_static += 1;
                    db_statics.push(stat);
                }
            }
        }
    }

    let doc = {
        let mut hash = yaml::Hash::new();
        hash.insert(Yaml::String("decls".to_string()), Yaml::Array(db_decls));
        hash.insert(Yaml::String("statics".to_string()), Yaml::Array(db_statics));
        Yaml::Hash(hash)
    };

    write_db(&doc);

    println!("⊛ {} (+ {} replaced) decls, {} statics", num_decl_new, num_decl_rep, num_static);
}

fn decl2yaml(decl: &str) -> Result<Yaml, String> {
    // decl format is "\newcommand{\$ID}{$MACRO}" or "\newcommand{\$ID}[$PC]{$MACRO}}"
    let (re_valid, re_invalid) = (Regex::new(REGEX_DECL_VALID).unwrap(), Regex::new(REGEX_DECL_INVALID).unwrap());
    let (caps_valid, caps_invalid) = (re_valid.captures(decl).unwrap(), re_invalid.captures(decl).unwrap());

    match (caps_valid, caps_invalid) {
        (Some(caps), _) if caps.len() == 5 => { // <-- note that this is (1) full capture, (1) [$ID] opt group, (3) needed values.
            Ok(assemble_decl(&caps))
        },

        (Some(caps_v), Some(caps_i)) if caps_v.len() < caps_i.len() => {
            Err(String::from("malformed decl!"))
        },

        _ => {
            Err(String::new())
        }
    }
}

fn query(msg: &str) -> String {
    print!("{}", format!("{} ... ", msg));
    let _ = stdout().flush();

    let mut bfr = String::new();
    stdin().read_line(&mut bfr).expect("Bad user input");
    bfr.trim().to_string()
}

/// Consumes a segment; cannot guarantee that immediate next token contains EID so must manually pass EID.
fn consume_segment<I: Iterator<Item = String>>(content: &mut Peekable<I>, delim: &Regex, eid: Label) -> Segment {
    let mut body = String::new();
    let re_qq = Regex::new(REGEX_USES_QQ).unwrap();

    //let eid = regextract(delim, &content.next().unwrap(), "eid").unwrap();

    while let Some(line) = content.next_if(|l| !delim.is_match(l).unwrap()) {
        //has_final &= re_final.is_match(&line).unwrap(); // <-- tried to make a Oncelet, but turns out bit-AND is just that.

        let nq = regextract(&re_qq, &line, "nq").unwrap_or(String::new());
        let is_qq = nq.len() < line.len();

        let append = match &line {
            l if l.is_empty() => {
                String::from("\\\\\n")
            },

            l if l.eq(LINE_BREAK) => {
                String::from("\\sqe\n")
            }

            l if is_qq => {
                format!("\\\\\n\n{}", &l).to_string()
            },

            l => {
                format!("\\\\\n{}", &l).to_string()
            }
        };

        body.push_str(&append);
    }

    Segment { eid, content: Right(body) }
}

// Consume EID from the immediate following token. May require other operations in future hence separation.
fn consume_eid<I: Iterator<Item = String>>(content: &mut I, re: &Regex) -> Option<String> {
    regextract(re, &content.next().unwrap(), "eid")
}

fn assemble_decl(caps: &Captures) -> Yaml { // <-- I don't think this is designed well so maybe fix!! ouo
    let (id, mac, pc) = (&caps["id"], &caps["macro"], &caps.name("pc"));
    let mut hash = yaml::Hash::new();
    hash.insert(Yaml::String("id".to_string()), Yaml::String(id.to_string()));
    hash.insert(Yaml::String("macro".to_string()), Yaml::String(mac.to_string()));
    hash.insert(Yaml::String("pc".to_string()), Yaml::Integer(pc.and_then(|c| Some(c.as_str().parse::<i64>().unwrap())).unwrap_or(0)));
    Yaml::Hash(hash)
}

fn regextract(re: &Regex, haystack: &str, name: &str) -> Option<String> {
    let caps = re.captures(haystack).unwrap();
    caps.and_then(|c| Some(c[name].to_string()))
}

fn regextract_n(re: &Regex, haystack: &str, names: &[&str]) -> Vec<Option<String>> {
    if let Some(caps) = re.captures(haystack).unwrap() {
        Vec::from(names)
            .iter()
            .map(|&n| caps.name(n).and_then(|c| Some(c.as_str().to_string())))
            .collect()
    } else {
        vec![None; names.len()]
    }
}

/// This only works with regex with one (1) named capture group. Also naive implem as groups could already be named numerically (e.g. pat1 -> pat11).
fn regmerge(re1: &Regex, re2: &Regex) -> Regex {
    let meta_re = Regex::new(REGEX_META_NCAP).unwrap();
    let (mut str1, mut str2) = (re1.to_string(), re2.to_string());
    let (caps1, caps2) = (meta_re.captures(&str1).unwrap(), meta_re.captures(&str2).unwrap());
    let symcheck = {
        let (nc1, nc2) = (caps1.and_then(|c| Some(c.name("ncap").unwrap().as_str().to_string())), caps2.and_then(|c| Some(c.name("ncap").unwrap().as_str().to_string())));
        nc1.and_then(|c1|
            if nc2.is_some_and(|c2| c1 == c2) {
                Some(c1)
            } else {
                None
            }
        )
    };

    if let Some(ncap) = symcheck { // <-- if both captured ncaps have same identifier...
        str1 = str1.replace(&ncap, &format!("{}1", ncap));
        str2 = str2.replace(&ncap, &format!("{}2", ncap));
    }

    Regex::new(&format!(r"({})|({})", str1, str2)).unwrap()
}

//fn load_db<'d>() -> (&'d mut Array, &'d mut Array, BufWriter<File>) {

fn open_db() -> Yaml {
    let doc = {
        let raw = fs::read_to_string(PATH_DB).expect("Could not read decls YAML");
        YamlLoader::load_from_str(&raw).expect("Could not parse YAML")
    };
    doc.into_iter().next().unwrap_or(Yaml::Array(vec![]))
}

fn write_db(doc: &Yaml) {
    let mut db = OpenOptions::new()
        .write(true)
        .append(false)
        .open(PATH_DB)
        .unwrap();
    let mut dump = String::new();
    let mut emitter = YamlEmitter::new(&mut dump);
    emitter.dump(doc).unwrap();

    db.write_all(dump.as_bytes()).expect("Could not write to decl DB");
}

fn to_yaml_str(str: &str) -> Yaml {
    Yaml::String(str.to_string())
}

/// Send contents to clipboard.
pub fn to_clipboard(contents: &str) {
    let mut pbcopy = Command::new("pbcopy")
        .stdin(Stdio::piped())
        .spawn().unwrap();

    pbcopy.stdin.as_mut().unwrap().write_all(contents.as_bytes()).unwrap();
    pbcopy.wait().unwrap();
}

pub fn str_count(haystack: &str, needle: &str) -> usize {
    haystack.match_indices(needle).count()
}

/// "Uproot" piece in string if present and apply ornaments in-place.
/// The format string must contain only one instance of the placeholder string ({}).
///
/// # Caveats
/// This is not 100% fmtstr-compliant as "{{}}" will not be recognized as
/// escaping into "{}". This is intentional.
pub fn uproot(haystack: &mut String, fmtstr: &str, needle: &str) {
    assert_eq!(str_count(&fmtstr, "{}"), 1, "Format string must include only one placeholder!");

    if let Some((start, end)) = haystack.match_indices(needle).next().and_then(|(i,item)| Some((i, i + item.len()))) {
        let (orna_s, orna_e) = {
            let mut ornaments = fmtstr.split("{}");
            (ornaments.next().unwrap_or(""), ornaments.next().unwrap_or(""))
        };

        haystack.insert_str(start-1, orna_s);
        haystack.insert_str(end, orna_e);
    }
}

/// "Uproot" piece in string if present and apply ornaments in-place. <-- unfort a proc macro is needed to modify variables? (https://stackoverflow.com/questions/71812185/is-there-a-way-to-make-a-macro-replace-things-in-strings)
// macro_rules! uproot {
//     ($haystack:expr, $fmt:expr, $needle:expr) => {{
//         $haystack = $haystack.as_mut_str().replace(format!($fmt, $needle));
//     }};
// }


/// Takes a segment out of a string, pre-allocates size and appends modifications, puts back.
pub fn segpend<R: RangeBounds<usize> + Clone + SliceIndex<str, Output=str>>(str: &mut String, seg: R, append: &FmtStr) {
    // Extract and prepare carrier string
    str.reserve_exact(append.len());
    let pati = str.get(seg.clone()).unwrap();
    str.replace_range(seg, &append.fmt(&pati));
}


/// Chunks string from tail and returns segment and index when regex match is found.
///
/// # Caveats
/// `re` must be a non-anchored single-match pattern, as chunk may have prefixed garbage chars.
pub fn segtil(str: &str, re: &Regex, chunk_by: usize) -> (String, usize) {
    todo!();
}

// pub fn invert_range<T: ?Sized>(range: &dyn RangeBounds<T>, len: usize) -> dyn RangeBounds<T> { <-- was thinking about libbing range inversion but seems a bit pedantic
//
// }

/// Converts Markdown table to TeX, stripping formatting.
/// # Examples
/// This will convert:
/// |  *sample*  | *type* |  *fish*  |
/// | -------- | ---- | ------ |
/// | $\alpha$ | 1    | trout  |
/// | $\beta$  | S    | salmon |
///
/// into:
///
/// \begin{table}[]
/// \begin{tabular}{|l|l|l|}
/// \hline
/// sample   & type & fish   \\ \hline
/// $\alpha$ & 1    & trout  \\
/// $\beta$  & S    & salmon \\ \hline
/// \end{tabular}
/// \end{table}
///
/// # Caveats
/// While most Markdown tables should have precomputed spacing for visual clarity table2tex does not assume this.
/// May be less performant but more broadly compatible.
///
/// All Markdown formatting (pretty much only * and **) will be clobbered; current implementation will blindly
/// also remove any stray asterisks.
///
/// # Requires
/// Markdown table must not contain any non-asterisk formatting (e.g. HTML tags)
/// and must not be improperly sized (e.g. 3/3/2 table).

// pub fn table2tex(md: &str) -> String {
//     let mut tex = String::new();
//
//     let mut rows = md.lines().peekable();
//     let row_len = rows.peek().unwrap().len();
//
//     // ▼  extract Split<'_> (collection) of cells arranged by row  ▼
//     let row_cells = rows.map(|r| r
//         .split("|")
//         .filter(str::is_empty)
//         .map(|cell| cell.trim().replace("*", "")));
//
//     // ▼  find max/padding lens for each column (of cells)  ▼
//     row_cells.clone() // <-- "iter of rows of cells"
//         .map(|row| row.max_by(|x,y| x.len().cmp(y.len())).unwrap()) // <-- "
//
//
//
//
//
//     tex.push_str("\\begin{table}[]\n");
//     tex.push_str(&format!("\\begin{{tabular}}{{|{}}}\n", "l|".repeat(row_len)));
//     tex.push_str("\\hline\n");
//
//
//
//
//
//
//
//     tex.push_str("\\end{tabular}\n");
//     tex.push_str("\\end{table}\n");
//
//     tex
// }

/// Iterator adapter for 2D iter ("iter of iters") for row-column transposition.
///
/// [a d g]       [a b c]
/// [b e h]  -->  [d e f]
/// [c f i]       [g h i]
///
/// This means calling `transpose_iters` twice produces an idempotent 2D iter,
/// meaning mutating column operations may be performed without breaking data format.
///
/// # Caveats
/// Jagged/asymmetric 2D iters are not permitted for the sake of iter integrity; please see `transpose_iters_asymm`
/// for a solution that returns Option<T> in lieu of T but works.
// pub fn transpose_iters<I,J,T>(iters: I) -> I
// where
//     I: IntoIterator<Item=J>,
//     J: IntoIterator<Item=T>,
// {
//
// }

/// Iterator adapter equivalent of `transpose_iters` but for jagged/asymmetric 2D iters.
///
/// [a d]          [a b c]
/// [b]      -->   [d _ e]
/// [c e f]        [_ _ f]
///
/// # Caveats
/// The adapter must be called on pre-mapped optionals, please use `symmetrize_iters` to prepare.
/// This is to support idempotency.
pub fn transpose_iters_asymm<I,J,T>(iters: I) -> I // <-- TODO impl generics getting out of hand!!
where
    I: IntoIterator<Item=J>,
    J: IntoIterator<Item=Option<T>>,
{
    unimplemented!();
}

// Symmetrizes "iter-of-iters" or 2D iter by filling
// pub fn symmetrize_iters<I,J,K,T>(iters: I) -> impl IntoIterator<Item=K>
// where
//     I: IntoIterator<Item=J>,
//     J: IntoIterator<Item=T>,
//     K: IntoIterator<Item=Option<T>>,
// {
//     unimplemented!();
// }


/// Directly adapted from "Writing SIMD Algorithm From Scratch" post.
///
/// Creates a SIMD mask for all elements within the given inclusive range specified
/// by `lo` and `hi`.
fn mask_range<const U: usize>(bytes: &Simd<u8, U>, lo: u8, hi: u8) -> Mask<i8, U>
where LaneCount<U>: SupportedLaneCount {
    bytes.simd_ge(Simd::splat(lo)) & bytes.simd_le(Simd::splat(hi))
}

/// Directly adapted from "Writing SIMD Algorithm From Scratch" post.
///
/// Selectively splats a SIMD vector if masked, zeroes if not.
fn masked_splat<const U: usize>(mask: &Mask<i8, U>, aug: i8) -> Simd<i8, U>
where LaneCount<U>: SupportedLaneCount {
    mask.select(Simd::splat(aug), Simd::splat(0))
}


/// Converts a string to Base64, adding '=' padding if necessary for alignment.
pub fn str2base64<const N: usize>(str: &str) -> Result<String, FromUtf8Error>
where LaneCount<N>: SupportedLaneCount {
    // CHALLENGE: make this branchless and hyper-optimize!! (but not micro-optimize?)
    // └————— tl;dr hot-cold loops for unaligned read from string to prepare u6 -> u8 for SIMD magic.
    //      └————— ...this is moreso for practicing SIMD/raw pointers rather than applicability (e.g. using a zeroed u8 Vec prolly compiles to faster anyway).

    // SAFETY: `str` is guaranteed to be valid UTF-8 (even if variable-length, base64 only takes 6b anyway) N x 8 bits.
    unsafe {
        // ❶ Pad the u6s to u8s! Unaligned-read (`mov rax, qword ptr [rdx + rax]`!!!) through entire string
        // @adapts https://lukefleed.xyz/posts/compressed-fixedvec/#faster-reads-unaligned-access
        let (mut ptr_u8, mut len, _): (*mut u8, usize, _) = str.to_string().into_raw_parts();
        len = (len * 8) / 6;

        let layout = Layout::from_size_align_unchecked(len, 8);
        let ptr_ps = alloc_zeroed(layout);

        let mut ptr_u6: *mut u8 = ptr_ps.clone();

        // `len` is num of u6 in str... then div by 4 for num of u24, remainder is removed 2 bits >:)
        let memch: *mut u8 = 0u32 as *mut u8;
        for _ in 0..(len >> 2) {
            ptr::copy_nonoverlapping(ptr_u8, memch, 3);

            for mi in (0..16).step_by(4) { // <-- mi = mask index
                ptr_u6.write(*memch & (0b0011_1111 << mi));
                ptr_u6 = ptr_u6.add(1);
            }
        }

        // offset           =   2 bits         4 bits       6 bits       (8 bits)      0 bits
        // *b2              = [111111]00 -> 1111]00 00 -> 11]00 0000 -> 00000000 -> [111111]00
        // *b1              =  000000 00 -> 0000 00[11 -> 00 00[1111 -> 00111111 ->  000000 00
        // ^b2 & m (strict) =  000000 00 -> 0000 00 11 -> 00 00 1111 -> 00111111 ->  000000 00
        // ^b2 & m (lazy)   =  111111 00 -> 1111 00 11 -> 11 00 1111 -> 00111111 ->  111111 00
        // ^(^bm & m (l))   =  000000 11 -> 0000 11 00 -> 00 11 0000 -> 11000000 ->  000000 11

        let mask_u6 = 0b11111100; // <-- ver. b2, complement for ver. b1
        let mask_cc = 0b00000011; // <-- complement AND mask (lazy) (complemented again)
        let (mut b1, mut b2) = (0u8, 0u8);

        for mi in 0..(len & 0b11) { // <-- guaranteed to be 0-3 loops
            b2 = ptr_u8.read();
            ptr_u6.write((b2 & mask_u6 << mi) >> mi & (b1 & !(mask_u6 << mi) & !(mask_cc << mi)) << (8 - mi));

            ptr_u8 = ptr_u8.add(1);
            ptr_u6 = ptr_u6.add(1);
            b1 = b2;
        }

        // reset pointer position...
        ptr_u6 = ptr_ps.clone();

        // ❷ Unroll and jam loops for base64 conversion! Hot loop is `chunks_exact` filling full SIMD registers, cold loop is part of a register.
        // @adapts https://mcyoung.xyz/2023/11/27/simd-base64/#simd-hash-table (technique, `in_range`)
        //
        // raws           hex            maps      ascii
        // 0..=25  ->   0x0..=0x19  ->   A-Z   -> +65
        // 26..=51 ->   0x1A..=0x33 ->   a-z   -> +97
        // 52..=61 ->   0x34..=0x3D ->   0-9   -> +48
        // 62      ->   0x3E        ->    +    -> +43
        // 63      ->   0x3F        ->    /    -> +47
        //
        // As far as I can tell there is no easy hashing function like w/ decoding (unique high nibbles)
        // so the next-best is doing branchless mask magic.
        //
        // Use `simd_le` and `simd_ge` to make masks to extract ranges, then do
        // masked splats augmenting offsets onto the mask values.
        // Then just bitwise OR all of the augments together and add the entire
        // offset vector to the chunk :D
        //
        // Note that this augment vector is dependent on the chunk values, so we can't
        // pre-generate it before trying any data or anything, sadly.
        //
        // ...technically may be more intuitive to map per-byte rather than writing then reading? bah lol

        let mut chunk: [u8; N] = [0; N];
        let ptr_chunk = chunk.as_mut_ptr();
        //let (chunks_n, chunks_rem) = (len / N, len % N);

        for _ in 0..=(len / N) { // <-- note that this will hit chunks_n as well as chunks_rem! this does mean chunks_rem will have some garbage, but string assembly trims that garbage off.
            ptr::copy_nonoverlapping(ptr_u6, ptr_chunk, N);

            let chu: Simd<u8, N> = chunk.into(); // i need better names lol

            let mask_upper = mask_range(&chu, 0, 25);
            let mask_lower = mask_range(&chu, 26, 51);
            let mask_numeric = mask_range(&chu, 52,61);
            let mask_pluses = mask_range(&chu, 62,62);
            let mask_slashes = mask_range(&chu, 63,63);

            let hun = masked_splat(&mask_upper, b'A' as i8) |
                masked_splat(&mask_lower, (b'a' - 26) as i8) |
                masked_splat(&mask_numeric, (52 - b'0') as i8) |
                masked_splat(&mask_pluses, (62 - b'+') as i8) |
                masked_splat(&mask_slashes, (63 - b'/') as i8);

            let ptr_hun = hun.cast::<u8>()[..].as_ptr();

            ptr::copy_nonoverlapping(ptr_hun, ptr_u6, N);
            ptr_u6 = ptr_u6.add(N);
        }

        String::from_utf8(Vec::from_raw_parts(ptr_ps, len, len))
    }
}

// /// Splits u8 into two halves, inspired by [Vec::split_at_mut](std::vec::Vec::split_at_mut).
// #[inline(always)]
// pub fn split_u8(num: u8, mid: u8) -> (u8, u8) {
//
// }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn genrc_decl_parsing() {
        let (re1, re2) = (Regex::new(REGEX_DECL_VALID).unwrap(), Regex::new(REGEX_DECL_INVALID).unwrap());
        let yaml1 = r"\newcommand{\comm}[1]{\;\text{#1}\;}";
        let yaml2 = r"\newcommand{\zq}{\phantom{}^2}";

        let caps = re1.captures(yaml2).unwrap().unwrap();
        let len = caps.len();

        for i in 0..len {
            let cap = &caps[i];
            println!("{}", cap);
        }

       // let decl1 = decl2yaml(yaml1);
        let decl2 = decl2yaml(yaml2);

        println!("{}", decl2.is_ok())
    }

    #[test]
    fn genrc_regex() {
        let (re1, re2) = (Regex::new(REGEX_SEG_D1).unwrap(), Regex::new(REGEX_SEG_ANY).unwrap());
        assert!(re1.is_match("**1.**").unwrap());
        assert!(!re1.is_match("jiawejifajweifjaiwejf").unwrap());
        assert!(re2.is_match("*(a)*").unwrap());
        assert!(re2.is_match("**1.**").unwrap());
        assert!(!re2.is_match("*(a)**").unwrap());
    }

}