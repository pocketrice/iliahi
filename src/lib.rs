use either::{Either, Left, Right};
use std::fs;
use std::fs::{File, OpenOptions};
use std::io::{stdin, stdout, BufRead, BufReader, Write};

use chrono::{Datelike, Local};
use fancy_regex::{Captures, Regex};
use std::iter::Peekable;
use std::process::{Command, Stdio};
use yaml_rust::{yaml, Yaml, YamlEmitter, YamlLoader};

type TeXContent = String;

static ORNAMENT_ANCHOR: &str = "{}";
static REGEX_META_NCAP: &str = r".*\(\?P<(?P<ncap>.+)>.*\).*"; // <-- note, this means only limited to one named capture group for regmerge!
static REGEX_SEG_D1: &str = r"\*\*(?P<eid>.+)\.\*\*";
static REGEX_SEG_D2: &str = r"\*\((?P<eid>.+)\)\*";
static REGEX_SEG_ANY: &str = r"^((\*)|(\*\*))(?(2)\(|)(?P<eid>[a-zA-Z0-9]+)(?(2)\)\*|\.\*\*)$"; // <-- requires use of fancy-regex;
static REGEX_DECL_VALID: &str = r"\\newcommand\{\\(?P<id>[a-z]+)}(\[(?P<pc>\d+)])?\{(?P<macro>.*)}";
static REGEX_DECL_INVALID: &str = r"\\newcommand\{\\(?P<id>.+)}(\[(?P<pc>.+)])?\{(?P<macro>.*)}";
static REGEX_DECL_ID: &str = r"\\newcommand\{\\(?P<id>[a-z]+)}(\[\d+])?\{.*}";

//static REGEX_EID_LAYERS: [&str; 3] = [r"(?P<eid>\d+\.", r"\((?P<eid>[a-z]+))", r"\((?P<eid>["]

// static REGEX_LHI_COMMENT: &str = r"^(\#\#).*"; <-- replaced with str::starts_with() for now but for semantics may want to replace with pattern match

static CLASS_DEFAULT: &str = "Math 3345";
static META_DEFAULT: &str = "MWF 1:50-2:45, Katz";
static AUTHOR_DEFAULT: &str = "Lucas Xie";
static PATH_DB: &str = "db.yaml";
static PATH_TEMPLATE: &str = "template.tex";
static NO_MATCH: &str = "";

// static EID_LAYERS: (char, char, char) = ('1', 'a', 'i') <-- TODO i increments by roman numeral instead...

pub struct MarkdownDoc {
    title: String,
    decls: Vec<String>,
    segs: Vec<Segment>, // assume (1)...($LEN), bound by bold TODO [Segment] should be more performant as on stack (esp. for arr of arr)
    cache: Option<u8> // TODO make this (Sized) byte array
}

// macro_rules! tex_decl { <-- relic of using technique of actually replacing placeholders in content... no need!
//
// }

pub struct Label { // <-- e.g. (1), ii., <hr>5</hr>
    ident: String,   // raw value; 1
    ornament: String // outside wrapper; ({}) TODO best to make ornament a ref?
}

impl Label {
    fn new(ident: String, ornament: String) -> Label {
        assert!(ornament.contains(ORNAMENT_ANCHOR) && !ornament.replacen(ORNAMENT_ANCHOR, "", 1).contains(ORNAMENT_ANCHOR), "Ornament must contain only one anchor");
        Label { ident, ornament }
    }

    fn from(str: String) -> Label {
        // note: the label string must distinguish ident and ornament by wrapping ident with {}.
        // e.g.: "({a})" or "{3}."
        // format: [ornament half] { [ident] } [ornament half]

        let spl = str.split(['{', '}']).collect::<Vec<&str>>();
        let ident: String = spl[1].to_string();
        let ornament: String = format!("{}{{}}{}", spl[0], spl[2]);

        Label { ident, ornament }
    }

    fn compile(&self) -> String {
        self.ornament.replace(ORNAMENT_ANCHOR, &self.ident)
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

                format!("\\item[{}]\n\\begin{{enumerate}}{}\\end{{enumerate}}\\sq\\sq", eid, con)
            },
            Right(con) => format!("\\item[{}]\n{}\\sq\\sq", eid, con)
        }
    }
}

impl MarkdownDoc {
    pub fn new(path: &str) -> Self {
        let (file, title) = (File::open(path).expect("Could not read file"), path.split('.').next().expect("File format bad").to_string());
        let mut content = BufReader::new(file)
                .lines()
                .map(|l| l.unwrap().trim().to_string())
                .peekable();



        // Note on parsing decls... strips all $ — may be problematic for decl macros that use $$, but obsitex theoretically shouldn't permit it.


        // Take first (and only) document in YAML db.
        let mut doc = open_db();
        let cold_decls = doc["decls"].as_mut_vec().expect("Bad decls array"); // TODO fill hole of expectation sadness

        let decl_ids: Vec<String> = cold_decls.iter().map(|d| {
                d.as_hash().expect("Bad decls YAML")
                    .get(&Yaml::String("id".to_string()))
                    .map(|s| s.as_str().unwrap().to_string())
                    .unwrap()
            }).collect();

        let mut hot_decls = {
            let mut decls: Vec<String> = Vec::new();

            while let Some(_) = content.next_if(|l| l.is_empty()) {}; // <-- skip initial blanks
            while let Some(decl) = content.next_if(|l| !l.is_empty()) { // <-- read until final blank
                decls.push(decl.replace("$", ""));
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

        println!("\n\n");

        // Parse segments. Depth of 2 for now.
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
                        subsegs.push(consume_segment(&mut content, &re0, eid2));
                      //  content.next_if(|l| !re1.is_match(l));
                    }

                    Segment { eid: eid1, content: Left(subsegs) }
                } else {
                    consume_segment(&mut content, &re1, eid1)
                }
            };

            segs.push(seg);
        }

        // TODO image cache
        let cache = None;


        Self { title, decls: hot_decls, segs, cache }
    }
    pub fn compile(&self) -> TeXContent {
        let mut doc = open_db();

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


        template = template.replace("%STATICS", &statics);
        template = template.replace("%DECLS", &decls);
        template = template.replace("%TITLE", &self.title);
        template = template.replace("%CLASS", CLASS_DEFAULT);
        template = template.replace("%META", META_DEFAULT);
        template = template.replace("%AUTHOR", AUTHOR_DEFAULT);
        template = template.replace("%DATE", &time);
        template = template.replace("%CONTENT", &content);

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
    unsafe {
        let bytes = new.as_bytes_mut();
        bytes[0] += 32;
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
    let mut has_final = false;
    //let eid = regextract(delim, &content.next().unwrap(), "eid").unwrap();

    while let Some(line) = content.next_if(|l| !delim.is_match(l).unwrap()) {
        if line.is_empty() {
            body.push_str("\\\\\n\n")
        } else {
            body.push_str(&line);
            body.push_str("\n");
        }
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

fn regextract(re: &Regex, haystack: &str, id: &str) -> Option<String> {
    let caps = re.captures(haystack).unwrap();
    caps.and_then(|c| Some(c[id].to_string()))
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decl() {
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
    fn regex() {
        let (re1, re2) = (Regex::new(REGEX_SEG_D1).unwrap(), Regex::new(REGEX_SEG_ANY).unwrap());
        assert!(re1.is_match("**1.**").unwrap());
        assert!(!re1.is_match("jiawejifajweifjaiwejf").unwrap());
        assert!(re2.is_match("*(a)*").unwrap());
        assert!(re2.is_match("**1.**").unwrap());
        assert!(!re2.is_match("*(a)**").unwrap());
    }
}