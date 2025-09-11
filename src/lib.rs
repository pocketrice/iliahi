use std::fs;
use either::{Either, Left, Right};
use std::fs::{File, OpenOptions};
use std::io::{stdin, stdout, BufRead, BufReader, BufWriter, Write};

use std::iter::Peekable;
use std::ops::Deref;
use chrono::{Datelike, Local};
use regex::Regex;
use yaml_rust::{yaml, Yaml, YamlEmitter, YamlLoader};
use yaml_rust::yaml::Array;

type TeXContent = String;

static REGEX_SEG_D1: &str = r"\*\*.*\*\*";
static REGEX_SEG_D2: &str = r"\*.*\*";
static REGEX_DECL_VALID: &str = r"\\newcommand\{\\(?P<id>[a-z]+)}(\[(?P<pc>\d+)])?\{(?P<macro>.*)}";
static REGEX_DECL_INVALID: &str = r"\\newcommand\{\\(?P<id>.+)}(\[(?P<pc>.+)])?\{(?P<macro>.*)}";

static CLASS_DEFAULT: &str = "Math 3345";
static META_DEFAULT: &str = "MWF 1:50-2:45, Katz";
static AUTHOR_DEFAULT: &str = "Lucas Xie";
static PATH_DECLS: &str = "decls.yaml";
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

pub struct Segment {
    content: Either<Vec<Segment>, String>, // assume (a)...(z) then 1. to $LEN., bound by italic
}

impl Segment {
    fn compile(&self, mut eid: char) -> String {
        match &self.content {
            Left(segs) => {
                eid = char::from_u32(eid as u32 + ('a' as u32 - '1' as u32)).unwrap(); // calc next starting EID?? pedantic?
                let con = segs.iter().map(|s| {
                    // note: this is assuming depth of 2 (meaning subsegs guaranteed to not be Left(segs). May need to do some recursive magic here in regards to \begin{enum}...!
                    let comp = s.compile(eid);
                    eid = char::from_u32(eid as u32 + 1).unwrap(); // increment EID
                    comp
                }).collect::<Vec<String>>().join("\n");

                format!("\\item[{}.]\n\\begin{{enumerate}}{}\\end{{enumerate}}", eid, con)
            },
            Right(con) => format!("\\item[{}.]\n{}", eid, con)
        }
    }
}

impl MarkdownDoc {
    pub fn new(path: &str) -> Self {
        let (file, title) = (File::open(path).expect("Could not read file"), path.split('.').next().expect("File format bad").to_string());
        let mut content = BufReader::new(file).lines().map(|l| l.unwrap()).peekable();

        // Note on parsing decls... strips all $ — may be problematic for decl macros that use $$, but obsitex theoretically shouldn't permit it.


        // Take first (and only) document in YAML db.
        let doc = {
            let yaml = fs::read_to_string(PATH_DECLS).expect("Could not read file");
            YamlLoader::load_from_str(&yaml).expect("Could not parse YAML")
        }.into_iter().next().unwrap();
        let mut cold_decls = doc.into_vec().expect("Bad decls array"); // TODO fill hole of expectation sadness

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

        let db_cands: Vec<&String> = hot_decls.iter()
            .filter(|&d| !decl_ids.contains(d))
            .collect();
        if !db_cands.is_empty() && query("New decls found, add to db? (y/n)") == "y" { // <-- note! contingent on short-circuit eval of boolean.
            // let mut dump = String::new(); <-- TODO save mem by reusing same variables, must fix mut rules
            // let mut emitter = YamlEmitter::new(&mut dump);

            let mut decl_db: BufWriter<File> = {
                let file = OpenOptions::new()
                    .write(true)
                    .append(false)
                    .open(PATH_DECLS)
                    .unwrap();

                BufWriter::new(file)
            };

            for cand in db_cands {
                match decl2yaml(&cand) {
                    Ok(yaml) => {
                        cold_decls.push(yaml);
                    },
                    Err(msg) => {
                        eprintln!("decl '{}' not written... {}", &cand, msg);
                    }
                }
            }

            let mut dump = String::new();
            let mut emitter = YamlEmitter::new(&mut dump);
            emitter.dump(&Yaml::Array(cold_decls)).unwrap();

            decl_db.write_all(dump.as_bytes()).expect("Could not write to decl DB"); // <-- write hot decls to db
            hot_decls.clear();                                                            // <-- clear hot decls as already written to database
        }

        println!("\n\n");

        // Parse segments. Depth of 2 for now.
        let mut segs: Vec<Segment> = Vec::new();
        //let (mut eid1, mut eid2) = (1, 'a');
        let (reg1, reg2) = (Regex::new(REGEX_SEG_D1).unwrap(), Regex::new(REGEX_SEG_D2).unwrap());

        while let Some(_) = content.peek() {
            let seg = {
                while !reg1.is_match(&content.next().unwrap()) {}; // <-- jump until (after) seg depth=1 tag

                // Check if subsegs are present... (a), (b), etc etc
                if reg2.is_match(&content.next().unwrap()) {
                    //eid2 = 'a';
                    let mut subsegs: Vec<Segment> = Vec::new();

                    while content.peek().is_some() && !reg1.is_match(content.peek().unwrap()) { // <-- must check for EOF
                        subsegs.push(consume_segment(&mut content, &reg2));
                        content.next_if(|l| !reg1.is_match(l));
                    }

                    Segment { content: Left(subsegs) }
                } else {
                    consume_segment(&mut content, &reg1)
                }
            };

            segs.push(seg);
        }

        // TODO image cache
        let cache = None;


        Self { title, decls: hot_decls, segs, cache }
    }
    pub fn compile(&self) -> TeXContent {
        let yaml = fs::read_to_string(PATH_DECLS).expect("Could not read decls YAML");
        let decls = {
            let mut hot = parse_decls(&YamlLoader::load_from_str(&yaml).expect("Could not parse decls YAML")[0]); // <-- ...forgive my weird naming it's 00:14 lol
            let cold = &self.decls.join("\n");
            hot.push_str(cold);
            hot
        };

        let mut template = fs::read_to_string(PATH_TEMPLATE).expect("Could not read template");
        let content = self.segs.iter().map(|s| s.compile('1')).collect::<Vec<String>>().join("\n");
        let time = {
            let now = Local::now();
            format!("{} {}, {}", monthize(now.month() as u8), ordinize(now.day() as u8), now.year())
        };


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

fn decl2yaml(decl: &str) -> Result<Yaml, String> {
    // decl format is "\newcommand{\$ID}{$MACRO}" or "\newcommand{\$ID}[$PC]{$MACRO}}"
    let (re_valid, re_invalid) = (Regex::new(REGEX_DECL_VALID).unwrap(), Regex::new(REGEX_DECL_INVALID).unwrap());
    let (caps_valid, caps_invalid) = (re_valid.captures(decl), re_invalid.captures(decl));

    match (caps_valid, caps_invalid) {
        (Some(caps), _) if caps.len() == 5 => { // <-- note that this is (1) full capture, (1) [$ID] opt group, (3) needed values.
            let mut hash = yaml::Hash::new();
            hash.insert(Yaml::String("id".to_string()), Yaml::String(caps["id"].to_string()));
            hash.insert(Yaml::String("macro".to_string()), Yaml::String(caps["macro"].to_string()));
            hash.insert(Yaml::String("pc".to_string()), Yaml::Integer(caps.name("pc").and_then(|c| Some(c.as_str().parse::<i64>().unwrap())).unwrap_or(0)));
            Ok(Yaml::Hash(hash))
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

fn consume_segment<I: Iterator<Item = String>>(content: &mut Peekable<I>, delim: &Regex) -> Segment {
    let mut body = String::new();
    while let Some(line) = content.next_if(|l| !delim.is_match(l)) {
        body.push_str(&line);
    }

    Segment { content: Right(body) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decl() {
        let (re1, re2) = (Regex::new(REGEX_DECL_VALID).unwrap(), Regex::new(REGEX_DECL_INVALID).unwrap());
        let yaml1 = r"\newcommand{\comm}[1]{\;\text{#1}\;}";
        let yaml2 = r"\newcommand{\zq}{\phantom{}^2}";

        let caps = re1.captures(yaml2).unwrap();
        let len = caps.len();

        for i in 0..len {
            let cap = &caps[i];
            println!("{}", cap);
        }

       // let decl1 = decl2yaml(yaml1);
        let decl2 = decl2yaml(yaml2);

        println!("{}", decl2.is_ok())
    }
}
