#![feature(portable_simd, vec_into_raw_parts, if_let_guard, pattern)]

use anyhow::Error;
use anyhow::{anyhow, bail};
use chrono::{Datelike, Local};
use either::{Either, Left, Right};
use fancy_regex::{Captures, Regex};
use map_macro::hash_map;
use std::alloc::{alloc_zeroed, Layout};
use std::collections::HashMap;
use std::fs;
use std::fs::{File, OpenOptions};
use std::io::{stdin, stdout, BufRead, BufReader, Read, Write};
use std::iter::Peekable;
use std::net::TcpStream;
use std::ops::RangeBounds;
use std::path::Path;
use std::process::{Command, Stdio};
use std::ptr;
use std::simd::prelude::{SimdInt, SimdPartialOrd};
use std::simd::{LaneCount, Mask, Simd, SupportedLaneCount};
use std::slice::SliceIndex;
use std::str::pattern::Pattern;
use std::str::FromStr;
use std::string::FromUtf8Error;
use std::time::{Duration, Instant};
use yaml_rust::{yaml, Yaml, YamlEmitter, YamlLoader};

type TeXContent = String;
type Fmtr<'a> = &'a str;


// changelog
// 0.1.x ... supports basic features (no content/db)
// 0.2.x ... decls rewrite to use db
// 0.3.x ... statics support to db, .lhi files
// 0.4.x ... preprocessor experimentation, migration to nightly
// 0.5.x ... preprocessor support, hyperoptim base64
// 0.6.x ... simple URL validation, export to overleaf finished
// 1.0.0 ... adapted from overleaf to pdflatex conversion
// 1.1.0 ... &CONDENSE (seg-local content) added, finalans/partans content
// 2.0.0 ... adapted from 'raw' to clap CLI usage, pdflatex binding

static USER_AGENT: &str = "iliahi TeX proxy";
static VERSION_NUM: &str = "2.0.0";
static VERSION_BRANCH: &str = "ALPHA";


pub static FMT_ANCHOR: &str = "{}";
static SEG_SENTINEL: &str = "*(S)*";
static REGEX_META_NCAP: &str = r".*\(\?P<(?P<ncap>.+)>.*\).*"; // <-- note, this means only limited to one named capture group for regmerge!
static REGEX_SEG_D1: &str = r"^\*\*(?P<eid>.+)\.\*\*( %.+%)?$";
static REGEX_SEG_D2: &str = r"^\*\((?P<eid>.+)\)\*( %.+%)?$";
static REGEX_SEG_ANY: &str = r"^((\*)|(\*\*))(?(2)\(|)(?P<eid>[a-zA-Z0-9]+)(?(2)\)\*|\.\*\*)( %.+%)?$"; // <-- requires use of fancy-regex;
static REGEX_DECL_VALID: &str = r"\\(renew|new|provide)command\{\\(?P<id>[a-z]+)}(\[(?P<pc>\d+)])?\{(?P<macro>.*)}";
static REGEX_DECL_INVALID: &str = r"\\(renew|new|provide)command\{\\(?P<id>.+)}(\[(?P<pc>.+)])?\{(?P<macro>.*)}";
static REGEX_DECL_ID: &str = r"\\(renew|new|provide)command\{\\(?P<id>[a-z]+)}(\[\d+])?\{.*}";
static REGEX_USES_FINAL: &str = r".*?((\\finalans\{.+\})|(##.+##)).*?";
static REGEX_USES_QQ: &str = r"((\\(q+|[;,>:]|(hspace)))*)(?<nq>.+)";
static REGEX_COMMS: &str = "%{2}.*?%{2}";
static REGEX_PREPROC_DEFINE: &str = r"^&DEFINE *\( *(?<ident>.+?) *, *(?<value>.*? *)\)$";
static REGEX_PREPROC_INCLUDE: &str = r"^&INCLUDE *\( *(?<ident>.+?)\.lhi *\)$";
static REGEX_PREPROC_CONDENSE: &str = r"^&CONDENSE *\( *(?<seg>[a-zA-Z0-9]+?) *(, *(?<subseg>[a-zA-Z0-9]+?))? *\)$";
static REGEX_URI: &str = r"(?<scheme>[a-zA-Z][a-zA-Z0-9+\-.]*):(?<authority>\/\/(?<host>([a-zA-Z0-9]+\.)*[a-zA-Z0-9]+)(:(?<port>[0-9]+))?)?(\/(?<path>([A-Za-z0-9:@!$&'()*+,;=]+)*))(\?(?<query>[0-9A-Za-z:@!$&'()*+,;=\-._~\/]+))?(\#(?<fragment>[0-9A-Za-z:@!$&'()*+,;=\-._~\/]+))?";
/// note this is a workaround for retrieving URI authority `dyn Identifier` replacing `URI`. This assumes the URI is already valid and is absolute (of type `URI`).
static REGEX_REQT_AUTH: &str = r".*(Host: (?<authority>([a-zA-Z0-9]+\.)*[a-zA-Z0-9]+(:[0-9]+)?).*)";
static REGEX_REL_URI: &str = r"\/(?<path>([A-Za-z0-9:@!$&'()*+,;=]+)*)(\?(?<query>[0-9A-Za-z:@!$&'()*+,;=\-._~\/]+))?(\#(?<fragment>[0-9A-Za-z:@!$&'()*+,;=\-._~\/]+))?";
static REGEX_HTTP_HEADER: &str = r"^[A-Za-z]+[A-Za-z-]*";
static REGEX_SEGDIRS: &str = r".*(?<sdc>%(?<segdirs>[a-zA-Z]*){}%)"; // <-- `sdc` encapsulates entire segdirs chunk (with ornaments), `segdirs` is purely the eponymous
static RERPL_PREPROC_FINALANS: &str = r"(?<left>.*)##(?<mid>.+)##(?<right>.*)"; // <-- "RERPL" denotes a regex replacer, it won't normally match the intended content (e.g. getting just the finalans part) as they're more or less scoped and inverted
static RERPL_PREPROC_PARTANS: &str = r"(?<left>.*)@@(?<mid>.+)@@(?<right>.*)";
static HTTP_VERSIONS: [f32; 5] = [0.9, 1.0, 1.1, 2.0, 3.0];
static HTTP_RW_TIMEOUT_SEC: u64 = 10;
static HTTP_RW_WAIT_MS: u64 = 5000;
static HTTP_RW_MAX_ATTEMPTS: usize = 3;
static HTTP_POST_BOUNDARY: &str = "S314mat-------p4g1!";
static HTTP_POST_NO_FILENAME: &str = "file";
static HTTP_PAYLOAD_MAX_SIZE: usize = 32768; // 32Kib

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
static SEG_D1: Fmtr = r"**{}.**";
static SEG_D2: Fmtr = r"*({})*";
static SEGDIR_FMT: Fmtr = r"%{}%";
static FINAL_FMT: Fmtr = r"\finalans{{}}";
static PROMISE_FMT: Fmtr = "{}... ";
static PROMISE_OK: &str = "OK";
static PROMISE_NG: &str = "NG";
static PROMISE_DEF_PRECISION: usize = 3;
static OVERLEAF_URL: Fmtr = "https://www.overleaf.com/docs?snip_uri={}";
static BASE64_VECTOR_SIZE: usize = 32; // <-- 2024 standard is AVX2 (256b) or SVE2 (128-1024b in 128b incr); using Assignments 1-9 avg=4620c, stdev=2085c. Using 1024b/128B would be most optimal but seems like 256b/32B is safer.

//static BASE64_VECTOR_OFFS: [i8; 5] = [b'A' as i8, (b'a' - 26) as i8, (52 - b'0') as i8, (62 - b'+') as i8, (63 - b'/') as i8]; // <-- add these to 6-bit value to receive the base64 representation!

// raws         maps      ascii
// 0..=25  ->   A-Z   -> +65
// 26..=51 ->   a-z   -> +97
// 52..=61 ->   0-9   -> +48
// 62      ->    +    -> +43
// 63      ->    /    -> +47

// static EID_LAYERS: (char, char, char) = ('1', 'a', 'i') <-- TODO i increments by roman numeral instead...

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

/// Generalized representation of an identifier, most commonly a URI.
/// What is needed is simply a way to resolve to absolute standalone identifier; already absolute identifiers
/// may simply return something akin to `self::compile`.
pub trait Identifier {
    fn resolve(&self, auri: Option<URI>) -> Result<String, Error>; // compile absolute
    fn compile(&self) -> String; // compile current (relative or absolute). the identifier should have already been verified, so no need for `Result<String, Error>`.
}

#[derive(Debug)]
pub struct URI {
    scheme: String,          //     https://         ...
    host: Option<String>,    // ... en.wikipedia.org ...
    port: Option<u16>,       // ... :443             ...
    path: String,            // ... /wiki/URI        ...
    query: Option<String>,   // ... ?t=253           ...
    fragment: Option<String> // ... #History
}
impl URI {
    /// Parses given URI.
    ///
    /// # Caveats
    /// For convenience appends `https://` if scheme missing.
    /// Note that path must be explicitly specified (even if empty) else will get a "valid" URI but parsed incorrectly. This is known
    /// behavior and will be fixed (soon).
    ///
    /// e.g. `https://mincci.no` vs. `https://mincci.no/`
    pub fn new(uri: &str) -> Result<URI, Error> {
        let re_uri = Regex::new(REGEX_URI)?;

        let uri = if uri.contains("://") {
            uri.to_string()
        } else {
            format!("https://{}", uri)
        };

        let [scheme, host, port, path, query, fragment] = regextract_n(&re_uri, &uri, ["scheme", "host", "port", "path", "query", "fragment"]);

        if scheme.is_some() && path.is_some() { // note that no other checks needed, if they are malformed and bleed into another section it would not cause this destructuring to "miss" it since it's now in that other section.
            Ok(URI {
                scheme: scheme.unwrap(),
                host,
                port: port.map(|s| u16::from_str(&s)).transpose().unwrap_or(None),
                path: path.unwrap(),
                query,
                fragment,
            })
        } else {
            Err(anyhow!("Malformed URI"))
        }
    }

    pub fn new_unchecked(uri: &str) -> URI {
        URI::new(uri).unwrap()
    }

    pub fn authority(&self) -> Option<String> {
        match &self.host {
            Some(h) if let Some(port) = self.port => Some(format!("{}:{}", h, port)),
            Some(h) => Some(h.to_string()),
            None => None
        }
    }
}

impl Identifier for URI {
    fn resolve(&self, _auri: Option<URI>) -> Result<String, Error> {
        Ok(self.compile())
    }

    fn compile(&self) -> String {
        let auth = self.authority().map(|mut a| { a.push('/'); a } ).unwrap_or(String::new());

        let query = match &self.query { // <-- as per note that while "self.query.map(|q| format!("?{}", q)).unwrap_or(String::new())" necessitates taking, you can use match ergonomics to wholly work in refland!
            Some(q) => format!("?{}", q),
            None => String::new()
        };

        let fragment = match &self.fragment {
            Some(f) => format!("#{}", f),
            None => String::new()
        };

        let mut uri = String::with_capacity(self.scheme.len() + auth.len() + self.path.len() + query.len() + fragment.len() + 3);
        uri.push_str(&self.scheme);
        uri.push_str("://");
        uri.push_str(&auth);
        uri.push_str(&self.path);
        uri.push_str(&query);
        uri.push_str(&fragment);

        uri
    }
}

#[derive(Debug)]
pub struct RelativeURI {
    path: String,
    query: Option<String>,
    fragment: Option<String>,
}

impl RelativeURI {
    /// Splits URI into path and residual chunks (note while RFC 3986 requires 'path', it may be empty).
    pub fn extract(mut uri: URI) -> (RelativeURI, URI) {
        let (mut path, mut query, mut fragment) = (String::new(), None, None);
        (uri.path, path) = (path, uri.path);
        (uri.query, query) = (query, uri.query);
        (uri.fragment, fragment) = (fragment, uri.fragment);

        (RelativeURI { path, query, fragment }, uri)
    }

    /// Creates a new relative URI, erring if not valid or relative.
    pub fn new(rel_uri: &str) -> Result<RelativeURI, Error> {
        let re_ruri = Regex::new(REGEX_REL_URI).unwrap();
        match rel_uri {
            ru if let [Some(path), query, fragment] = regextract_n(&re_ruri, ru, ["path", "query", "fragment"]) => {
                Ok(RelativeURI { path, query, fragment }) // theoretically path always must match (even empty), so it never fails
            }
            _ => Err(anyhow!("Malformed relative URI"))
        }
    }
}

impl Identifier for RelativeURI {
    /// Resolves the relative URI against an absolute anchor URI. Absolute fragment and query are replaced.
    fn resolve(&self, auri: Option<URI>) -> Result<String, Error> {
        match auri {
            Some(a) => { // manual format to avoid moves
                let auth = a.authority().unwrap_or(String::new());
                let ruri = self.compile();

                let mut uri = String::with_capacity(a.scheme.len() + auth.len() + ruri.len() + 3);
                uri.push_str(&a.scheme);
                uri.push_str("://");
                uri.push_str(&auth);
                uri.push_str(&ruri);

                Ok(uri)
            },
            None => Err(anyhow!("Relative URI must resolve with an absolute URI")),
        }
    }

    fn compile(&self) -> String {
        let query = match &self.query {
            Some(q) => format!("?{}", q),
            None => String::new()
        };

        let fragment = match &self.fragment {
            Some(f) => format!("#{}", f),
            None => String::new()
        };

        let mut ruri = String::with_capacity(self.path.len() + query.len() + fragment.len() + 1);
        ruri.push('/');
        ruri.push_str(&self.path);
        ruri.push_str(&query);
        ruri.push_str(&fragment);

        ruri
    }
}

/// Representation of a segment processing directive containing
/// a basic constructive behavior applied line-wise for a segment.
///
/// Note that this is not a segment content directive, instead it overrides standard
/// segment compilation behavior. Hence no `process` method is provided as the
/// segment compiler should manage what to do with these directives.
#[derive(PartialEq)]
pub enum SegmentDirective {
    Condense,                        // keeps segment condensed (no line end spacing)
}

impl SegmentDirective {
    /// Creates new instance from char representation. Case-insensitive.
    ///
    /// # Caveats
    /// If you are looking to extract and dissect a segdirs chunk within a string, please use [`SegmentDirective::extract`] instead.
    pub fn from(directive: char) -> Result<SegmentDirective, Error> {
        match directive {
            'C' | 'c' => Ok(SegmentDirective::Condense),
            _ => Err(anyhow!("Invalid or nonexistent segment directive"))
        }
    }

    /// Extracts (and dissects) segment directive chunk encoded within a string.
    /// Note that calling this on a string without a segdir chunk is defined behavior, and that `line` will be stripped of its segdir chunk.
    ///
    /// # Caveats
    /// Non-segdir chunk part of `line` must not contain %.
    pub fn extract(line: &mut String) -> Vec<SegmentDirective> {
        let re_segdirs = Regex::new(REGEX_SEGDIRS).unwrap();

        let matches = regextract_n(&re_segdirs, line, ["sdc", "segdirs"]);

        if let [Some(sdc), Some(sds)] = matches { // note that existence of `sds` (segdirs) guarantees `sdc` (segdir chunk) and vice versa
            let mut segdirs = Vec::<SegmentDirective>::with_capacity(sds.len()); // prefer over allocating at init to eliminate vec realloc
            *line = line.replace(&sdc, "");
            segdirs.splice(0..0, sds.as_str().chars().map(SegmentDirective::from).filter_map(|sd| sd.ok()).collect::<Vec<_>>());

            segdirs
        } else {
            vec![]
        }
    }
}

/// Representation of a preprocessor directive containing a basic
/// constructive behavior applied either globally or locally.
///
/// The use of `PreprocessorDirective`s produces a standard .lho preprocessed file.
pub enum PreprocessorDirective {
    TrimComms,                        // Remove all Markdown (%%...%%) comments.
    Finalize,                        // Marks the last lines of each segment as final (if no final is present).
    Define(String, String),           // Replaces the placeholder string (left) with its value.
    Include(String),                  // Inlines the contents of .lhi file to top of content. <-- purposefully doesn't abide by IgnoreDecls if you want to selectively append and remove things :)
    IgnoreDecls,                      // Ignores all in-line decls in the file. <-- note, this may seem useless but if you're just using default decl lib then this saves parsing decls!
    EnforceSpacing,                   // Spaces each line forcibly even if not originally present.
    FlatSegs,                         // Converts all subsegments, resulting in 1-deep segments.
    Condense(String, Option<String>), // Reformats the target (sub)segment for condensed output on single-line lists. Max 2 layers deep.
}

impl PreprocessorDirective {
    /// Creates new instance from string representation.
    ///
    /// # Caveats
    /// Note that `directive` will be in the form of "(.*)"; note
    /// stripped newline but presence of & identifier.
    pub fn from(directive: &str) -> Result<PreprocessorDirective, Error> {
        let (re_def, re_incl, re_cnds) = (Regex::new(REGEX_PREPROC_DEFINE)?, Regex::new(REGEX_PREPROC_INCLUDE)?, Regex::new(REGEX_PREPROC_CONDENSE)?);

        match directive {
            "&TRIM_COMM" | "&TRIM_COMMS" | "&TRIMCOMM" | "&TRIMCOMMS" => Ok(PreprocessorDirective::TrimComms),
            "&IGNORE_DECLS" | "&IGNORE_DECL" | "&IGNOREDECLS" | "&IGNOREDECL" => Ok(PreprocessorDirective::IgnoreDecls),
            "&FINALIZE" | "&FINALISE" | "&MARKFINAL" | "&MARK_FINAL" => Ok(PreprocessorDirective::Finalize),
            "&ENFORCE_SPACING" | "&ENFORCE" | "&ENFORCESPACING" => Ok(PreprocessorDirective::EnforceSpacing),
            "&FLATTEN" | "&FLAT" => Ok(PreprocessorDirective::FlatSegs),
            d if let [Some(ident), Some(value)] = regextract_n(&re_def, d, ["ident", "value"]) => Ok(PreprocessorDirective::Define(ident, value)),
            d if let Some(ident) = regextract(&re_incl, d, "ident") => Ok(PreprocessorDirective::Include(ident)), // <-- you could technically throw a fit here for nonexistant lib, but better to save until parse-time anyway. Plus, the mere existence of a directive does not constitute validity.
            d if let [Some(seg), subseg] = regextract_n(&re_cnds, d, ["seg", "subseg"]) => Ok(PreprocessorDirective::Condense(seg, subseg)),
            _ => Err(anyhow!("Invalid or nonexistent content directive")),
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
    ///
    /// If `PreprocessorDirective::Condense` is present in `directives`, it should be placed prior to `PreprocessorDirective::MarkFinal`
    /// or condensed segments may not be finalized properly (if not already finalized by user).
    ///
    /// Any non-directive preprocessing (e.g. required macro fills) will not be performed here, and should instead be delegated to `$PARSER::preprocess`.
    /// This function assumes such preprocessing is already performed.
    pub fn preprocess(directives: &Vec<PreprocessorDirective>, content: &mut Vec<String>) {
        let (dirs_global, dirs_local): (Vec<_>, Vec<_>) = directives.iter().partition(|&d| matches!(d, PreprocessorDirective::Include(_) | PreprocessorDirective::Finalize | PreprocessorDirective::IgnoreDecls | PreprocessorDirective::Condense(_,_)));
        let (re_seg_d1, re_seg_d2) = (Regex::new(REGEX_SEG_D1).unwrap(), Regex::new(REGEX_SEG_D2).unwrap());

        for dir in dirs_global {
            match dir {
                PreprocessorDirective::Include(ident) => { // <-- #include are injected blindly to the top of the file for the sake of speed.
                    let decls = fs::read_to_string(format!("{}.lhi", ident)).expect(&format!("The include file, {}, could not be read", &ident));
                    content.insert(0, decls);
                    // ▼ use if `content` is purely a string and not vec of strings! ▼
                    // let decls_len = decls.len();
                    //
                    // content.push(decls);
                    // content.rotate_right(decls_len); // <-- pushing to tail of vec then single memory realloc feels more performant than individually shifting all contents one-by-one...
                },
                PreprocessorDirective::Finalize => {
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


                    // ❶ Inject 1..n-1 segments finals, skipping if final found in segment.
                    // ❷ Using 2 sentinel values, does a clever inject of nth segment as well.
                    content.push(String::from(SEG_SENTINEL));
                    content.push(String::from(SEG_SENTINEL));

                    let mut seg_needs_final = true;
                    for i in 1..(content.len() - 2) {
                        // SAFETY: entering for loop = guaranteed chunk size of 3, indices never overlap.
                        // `peek` is borrowed as mut even though it doesn't need to since (a) convinces bchk and (b) prolly saves time as it's 1 access vs. 2.
                        let [pre, curr, peek] = unsafe { content.get_disjoint_unchecked_mut([i - 1, i, i + 1]) };

                        if re_final.is_match(curr).unwrap() { seg_needs_final = false; }

                        if !re_seg.is_match(curr).unwrap() && re_seg.is_match(peek).unwrap() { // <-- final injection should occur on curr or pre... depending on if \n is present before segment identifier
                            if seg_needs_final {
                                let mut target = if curr.is_empty() { pre } else { curr };

                                let nq = regextract(&re_qq, &target, "nq").unwrap();
                                let seg = (target.len() - nq.len())..;
                                segpend(&mut target, seg, &fmst);
                            } else {
                                seg_needs_final = true;
                            }
                        }
                    }

                    content.pop();
                    content.pop();
                },
                PreprocessorDirective::IgnoreDecls => { //                          <-- although this may technically be "local" rather "global", if decl notation changes and must be inspected relatively this helps.
                    let re_declv = Regex::new(REGEX_DECL_VALID).unwrap(); //      additionally, as this is simply a remove operation I feel a simple `retain` may be more performant
                    content.retain(|l| !re_declv.is_match(l).unwrap());
                },
                PreprocessorDirective::Condense(seg, subseg) => {
                    let (con_init, mut con_ptr, mut con_buf) = (content[..].iter_mut(), 0usize, Vec::<String>::new()); // following this, will begin at the target (sub)segment. prefer over content[..].iter_mut() or splice() as cannot insert and iter easily respectively
                    let re_segdirs = Regex::new(REGEX_SEGDIRS).unwrap();

                    //    ▼ end delim regex    ▼ start delim regex
                    let (delim_end, delim_init) = if let Some(ss) = subseg { // condense a subseg of a seg (may include subsegs of subseg))
                        (&re_seg_d2, FmtStr::only_fmt(SEG_D2, ss).unwrap())
                    } else { // condense entire seg
                        (&re_seg_d1, FmtStr::only_fmt(SEG_D1, seg).unwrap())
                    }; // <-- both fmstr & regex should always be valid

                    let mut con_init = con_init.skip_while(|c| { con_ptr += 1; delim_init != **c } ).skip(1); // note! side effect is increment con_ptr. skips the initial label.

                    while let Some(l) = con_init.next() && !delim_end.is_match(l).unwrap() { // <-- this covers all lines to be modified (within the desired (sub)seg). for actually splitting subseg label a blind space check is used.
                        if !l.is_empty() { // skip empty lines. This is especially relevant for the ever-poignant space right before next seglabel that messes this up lol
                            let [mut label, tex] = {
                                let (split, _) = str_splitn_fixed::<_, 2>(l, ' '); // per https://stackoverflow.com/questions/41517187/split-string-only-once-in-rust
                                split.map(str::to_string)
                            };

                            if !re_segdirs.is_match(&label).unwrap() { // !label.contains(&re_segdirs) { add segdirs section if not present
                                label.push_str(r" %{}%");
                            }
                            con_buf.push(FmtStr::only_fmt(&label, &"C{}").unwrap()); // <-- a special "seg directive" that &TRIM_COMM ignores. note how you must continue the {} chain to permit future segdirs. This is parsed and stripped by `Segment::compile`.
                            con_buf.push(tex.to_string());
                        }
                    }
                    content.splice(con_ptr..(con_ptr + con_buf.len() / 2), con_buf); // <-- this should replace all of those segment (buf.len / 2) and insert the extra other half too! per https://stackoverflow.com/questions/28678615/efficiently-insert-or-replace-multiple-elements-in-the-middle-or-at-the-beginnin
                },
                _ => unreachable!()
            }
        }

        for line in content {
            for dir in &dirs_local {
                match *dir {
                    PreprocessorDirective::TrimComms => { // <-- take note, any segdirs must NOT use %%...%%! for example, current SEGDIR_FMT is simply %...%!
                        let re_comms = Regex::new(REGEX_COMMS).unwrap();
                        *line = re_comms.replace_all(line, "").into_owned();
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
            PreprocessorDirective::Finalize => String::from("&FINALIZE"),
            PreprocessorDirective::EnforceSpacing => String::from("&ENFORCE_SPACING"),
            PreprocessorDirective::FlatSegs => String::from("&FLATTEN"),
            PreprocessorDirective::IgnoreDecls => String::from("&IGNORE_DECL"),
            PreprocessorDirective::Define(ident, value) => format!("&DEFINE({}, {})", ident, value),
            PreprocessorDirective::Include(ident) => format!("&INCLUDE({})", ident),
            PreprocessorDirective::Condense(seg, subseg) => {
                match subseg {
                    Some(ss) => format!("&CONDENSE({}, {})", seg, ss),
                    None => format!("&CONDENSE({})", seg)
                }
            }
        }
    }
}

/// An operation segmentator based on wish/fulfill-design.
pub struct Promise {
    ident: String,
    ts: Option<Instant> // timer, time precision
}

impl Promise {
    /// Create new promise.
    /// Note that this will timestamp automatically at instantiation time and stop at drop.
    pub fn new(id: &str) -> Promise {
        Promise { ident: FmtStr::only_fmt(PROMISE_FMT, &id).unwrap(), ts: None }
    }

    /// Creates new promise and wishes upon it, returning promise for fulfillment.
    pub fn only_wish(ident: &str) -> Promise {
        let mut pr = Promise::new(ident);
        pr.wish();
        pr
    }

    /// Wishes the promise, expecting fulfillment.
    pub fn wish(&mut self) {
        self.ts = Some(Instant::now());
        print!("{}", self.ident);
    }

    /// Fulfills the promise and outputs based on pass condition, thus closing it.
    pub fn fulfill(self, pass: bool) { // <-- more behavior can go here if needed (don't touch Drop; may want to allow a cleanup function etc etc.)
        let msg = if pass { PROMISE_OK } else { PROMISE_NG };
        println!("{} ({:.2}ms)", msg, self.ts.and_then(|t| Some(t.elapsed().as_micros() as f32 / 1000.0)).unwrap_or(0.0));
    }

    /// Performs and returns [`Promise::only_wish`] if condition is met, otherwise None.
    /// This is handy for concise conditional promising using a global like `should_bc` in conjunction with [`Promise::fulfill_if`].
    pub fn promise_if(ident: &str, cond: bool) -> Option<Promise> {
        match cond {
            true => Some(Promise::only_wish(ident)),
            false => None
        }
    }

    /// Fulfills and closes promise if `Some`, otherwise does nothing (consumes).
    pub fn fulfill_if(promise: Option<Promise>, pass: bool) {
        match promise {
            Some(p) => p.fulfill(pass),
            None => (),
        }
    }
}

//
// impl Drop for Promise {
//     /// Drops and prints 'parting words' for this `Promise`.
//     fn drop(&mut self) {
//         println!("{} ({:.2}ms)", PROMISE_OK, self.ts.and_then(|t| Some(t.elapsed().as_micros() as f32 / 1000.0)).unwrap_or(0.0));
//     }
// }

#[derive(Debug)]
pub enum HTTPMethod {
    GET,
    HEAD,
    POST,
    PUT,
    DELETE,
    CONNECT,
    OPTIONS,
    TRACE,
    PATCH
}

impl HTTPMethod {
    pub fn new(method: &str) -> Result<HTTPMethod, Error> {
        match method {
            "GET" => Ok(HTTPMethod::GET),
            "HEAD" => Ok(HTTPMethod::HEAD),
            "POST" => Ok(HTTPMethod::POST),
            "PUT" => Ok(HTTPMethod::PUT),
            "DELETE" => Ok(HTTPMethod::DELETE),
            "CONNECT" => Ok(HTTPMethod::CONNECT),
            "OPTIONS" => Ok(HTTPMethod::OPTIONS),
            "TRACE" => Ok(HTTPMethod::TRACE),
            "PATCH" => Ok(HTTPMethod::PATCH),
            _ => Err(anyhow!("No such HTTP method"))
        }
    }
}

pub struct HTTPRequest {
    method: HTTPMethod,
    uri: Box<dyn Identifier>,
    http_ver: f32, // relative-indexed versioning (HTTP/0.9, /1.0, /1.1, /2, /3)
    headers: HashMap<String, String>, // avoid `Header` enum, as custom "X-header" is possible!
    payload: String, // prefer string over raw bytes; (a) transfer is string anyway and (b) HTTP/1.x is plaintext while HTTP/2 is binary
}

impl HTTPRequest {
    /// Assembles a new HTTP request.
    ///
    /// # Caveats
    /// If payload size exceeds [`HTTP_PAYLOAD_MAX_SIZE`] bytes, an error will be forcibly thrown as a safeguard against
    /// overloading recipient servers.
    pub fn new(method: HTTPMethod, uri: URI, http_ver: f32, headers: HashMap<&str, &str>, payload: String) -> Result<Self, Error> {
        if payload.len() > HTTP_PAYLOAD_MAX_SIZE { return Err(anyhow!("Request payload is too large")); }

        let re_http_header = Regex::new(REGEX_HTTP_HEADER)?;
        let mut headers: HashMap<String, String> = headers.iter().map(|(name, field)| (name.to_string(), field.to_string())).collect(); // convert &str map to String map; prior is for front-facing convenience

        if headers.keys().all(|name| re_http_header.is_match(name).unwrap()) && HTTP_VERSIONS.contains(&http_ver) {
            Ok(match method {
                HTTPMethod::POST => {
                    let (ruri, auri) = RelativeURI::extract(uri);
                    headers.insert(String::from("Host"), auri.authority().unwrap()); // For "Host", the scheme is implied and actually must not be existent
                    HTTPRequest { method, uri: Box::new(ruri), http_ver, headers, payload }
                },
                _ => HTTPRequest { method, uri: Box::new(uri), http_ver, headers, payload }
            })
        } else {
            Err(anyhow!("Bad HTTP request"))
        }
    }

    /// Parses and assembles a HTTP request from plaintext form.
    ///
    /// # Caveats
    /// If payload size exceeds [`HTTP_PAYLOAD_MAX_SIZE`] bytes, an error will be forcibly thrown as a safeguard against
    /// overloading recipient servers.
    pub fn from(reqt: &str) -> Result<Self, Error> {
        let re_http_header = Regex::new(REGEX_HTTP_HEADER)?;

        let mut lines = reqt.lines()
            .map(|l| l.trim());

        let (method, uri, http_ver) = {
            if let Some(line) = lines.next() {
                let ([m, u, v], _) = str_splitn_fixed::<_, 3>(line, ' ');
                let nm = HTTPMethod::new(m)?;
                let nu: Box<dyn Identifier> = match nm {
                    HTTPMethod::POST => Box::new(RelativeURI::new(u)?),
                    _ => Box::new(URI::new(u)?),
                };
                let nv = f32::from_str(&v.replace("HTTP/", ""))?;
                if !HTTP_VERSIONS.contains(&nv) {
                    bail!("Invalid HTTP version: {}", nv)
                }

                (nm, nu, nv)
            } else {
                bail!("Missing initial line or bad format in HTTP request")
            }
        };

        let mut headers = HashMap::<String, String>::new();
        while let Some(line) = lines.next() && re_http_header.is_match(line)? {
            if let [name, field, ..] = line.split(": ").collect::<Vec<&str>>()[..] {
                headers.insert(String::from(name), String::from(field));
            } else {
               bail!("Bad headers in HTTP request")
            }
        }

        let payload = lines.collect::<Vec<&str>>().join(" ");

        Ok(HTTPRequest { method, uri, http_ver, headers, payload })
    }

    /// Fill common HTTP headers for a generic single-time request.
    pub fn hfill(&mut self) {
        self.hput("Connection", "close").unwrap(); // per https://stackoverflow.com/a/67038784/30291565, this is why prior requests were stalling for ~60s!
        self.hput("Accept-Encoding", "br, deflate, gzip, x-gzip").unwrap();
        self.hput("Accept", "*/*").unwrap();
    }

    /// Insert given HTTP header if not existent.
    ///
    /// # Caveats
    /// Errs if header name is not valid.
    pub fn hput(&mut self, name: &str, field: &str) -> Result<(), Error>{
        let re_http_header = Regex::new(REGEX_HTTP_HEADER)?;

        if re_http_header.is_match(name)? {
            let (name, field) = (name.to_string(), field.to_string());
            self.headers.entry(name).or_insert(field);

            Ok(())
        } else {
            Err(anyhow!("Invalid HTTP header name"))
        }
    }

    /// Insert given HTTP header, overwriting if existent.
    pub fn hpush(&mut self, name: &str, field: &str) -> Result<Option<String>, Error> {
        let re_http_header = Regex::new(REGEX_HTTP_HEADER)?;

        if re_http_header.is_match(name)? {
            let (name, field) = (name.to_string(), field.to_string());
            Ok(self.headers.insert(name, field))
        } else {
            Err(anyhow!("Invalid HTTP header name"))
        }
    }

    /// Compiles HTTP request into plaintext form valid for sending, such as via TCP.
    pub fn compile(self) -> String {
        format!("{:?} {} HTTP/{}\n{}\n\n{}",
                self.method, self.uri.compile(), self.http_ver, // <-- note! prior `self.uri.resolve(auri)` was throwing "cannot move a value of type 'dyn Identifier'; per https://stackoverflow.com/a/76038535/30291565 trait objects must act only on &self not self
                self.headers.iter().map(|(name, field)| format!("{}: {}", name, field)).collect::<Vec<_>>().join("\n"),
                self.payload)
    }

    /// Sends the compiled HTTP request via [`TcpStream`] to the recipient server specified by the URI and awaits a response with retries and timeouts.
    /// `should_bc` sets if status info is written to stdout.
    ///
    /// # Caveats
    /// For respecting recipient servers, some headers (`User-Agent`, `content-length`) are forcibly overwritten.
    pub fn send(mut self, r_timeout: Duration, w_timeout: Duration, should_bc: bool) -> Result<HTTPResponse, Error> {
        self.hpush("User-Agent", &format!("{}/{}", USER_AGENT, VERSION_NUM))?; // compliant per RFC 2068 14.42, https://stackoverflow.com/questions/16391842/setting-user-agent-correctly-for-a-command-line-app
        self.hpush("Content-Length", &self.payload.as_bytes().len().to_string())?;

        let (reqt, mut resp) = (self.compile(), String::new());
        let auth_cand = regextract(&Regex::new(REGEX_REQT_AUTH).unwrap(), &reqt, "authority");

        if let Some(auth) = auth_cand {
            || -> Result<HTTPResponse, Error> { // "try-catch" behavior adapted https://stackoverflow.com/a/55756926/30291565
                let pr_con = Promise::promise_if("\n▶ Connecting", should_bc);

                let mut stream = TcpStream::connect(format!("{}:80", auth))?;
                stream.set_read_timeout(Some(r_timeout))?;
                stream.set_write_timeout(Some(w_timeout))?;

                Promise::fulfill_if(pr_con, true);



                let pr_write = Promise::promise_if("▶ Writing", should_bc);

                stream.write_all(reqt.as_bytes())?;
                stream.flush();

                Promise::fulfill_if(pr_write, true);

                let pr_read = Promise::promise_if("▶ Reading", should_bc);

                let mut num_reads = 1usize;
                std::thread::sleep(Duration::from_millis(HTTP_RW_WAIT_MS));

                while resp.is_empty() {
                    stream.read_to_string(&mut resp)?;

                    num_reads += 1;
                    if num_reads > HTTP_RW_MAX_ATTEMPTS { return Err(anyhow!("Exceeded max read attempts")) }
                }
                Promise::fulfill_if(pr_read, true);

                HTTPResponse::from(&resp)
            }()
        } else {
            Err(anyhow!("HTTP request failed or timed out"))
        }
    }

    /// Assembles a `multipart/form-data` HTTP/1.1 POST request for plaintext or binary file.
    /// Optional filename parameter if desired.
    ///
    /// # Caveats
    /// In a significant majority of cases the use of `HTTP_POST_BOUNDARY` should already be sufficient; however
    /// if present a manual appendage process is used. If the payload contains the boundary template and many of the
    /// appendage character this method may stall.
    ///
    /// If no filename is given, the method assumes a placeholder extensionless file name that the server may or may not accept.
    ///
    /// The actual file is denoted using `name="file"; filename="$NAME"` which the server may or may not accept.
    ///
    /// Per MDN, any nonalphanumeric chars will be percent-encoded so prefer `Left<&Path>` for binary files.
    pub fn multipost(payload: Either<&str, &Path>, uri: URI, name: Option<&str>, fields: HashMap<&str, &str>) -> Result<Self, Error> {
        let boundary = match payload {
            Left(text) => {
                let mut cand = String::with_capacity(HTTP_POST_BOUNDARY.len() + 3);
                cand.push_str(&HTTP_POST_BOUNDARY);

                while text.contains(&cand) {
                    cand.push('=');
                }
                cand
            },
            Right(_) => String::from(HTTP_POST_BOUNDARY)
        };

        let body = {
            let mut data = fields.iter()
                .map(|(k, v)| format!("--{}\nContent-Disposition: form-data; name=\"{}\"\n\n{}", boundary, k, v))
                .collect::<Vec<_>>();

            data.push(match payload {
                Left(text) =>
                    format!("--{}\nContent-Disposition: form-data; name=\"file\"; filename=\"{}\"\nContent-Type: text/plain\n\n{}", boundary, name.unwrap_or(HTTP_POST_NO_FILENAME), text),
                Right(path) => {
                    let data = fs::read(path)?;
                    format!("--{}\nContent-Disposition: form-data; name=\"file\"; filename=\"{}\"\nContent-Type: application/octet-stream\n\n{:?}", boundary, name.unwrap_or(HTTP_POST_NO_FILENAME), data)
                }
            });

            data.push(format!("--{}--", boundary));
            data.join("\n")
        };

        HTTPRequest::new(HTTPMethod::POST, uri, 1.1, hash_map!["Content-Type" => format!("multipart/form-data; boundary={}", boundary).as_str()], body)
    }
}


pub struct HTTPResponse {
    http_ver: f32,
    status: u16,
    reason: String,
    headers: HashMap<String, String>,
    payload: String,
}

impl HTTPResponse {
    pub fn new(http_ver: f32, status: u16, reason: String, headers: HashMap<&str, &str>, payload: String) -> Result<Self, Error> {
        let re_http = Regex::new(REGEX_HTTP_HEADER).unwrap();

        let headers: HashMap<String, String> = headers.iter().map(|(name, field)| (name.to_string(), field.to_string())).collect();

        if headers.keys().all(|name| re_http.is_match(name).unwrap()) && HTTP_VERSIONS.contains(&http_ver) {
            Ok(HTTPResponse { http_ver, status, reason, headers, payload })
        } else {
            Err(anyhow!("Bad HTTP response"))
        }
    }

    pub fn from(resp: &str) -> Result<Self, Error> {
        let re_http_header = Regex::new(REGEX_HTTP_HEADER)?;

        let mut lines = resp.lines()
            .map(|l| l.trim());

        let (http_ver, status, reason) = {
            if let Some(line) = lines.next() {
                let ([v, s, r], _) = str_splitn_fixed::<_, 3>(line, ' ');
                let nv = f32::from_str(&v.replace("HTTP/", ""))?;
                if !HTTP_VERSIONS.contains(&nv) {
                    bail!("Invalid HTTP version: {}", nv)
                }

                (nv, u16::from_str(s)?, r.to_string())
            } else {
                bail!("Missing initial line or bad format in HTTP response")
            }
        };

        let mut headers = HashMap::<String, String>::new();
        while let Some(line) = lines.next() && !line.is_empty() {
            if let [name, field, ..] = line.split(": ").collect::<Vec<&str>>()[..] && re_http_header.is_match(name)? {
                headers.insert(String::from(name), String::from(field));
            } else {
                bail!("Bad headers in HTTP response")
            }
        }

        let payload = lines.collect::<Vec<&str>>().join(" ");

        Ok(HTTPResponse { http_ver, status, reason, headers, payload })
    }

    pub fn compile(self) -> String {
        format!("HTTP/{} {} {}\n{}\n{}",
                self.http_ver, self.status, self.reason,
                self.headers.iter().map(|(name, field)| format!("{}: {}", name, field)).collect::<Vec<_>>().join("\n"),
                self.payload)
    }
}


/// Constrained representation of a 1-sub decorated label.
/// Effectively a wrapped version of `FmtStr`.
/// e.g. (1), ii., \<hr>5\</hr>
pub struct Label {
    ident: String,   // raw value; 1
    ornament: FmtStr // outside wrapper; ({})
}

impl Label {
    /// Creates new `Label` from parts, erring if a valid 1-sub `FmtStr` cannot be created.
    fn new(ident: String, ornament: String) -> Result<Label, Error> {
        match FmtStr::from(&ornament) {
            Ok(fmts) => Ok(Label { ident, ornament: fmts }),
            Err(e) => Err(e),
        }
    }

    /// Creates new [`Label`] from collated, erring if a valid 1-sub [`FmtStr`] cannot be created.
    ///
    /// # Caveats
    /// Note that the label string must distinguish ident and ornament by wrapping ident with {}.
    ///
    /// e.g.: "({a})" or "{3}."
    ///
    /// format: \[ornament half] { \[ident] } \[ornament half]
    fn from(str: String) -> Result<Label, Error> {
        // note: the label string must distinguish ident and ornament by wrapping ident with {}.
        // e.g.: "({a})" or "{3}."
        // format: [ornament half] { [ident] } [ornament half]

        let spl = str.split(['{', '}']).collect::<Vec<&str>>();
        if let [orna_l, ident, orna_r] = spl[0..3] {
            let ornament: String = format!("{}{{}}{}", orna_l, orna_r);

            Ok(Label::new(ident.to_string(), ornament)?)
        } else {
            Err(anyhow!("Bad label collation"))
        }

    }

    /// Compiles the label parts into collated form.
    fn compile(&self) -> String {
        self.ornament.fmt(&self.ident)
    }
}



/// Representation of the segment structure (labeled ordered possibly-recursive groups of strings).
pub struct Segment {
    eid: Label,
    content: Either<Vec<Segment>, String>, // assume (a)...(z) then 1. to $LEN., bound by italic
    segdirs: Vec<SegmentDirective>
}

impl Segment {
    /// Compiles the segment parts into collated form, with proper TeX spacing.
    ///
    /// # Caveats
    /// TeX spacing depends on inclusion of `req.lhi` (or related spacers) in the compiled document.
    fn compile(&self) -> String {
        let eid = &self.eid.compile();

        match &self.content {
            Left(segs) => {
                let con = segs.iter()
                    .map(Segment::compile)
                    .collect::<Vec<String>>()
                    .join("\n");

                format!("\\item[{}]\n\\begin{{enumerate}}{}\\nq\\end{{enumerate}}\n", eid, con)
            },
            Right(con) if self.segdirs.contains(&SegmentDirective::Condense) => format!("\\item[{}]{}", eid, con),
            Right(con) => format!("\\item[{}]{}\\sqe", eid, con),
        }
    }
}

/// Constrained representation of a 1-sub format string for use with a string anchor.
pub struct FmtStr { // <-- called FmtString? FmtStr? temporarily only accepts one anchor b/c format!() exists.
    orna_l: String,
    orna_h: String
}

impl FmtStr {
    /// Creates a new `FmtStr` from parts.
    ///
    /// # Caveats
    /// Note that this does not include the anchor.
    pub fn new(left: &str, right: &str) -> FmtStr {
        FmtStr { orna_l: left.to_string(), orna_h: right.to_string() }
    }

    /// Creates a new `FmtStr` from collated form.
    /// Errs if invalid form.
    ///
    /// # Caveats
    /// Note that this does not include the anchor; also assumed use of
    /// `FMT_ANCHOR` to represent the anchor.
    pub fn from(fmt_str: &str) -> Result<FmtStr, Error> {
        if fmt_str.contains(FMT_ANCHOR) {
            let (orna_l, orna_h) = fmt_str.split_once(FMT_ANCHOR).unwrap();
            Ok(FmtStr::new(orna_l, orna_h))
        } else {
            Err(anyhow!("Bad fmtstr collation"))
        }
    }

    /// Creates a new `FmtStr` from collated form with anchor and immediately formats.
    /// Errs if invalid form.
    ///
    /// # Caveats
    /// Note that this does not include the anchor; also assumed use of
    /// `FMT_ANCHOR` to represent the anchor.
    pub fn only_fmt(fmt_str: &str, anchor: &dyn ToString) -> Result<String, Error> { // <-- **NEW** this is a new paradigm I'm designing to signify concise (but expensive) make-and-toss operations... OR shortcutting a single-time operation (like a fuse).
        let fmstr = FmtStr::from(fmt_str);
        fmstr.and_then(|fs| Ok(fs.fmt(anchor)))
    }

    /// Formats and collates using the given anchor.
    pub fn fmt(&self, anchor: &dyn ToString) -> String {
        let mut res = String::from(&self.orna_l);
        res.push_str(&anchor.to_string());
        res.push_str(&self.orna_h);

        res
    }

    /// Returns length of ornaments, sans anchor (or placeholder).
    pub fn len(&self) -> usize {
        self.orna_l.len() + self.orna_h.len()
    }

    /// Formats and collates using the anchor placeholder as anchor.
    /// Useful if chaining with other formatters, like `format!()`.
    pub fn raw(&self) -> String {
        let mut res = String::from(&self.orna_l);
        res.push_str(FMT_ANCHOR);
        res.push_str(&self.orna_h);

        res
    }
}


/// Representation and destructuring of Assignment Markdown (AMD)
/// in preparation for compilation to pure TeX.
pub struct MarkdownDoc {
    title: String,
    decls: Vec<String>,
    segs: Vec<Segment>, // assume (1)...($LEN), bound by bold TODO [Segment] should be more performant as on stack (esp. for arr of arr)
    //cache: Option<u8> // TODO make this (Sized) byte array
}

impl MarkdownDoc {
    /// Creates new AMD document representation by parsing from the given filepath, preprocessing, checking decls into database, and destructuring segments.
    ///
    /// # Caveats
    /// Panicks if path was invalid or file could not be read. This behavior may change in the future (i.e. return Result<Self, ()>).
    pub fn from(path: &Path) -> Self {
        let pr_nab = Promise::only_wish("Nabbing");
        let lines = fs::read_to_string(path).expect("Could not read doc")
            .lines()
            .map(|l| l.trim().to_string())
            .collect::<Vec<String>>();
        pr_nab.fulfill(true);

        let pr_prep = Promise::only_wish("Preprocessing");
        let preproc = preprocess_content(lines);
        pr_prep.fulfill(true);

        let (pr_lho, path_lho) = (Promise::only_wish("Writing object file"), format!("{}.lho", path.file_stem().unwrap().display()));
        fs::write(&path_lho, preproc.join("\n")).expect("Could not write object file");
        pr_lho.fulfill(true);

        Self::from_lho(Path::new(&path_lho))
    }

    pub fn from_lho(path: &Path) -> Self {
        let pr_lho = Promise::only_wish("Reading object file");
        let buf = fs::read_to_string(path).expect("Could not read object file");
        let mut content = buf
            .lines()
            .map(|l| l.trim().to_string())
            .into_iter()
            .peekable();
        pr_lho.fulfill(true);

        // Note on parsing decls... strips all $ — may be problematic for decl macros that use $$, but obsitex theoretically shouldn't permit it.

        // Take first (and only) document in YAML db.
        let pr_decls = Promise::only_wish("Injecting decls");

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
        if !db_cands.is_empty() && query(&format!("\n{} new decls found, add to db? (y/n)", db_cands.len())) == "y" { // <-- note! contingent on short-circuit eval of boolean.
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

            write_db(&doc);    // <-- write hot decls to db
            hot_decls.clear(); // <-- clear hot decls as already written to database
        }

        pr_decls.fulfill(true);

        // Parse segments. Depth of 2 for now.
        let pr_segs = Promise::only_wish("Parsing segments");

        let mut segs: Vec<Segment> = Vec::new();
        //let (mut eid1, mut eid2) = (1, 'a');
        let (re1, re2, re0) = (Regex::new(REGEX_SEG_D1).unwrap(), Regex::new(REGEX_SEG_D2).unwrap(), Regex::new(REGEX_SEG_ANY).unwrap());

        while let Some(_) = content.peek() {
            let seg = {
                while let Some(_) = content.next_if(|l| !re1.is_match(l).unwrap()) {} // <-- jump until (before) seg depth=1 tag
                let (eid1, sdc1) = {
                    let (e1, s1) = consume_eid(&mut content, &re1);
                    (Label::from(format!("{{{}}}.", e1.unwrap())), s1.map(|mut s| SegmentDirective::extract(&mut s)).unwrap_or(Vec::new()))
                };

                // Check if subsegs are present... (a), (b), etc etc
                if re2.is_match(&content.peek().unwrap()).unwrap() {
                    let mut subsegs: Vec<Segment> = Vec::new();

                    while content.peek().is_some_and(|c| !re1.is_match(c).unwrap()) { // <-- must check for EOF!
                        let (eid2, sdc2) = {
                            let (e2, s2) = consume_eid(&mut content, &re2);
                            (Label::from(format!("({{{}}})", e2.unwrap())), s2.map(|mut s| SegmentDirective::extract(&mut s)).unwrap_or(Vec::new()))
                        };
                        subsegs.push(consume_segment(&mut content, &re0, eid2.unwrap(), sdc2));
                        //  content.next_if(|l| !re1.is_match(l));
                    }

                    Segment { eid: eid1.unwrap(), content: Left(subsegs), segdirs: sdc1 }
                } else {
                    consume_segment(&mut content, &re1, eid1.unwrap(), sdc1)
                }
            };

            segs.push(seg);
        }

        pr_segs.fulfill(true);

        // TODO image cache
        // let cache = None;

        let title = path.file_stem().unwrap().display().to_string();

        Self { title, decls: hot_decls, segs/*, cache*/ }
    }

    /// Compiles a prepared AMD document into TeX, via injecting decls and substituting content into TeX template.
    pub fn compile(&self) -> TeXContent {
        let pr = Promise::only_wish("Compiling");

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

        pr.fulfill(true);

        TeXContent::from(template)
    }
}


/// Returns string containing ordinal number with corresponding suffix.
fn ordinize(ordinal: u8) -> String {
    let fmtr = match ordinal {
        0 => "th",
        i if i % 10 == 1 => "st",
        i if i % 10 == 2 => "nd",
        i if i % 10 == 3 => "rd",
        _ => "th",
    };

    format!("{}{}", ordinal, fmtr)
}

/// Converts (solar 12mo calendar) month from numeric to word form.
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

/// Capitalizes the given string; if empty no change.
fn capitalize(word: &str) -> String {
    let mut new = String::from(word);

    if !word.is_empty() {
        // SAFETY: already checked so string must be non-empty!
        unsafe {
            let bytes = new.as_bytes_mut();
            bytes[0] += ((b'a'..=b'z').contains(&bytes[0]) as u8) & 32;
        }
    }

    new
}

/// Parses and collects given `.lhi` YAML of statics into string bundle.
///
/// # Caveats
/// Panicks if YAML is not 1D array of strings.
fn parse_statics(yamls: &Yaml) -> String {
    let statics = yamls.as_vec().expect("Bad statics YAML format");
    statics.iter()
        .map(|s| s.as_str().unwrap().to_string())
        .collect::<Vec<String>>()
        .join("\n")
}

/// Parses and collects given `.lhi` YAML of decls into string bundle.
///
/// # Caveats
/// Panicks if YAML is not 1D array of strings.
/// Usage of decls must be within a TeX environment that supports `\newcommand`.
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
                format!("\\providecommand{{\\{}}}{{{}}}\n", id, mac)
            } else {
                format!("\\providecommand{{\\{}}}[{}]{{{}}}\n", id, pc, mac)
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
/// the output to a separate designated "object" file if you want (e.g. .lho or .pli)
///
/// # Caveats
/// Applying all preprocessing will:
///
/// - Guarantee all newlines are at most 1 line
/// - Process all valid directives (%%...%%)
///
/// Behavior may be modified as necessary.
pub fn preprocess_content(mut content: Vec<String>) -> Vec<String> {
    // ▼ REVERSE (AND UNDO) ▼
    // Reverse the vec to get the proper end for FIFO. This is undone afterward !
    // note this is preferred over `VecDeque` and `pop_front()` as lack of utilities (e.g. `dedup`) and no need for other tail;
    // `VecDeque` generally trades excellent head/tail pop/push for more broad overhead while `Vec` has terrible overhead for non-end pop/push but good caching.
    // ...per https://stackoverflow.com/questions/68351027/why-is-vecdeque-slower-than-a-vec
    content.reverse();

    // ▼ TRIM NEWLINES (>=2 -> 1 \n) ▼
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

    // ▼ PARSE DIRECTIVES ▼
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

    if content.last().is_some_and(|l| l.is_empty()) { content.pop(); } // this simple check saves many simple checks later... net profit vuv

    if let Some(_) = content.pop_if(|l| l.contains("%%")) {
        let mut directives = Vec::<PreprocessorDirective>::new();

        while let Some(line) = content.pop() && !line.contains("%%") {
            if let Ok(dir) = PreprocessorDirective::from(line.trim()) {
                directives.push(dir);
            }
        }

        // move any priority directives to front of vec
        // TODO

        // undo fifo reversal
        content.reverse();

        // perform necessary pre-preprocessing
        let (rp_fans, rp_pans) = (Regex::new(RERPL_PREPROC_FINALANS).unwrap(), Regex::new(RERPL_PREPROC_PARTANS).unwrap());

        for line in content.as_mut_slice() {
            // filling \finalans (##) and \partans (@@) macros
            *line = rp_fans.replace(line, r"$left\finalans{$mid}$right").to_string();
            *line = rp_pans.replace(line, r"$left\partans{$mid}$right").to_string();

        }

        PreprocessorDirective::preprocess(&directives, &mut content);
    }

    // ▼ AL DENTE! ▼
    content
}

/// Generates new Overleaf document from given TeX content via URL base64 payload encoding.
/// Prints "encoding" and "exporting" promises if enabled.
///
/// # Caveats
/// Errs if content could not be converted to base64 or failed to send/receive TCP payload to Overleaf servers.
pub fn export_overleaf(tex: TeXContent, should_bc: bool) -> Result<URI, Error> {
    // Encode into base64 (adapt from https://mcyoung.xyz/2023/11/27/simd-base64/#ascii-to-sextet)
    // let pr_enc = Promise::promise_if("Encoding", should_bc);
    // let bex = str2base64::<BASE64_VECTOR_SIZE>(&tex)?;
    // Promise::fulfill_if(pr_enc, true);

    let pr_expo = Promise::promise_if("Exporting", should_bc);

    let mut reqt = HTTPRequest::multipost(Left(&*tex), URI::new_unchecked("http://0x0.st/"), Some("file.tex"), hash_map!["expires" => "1"])?;
    reqt.hfill();

    let resp = reqt.send(Duration::from_secs(HTTP_RW_TIMEOUT_SEC), Duration::from_secs(HTTP_RW_TIMEOUT_SEC), true)?;
    let expo = URI::new(&FmtStr::only_fmt(OVERLEAF_URL, &resp.payload)?);

    Promise::fulfill_if(pr_expo, true);
    expo
}

// Note that statics are only declarable in .lhi and some add'l assumptions are made (strip spacing, immediately add all new, etc).
// ...hence why this is not broadened to work for local scan.

/// Scans the given `.lhi` file capturing all statics and decls.
/// The YAML database is appended with new candidates and resultant stats are printed to out.
///
/// # Caveats
/// The database must retain a valid format (e.g. array of 'decls' and 'statics' with identical destructured arrays as entries.
pub fn scan_lhi(path: &Path) -> Result<(), Error>{
    let lhi = File::open(path)?;

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

    write_db(&doc)?;

    println!("⊛ {} (+ {} replaced) decls, {} statics", num_decl_new, num_decl_rep, num_static);

    Ok(())
}

/// Scans all .lhi files in the working directory.
pub fn scan_lhis() -> Result<(), Error> {
    for lhi in fs::read_dir(".")? // per https://stackoverflow.com/a/75880545/30291565
        .filter_map(|res| res.ok())
        .map(|entry| entry.path())
        .filter_map(|path| {
            if path.extension().map_or(false, |ext| ext == "lhi") {
                Some(path)
            } else {
                None
            }
        })
        .collect::<Vec<_>>()
    {
        scan_lhi(&lhi)?;
    }

    Ok(())
}

/// Converts the collated decl into a YAML entry using [assemble_decl].
///
/// # Caveats
/// Errs if decl is not able to be parsed (i.e. invalid format).
fn decl2yaml(decl: &str) -> Result<Yaml, Error> {
    // decl format is "\newcommand{\$ID}{$MACRO}" or "\newcommand{\$ID}[$PC]{$MACRO}}"
    let (re_valid, re_invalid) = (Regex::new(REGEX_DECL_VALID)?, Regex::new(REGEX_DECL_INVALID)?);
    let (caps_valid, caps_invalid) = (re_valid.captures(decl)?, re_invalid.captures(decl)?);

    match (caps_valid, caps_invalid) {
        // Valid decl
        (Some(caps), _) if caps.len() == 5 => { // <-- note that this is (1) full capture, (1) [$ID] opt group, (3) needed values.
            Ok(assemble_decl(&caps))
        },

        // Invalid decl (content in right place but not right format)
        (Some(caps_v), Some(caps_i)) if caps_v.len() < caps_i.len() => {
            Err(anyhow!("Cannot parse invalid decl to YAML"))
        },

        // Malformed decl (content not in right places)
        _ => {
            Err(anyhow!("Cannot parse malformed decl to YAML"))
        }
    }
}

/// Prompts user for input and returns, erring if unable to read from buffer.
fn query(msg: &str) -> String {
    print!("{}", format!("{} ... ", msg));
    let _ = stdout().flush();

    let mut bfr = String::new();
    stdin().read_line(&mut bfr).expect("Bad user input");
    bfr.trim().to_string()
}

/// Consumes an entire AMD segment; this works with any level of segment.
///
/// # Caveats
/// Cannot guarantee that immediate next token contains matching EID so must manually pass the constructed segment's EID.
/// Likewise, cannot know what to use to end stepping so must manually pass in delimiting pattern.
fn consume_segment<I: Iterator<Item = String>>(content: &mut Peekable<I>, delim: &Regex, eid: Label, segdirs: Vec<SegmentDirective>) -> Segment {
    let mut body = content.next().unwrap(); // <-- no add'l formatting for initial segment separator. This should always exist.
    body.push('\n');
    let re_qq = Regex::new(REGEX_USES_QQ).unwrap();

    //let eid = regextract(delim, &content.next().unwrap(), "eid").unwrap();

    while let Some(line) = content.next_if(|l| !delim.is_match(l).unwrap()) {
        //has_final &= re_final.is_match(&line).unwrap(); // <-- tried to make a Oncelet, but turns out bit-AND is just that.

        let nq = regextract(&re_qq, &line, "nq").unwrap_or(String::new());
        let is_qq = nq.len() < line.len();

        let append = match &line {
            l if l.is_empty() => {
                String::from("\\\\")
            },
            _ if segdirs.contains(&SegmentDirective::Condense) => {
                String::from("\n")
            }

            l if l.eq(LINE_BREAK) => {
                String::from("\\sqe\n")
            }

            l if is_qq => {
                format!("\n\n{}", &l).to_string()
            },

            l => {
                format!("\n\n{}", &l).to_string()
            }
        };

        body.push_str(&append);
    }

    Segment { eid, content: Right(body), segdirs }
}

/// Consume effective identifier (EID) and segdirs chunk (SDC) from the immediate following token.
/// Note this is preferred over returning `(Option<String>, Option<String>)` as existence of EID guarantees SDC.
///
/// # Caveats
/// May require other operations in future hence separation from its (one) usage.
fn consume_eid<I: Iterator<Item = String>>(content: &mut I, re_eid: &Regex) -> (Option<String>, Option<String>) {
    let re_sdc = Regex::new(REGEX_SEGDIRS).unwrap();

    if let Some(line) = content.next() {
        (regextract(re_eid, &line, "eid"), regextract(&re_sdc, &line, "sdc"))
    } else {
        (None, None)
    }
}

/// Assembles decl YAML given named regex captures.
///
/// # Caveats
/// Named capture groups must be `id`, `macro`, `pc` and datatypes must be valid.
fn assemble_decl(caps: &Captures) -> Yaml { // <-- I don't think this is designed well so maybe fix!! ouo
    let (id, mac, pc) = (&caps["id"], &caps["macro"], &caps.name("pc"));
    let mut hash = yaml::Hash::new();
    hash.insert(Yaml::String("id".to_string()), Yaml::String(id.to_string()));
    hash.insert(Yaml::String("macro".to_string()), Yaml::String(mac.to_string()));
    hash.insert(Yaml::String("pc".to_string()), Yaml::Integer(pc.and_then(|c| Some(c.as_str().parse::<i64>().unwrap())).unwrap_or(0)));
    Yaml::Hash(hash)
}

/// Extracts named capture group from matching the given haystack, if present.
pub fn regextract(re: &Regex, haystack: &str, name: &str) -> Option<String> {
    let caps = re.captures(haystack).unwrap();
    caps.and_then(|c| c.name(name).map(|m| m.as_str().to_string())) // <-- m is of type `Match<'_>`, not `&str`
}

/// Extracts the specified named capture groups from the given haystack, if present per-case.
///
/// # Caveats
/// Note that returns `Err` if regex could not match, while returns `Some([None, None..])` if regex able to match but no captures.
/// This is for avoiding requiring two matches if need to check for regex validity and actual captures (e.g. add'l `Regex::is_match`).
pub fn regextract_n<const N: usize>(re: &Regex, haystack: &str, names: [&str; N]) -> [Option<String>; N]
where [Option<String>; N]: Default {
    if let Some(caps) = re.captures(haystack).unwrap() {
        names.map(|n| caps.name(n).and_then(|c| Some(c.as_str().to_string())))
    } else {
        Default::default() // https://www.reddit.com/r/learnrust/comments/n0siwl/why_is_copy_required_for_initializing_an_array/; for Option<U>, U has trait reqs that None won't meet. Default does the trick!
    }
}

/// Merges two regex patterns together; the resultant may match either case.
///
/// # Caveats
/// This only works with regex with one (1) named capture group. Also naive implem as groups could already be named numerically (e.g. pat1 -> pat11).
/// This may be inefficient as well, since it naively glues both together rather than considering redundancies (e.g. \[a-z] + \[f-zA-C] produces (\[a-z]|\[f-zA-C]), not \[a-zA-C]).
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

/// Equivalent to [str::splitn] but returns a fixed-length `[&str; N]` instead of `SplitN<'_>` for easier binding.
///
/// # Caveats
/// Still uses [str::splitn], which will give 0 ≤ `n` ≤ N items dependent on how many splits.
/// If less than N, empty &str will be stored in trailing spots. Use the returned `usize` to track `n`.
#[inline(always)]
fn str_splitn_fixed<P: Pattern, const N: usize>(str: &str, pat: P) -> ([&str; N], usize) {
    let (mut buf, mut len, split) = ([str; N], 0usize, str.splitn(N, pat));

    for (i,s) in split.enumerate() {
        buf[i] = s;
        len += 1;
    }

    (buf, len)
}

//fn load_db<'d>() -> (&'d mut Array, &'d mut Array, BufWriter<File>) {

/// Opens and parses the YAML decls/statics database.
///
/// # Caveats
/// Panicks if database not in valid format (see [scan_lhi] for validity specs).
fn open_db() -> Yaml {
    let doc = {
        let raw = fs::read_to_string(PATH_DB).expect("Could not read decls YAML");
        YamlLoader::load_from_str(&raw).expect("Could not parse YAML")
    };
    doc.into_iter().next().unwrap_or(Yaml::Array(vec![]))
}

/// Opens YAML decls/statics database, and dumps/appends the given YAML doc.
///
/// # Caveats
/// Panicks if the given YAML is not valid or dumpable.
fn write_db(doc: &Yaml) -> Result<(), Error>{
    let mut db = OpenOptions::new()
        .write(true)
        .append(false)
        .open(PATH_DB)
        .unwrap();
    let mut dump = String::new();
    let mut emitter = YamlEmitter::new(&mut dump);
    emitter.dump(doc)?;

    db.write_all(dump.as_bytes())?;
    Ok(())
}

/// Helper function for converting Rust string to YAML string.
fn to_yaml_str(str: &str) -> Yaml {
    Yaml::String(str.to_string())
}

/// Send contents to clipboard.
///
/// # Caveats
/// `pbcopy` must be present and executable (-xr) on the executing machine.
pub fn to_clipboard(contents: &str) {
    let mut pbcopy = Command::new("pbcopy")
        .stdin(Stdio::piped())
        .spawn().unwrap();

    pbcopy.stdin.as_mut().unwrap().write_all(contents.as_bytes()).unwrap();
    pbcopy.wait().unwrap();
}

/// Counts the number of occurrences of the given string within the haystack.
///
/// # Caveats
/// This uses blind exact-match counting, patterns and variations (e.g. caps) will not work.
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
    str.reserve_exact(append.len());                 // <-- prealloc base string
    let pati = str.get(seg.clone()).unwrap(); // <-- take segment
    str.replace_range(seg, &append.fmt(&pati));     // <-- append mod to seg, put back
}

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


/// Converts a string to Base64, appending alignment character(s) when necessary.
/// Errs if cannot assemble valid (UTF-8) string from modified bytes.
pub fn str2base64<const N: usize>(str: &str) -> Result<String, FromUtf8Error>
where LaneCount<N>: SupportedLaneCount {
    // CHALLENGE: make this branchless and hyper-optimize!! (but not micro-optimize?)
    // └————— tl;dr hot-cold loops for unaligned read from string to prepare u6 -> u8 for SIMD magic.
    //      └————— ...this is moreso for practicing SIMD/raw pointers rather than applicability (e.g. using a zeroed u8 Vec prolly compiles to faster anyway).


    // SAFETY: `str` is guaranteed to be valid UTF-8 (even if variable-length, base64 only takes 6b anyway) N x 8 bits.
    unsafe {
        // ❶ Pad the u6s to u8s! Unaligned-read (`mov rax, qword ptr [rdx + rax]`!!!) through entire string
        // Note that (i) string has to be padded with zero bytes for perfect 3B chunks and (ii) bytes have to be put into big endian!
        // @adapts https://lukefleed.xyz/posts/compressed-fixedvec/#faster-reads-unaligned-access
        let (mut padded_str, mut len) = (str.to_string(), str.len());
        let pad = ((len % 3) ^ 2 ^ 1) % 3;

        padded_str.push_str(&String::from_utf8_unchecked(vec![0x0, pad as u8])); // 2 -> 1, 1 -> 2; 5 -> 2, 6 -> 1
        let mut ptr_u8: *mut u8 = padded_str.as_mut_ptr();

        len = ((len + pad) * 8) / 6; // <-- even with the 3B guarantee, still have to divide!

        // let (mut ptr_u8, mut len, _): (*mut u8, usize, _) = padded_str.into_raw_parts(); <-- per the docs, this memory is not freed unless `from_raw_parts` is called :(

        // wait, first what the hey is going on in that vec! declaration?
        // this is for padding zero bytes to make perfect 3B chunks, but note that `len % 3` is not enough as 2 maps to '=' (1) and 1 maps to '==' (2).
        //
        // if you look at small samples, you'll see that len 3 -> '', len 4 -> '==', len 5 -> '=', len 6 = '', len 7 -> '=', len 8 -> '=='...
        // oh!! if not divisible by 3, then even takes '==' (2) and odd takes '=' (1).
        //
        // ~~courtesy of https://electronics.stackexchange.com/a/611862/451305, seems like modulo is usually expensive, unless you already know what you mod by!
        // in that case the compiler, rather than using taxing division (ouch) will turn it into a simple mask (ie a & 0x07) which is nice and cheap!~~
        // ▲ false; rust 1.90.0 optimizes powers-of-2 into `and rax, 3...` while nons into `xor edx, edx; div rcx...` vnv
        //
        // but turns out our good friend xor has something to say...
        // a ^ a = 0
        // a ^ 0 = a
        //
        // done and dusted!
        // (len % 3) ^ (2 ^ 1)

        //assert!(N <= len, "Cannot call with N > string length");

        let layout = Layout::from_size_align_unchecked(len, 8);
        let ptr_ps = alloc_zeroed(layout);

        let mut ptr_u6: *mut u8 = ptr_ps.clone();

        // 'HOT LOOP'
        // `len` is num of u6 in str... then div by 4 for num of u24, remainder is removed 2 bits >:)
        // let mut chunk: [u8; 3] = [0; 3];
        // let mut ptr_chunk = chunk.as_mut_ptr();

        let mut chunk = 0u32;
        let ptr_chunk: *mut u8 = (&raw mut chunk).cast::<u8>(); // <-- `addr_as_mut!` is soft-deprecated, recommended &raw mut instead.

        for _ in 0..(len >> 2) {
            ptr::copy_nonoverlapping(ptr_u8, ptr_chunk,3); // <-- `chunk` is anchored LSB, `ptr_chunk` is anchored MSB! (1111_1100_0000_0000 vs 0000_0000_0011_1111)
            chunk = chunk.to_be() >> 8; // <-- must convert to big-endian, but note that u32 is 4 bytes not 3, so shift back into position (as in, "41 42 43 00".to_be() = "00 43 42 41" not "43 42 41 00"!)

            // a little something to help you visualize...!
            // let's try with `base64_sm_remless`'s example, "000" or 0x303030.
            //
            //                (1)       (2)        (3)     (4)
            // 0bXXXX_XXXX_[0011_00][00_0011]_[0000_00][11_0000]
            //
            // (1) 0011_00 = 12 = 0x0C
            // (2) 00_0011 = 3 = 0x03
            // (3) 0000_00 = 0 = 0x00
            // (4) 11_0000 = 48 = 0x30
            //
            // that example doesn't demonstrate but note byte endianness matters...
            // consider a truncation of `base64_med_remless`, "ABC" or 0x414243.
            // this is equivalent to 0b01000001_01000010_0100011.
            //
            // naively extracting the most-significant bits using the following code
            // will actually give you malformed output!
            //
            //
            // the naive trick works for "000" since byte order is irrelevant, but it does here.
            //      you get 0b[010000][11_0100][0010_01][000001] which produces Q8JB...
            // but you want 0b[010000][01_0100][0010_01][000011] which produces QUJD!
            // so obviously you need to change it from little endian to big endian, right?
            //
            // things get complicated when you consider a multi-chunk like "ABCDEF"... you can't just simply
            // take the string and flip all the bytes b/c that messes up ordering.
            //
            // ✧ the key is to convert to big-endian... u32 is 4 not 3 bytes hence see the fix above nvn ✧

            for _ in 0..4 {
                ptr_u6.write(((chunk & 0xFC0000) >> 18) as u8); // 0xFC0000 = 0b0000_0000_1111_1100_0000_0000_0000_0000 (leading 6 bits)
                chunk <<= 6;
                ptr_u6 = ptr_u6.add(1);
            }

            ptr_u8 = ptr_u8.add(3);
        }

        // 'COLD LOOP'
        // I was hoping to use these clever masking tricks I conjured up ^^
        // but I found out they don't really work (either my logic was messed up or the need for zero-byte appending)...
        // the idea was to do some clever masking (including getting lazy to save another mask layer) to extract the appropriate
        // bits and counterpart bits from the current and prior byte respectively.
        //
        // "ab" -> 0x6162 -> 0b[011000][01_0110  ][0010 + 00][000000] -> YWI=
        // "a"  -> 0x61   -> 0b[011000][01 + 0000][0000 + 00][000000] -> YQ==
        //
        // ▲ notice that you can just directly append "=" for r2 and "==" for r1 and still chunk by 3 bytes! ▲
        //
        // offset           =   2 bits         4 bits       6 bits       (8 bits)      0 bits
        // *b2              = [111111]00 -> 1111]00 00 -> 11]00 0000 -> 00000000 -> [111111]00
        // *b1              =  000000 00 -> 0000 00[11 -> 00 00[1111 -> 00111111 ->  000000 00
        // ^b2 & m (strict) =  000000 00 -> 0000 00 11 -> 00 00 1111 -> 00111111 ->  000000 00
        // ^b2 & m (lazy)   =  111111 00 -> 1111 00 11 -> 11 00 1111 -> 00111111 ->  111111 00
        // ^(^bm & m (l))   =  000000 11 -> 0000 11 00 -> 00 11 0000 -> 11000000 ->  000000 11
        //
        // ▼ nonetheless I still think the logic is really interesting, see if you can tidy this up and make it actually work! ▼
        //
        // ```
        // let mask_u6: u8 = 0b11111100; // <-- ver. b2, complement for ver. b1
        // let mask_cc: u8 = 0b00000011; // <-- complement AND mask (lazy) (complemented again)
        // let (mut b1, mut b2) = (0u8, 0u8);
        //
        // for mi in 0u32..(len & 0b11) as u32 { // <-- guaranteed to be 0-3 loops
        //     b2 = ptr_u8.read();
        //     ptr_u6.write((b2 & mask_u6 << mi) >> mi | (b1 & !(mask_u6 << mi) & !(mask_cc << mi)) << (8 - mi));
        //
        //     ptr_u8 = ptr_u8.add(1);
        //     ptr_u6 = ptr_u6.add(1);
        //     b1 = b2;
        // }
        // ```

        // reset pointer position...
        ptr_u6 = ptr_ps.clone();

        // ❷ Unroll and jam loops for base64 conversion! Hot loop is `chunks_exact` filling full SIMD(?) registers, cold loop is part of a register.
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
                masked_splat(&mask_numeric, b'0' as i8 - 52) |
                masked_splat(&mask_pluses, b'+' as i8 - 62) |
                masked_splat(&mask_slashes, b'/' as i8 - 63);

            let ptr_hun = (hun.cast::<u8>() + chu)[..].as_ptr();

            ptr::copy_nonoverlapping(ptr_hun, ptr_u6, N);
            ptr_u6 = ptr_u6.add(N); // <-- `ptr_u6` won't point to end of string but sometimes a bit ahead, hence cannot backtrack from relative. instead...
        }

        // overwrite garbage bytes with padding characters by resetting and reusing `ptr_u6`
        ptr_u6 = ptr_ps.add(len - pad);
        ptr_u6.write_bytes(b'=', pad);

        String::from_utf8(Vec::from_raw_parts(ptr_ps, len, len))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[inline(always)]
    fn base64_test(content: &str, expected: &str) {
        let res4 = str2base64::<4>(content).unwrap();
        let res8 = str2base64::<8>(content).unwrap();
        let res16 = str2base64::<16>(content).unwrap();
        let res32 = str2base64::<32>(content).unwrap();
        let res64 = str2base64::<64>(content).unwrap();

        assert_eq!(res4, expected);
        assert_eq!(res8, expected);
        assert_eq!(res16, expected);
        assert_eq!(res32, expected);
        assert_eq!(res64, expected);
    }

    #[test]
    fn grc_uri() {
        let u0 = URI::new("http://example.com");
        let u1 = URI::new("https://www.overleaf.com/docs");

        assert!(u0.is_ok());
        assert!(u1.is_ok());
    }

    #[test]
    fn grc_decl_parsing() {
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
    fn grc_regex() {
        let (re1, re2) = (Regex::new(REGEX_SEG_D1).unwrap(), Regex::new(REGEX_SEG_ANY).unwrap());
        assert!(re1.is_match("**1.**").unwrap());
        assert!(!re1.is_match("jiawejifajweifjaiwejf").unwrap());
        assert!(re2.is_match("*(a)*").unwrap());
        assert!(re2.is_match("**1.**").unwrap());
        assert!(!re2.is_match("*(a)**").unwrap());
    }

    #[test]
    fn grc_preproc() {
        // &TRIM_COMM
        let re_comms = Regex::new(REGEX_COMMS).unwrap();
        let res = re_comms.replace_all("%%test%%", "");
        assert_eq!(res, "");

        // &DEFINE(_, _)
        let re_def = Regex::new(REGEX_PREPROC_DEFINE).unwrap();
        let res = regextract_n(&re_def, "&DEFINE(wario, mario)", ["ident", "value"]);
        print!("");
    }

    #[test]
    fn http_multipost() {
        let res = HTTPRequest::multipost(Left("000CD!"), URI::new_unchecked("http://0x0.st/"), Some("wow.txt"), hash_map!["expires" => "1"]);

        to_clipboard(&res.unwrap().compile());

//         assert!(res.is_ok());
//         assert_eq!(res.unwrap().compile(), "POST / HTTP/1.1\n\
// Host:  0x0.st\n\
// Content-Type: multipart/form-data; boundary=------------------------boundary123\n\
// \n\
// --------------------------boundary123\n\
// Content-Disposition: form-data; name=\"file\"; filename=\"file\"\n\
// Content-Type: application/octet-stream\n\
// \n\
// 4588484564849849846546546846848646\n\
// --------------------------boundary123\n\
// Content-Disposition: form-data; name=\"expires\"\n\
// \n\
// 1\n\
// --------------------------boundary123--")
    }

    #[test]
    fn base64_sm_rl_symm() {
        base64_test("000", "MDAw");
    }

    #[test]
    fn base64_sm_rl_asymm() {
        base64_test("ABC", "QUJD");
    }

    #[test]
    fn base64_sm_rf0() {
        base64_test("ab", "YWI=");
    }

    #[test]
    fn base64_sm_rf1() {
        base64_test("a", "YQ==");
    }

    #[test]
    fn base64_med_rl0() {
        base64_test("ABCDEFGHIJKL", "QUJDREVGR0hJSktM");
    }

    #[test]
    fn base64_med_rl_spaces() {
        base64_test("these are words you should convert into base64 lolz", "dGhlc2UgYXJlIHdvcmRzIHlvdSBzaG91bGQgY29udmVydCBpbnRvIGJhc2U2NCBsb2x6");
    }

    #[test]
    fn base64_med_rl1() {
        base64_test("293jf9j3292i40o0245$=", "MjkzamY5ajMyOTJpNDBvMDI0NSQ9");
    }

    #[test]
    fn base64_med_rl_uni0() {
        base64_test("語 Φ Д Δ ㅂ و ߐ ሀ ހ ઘ  ஊ అ ഗ Ꮳ ᚨ 𐌀 ee𐤀", "6KqeIM6mINCUIM6UIOOFgiDZiCDfkCDhiIAg3oAg4KqYICDgroog4LCFIOC0lyDhj6Mg4ZqoIPCQjIAgZWXwkKSA");
    }

    #[test]
    fn base64_med_rl_uni1() {
        base64_test("�����������������������������", "77+977+977+977+977+977+977+977+977+977+977+977+977+977+977+977+977+977+977+977+977+977+977+977+977+977+977+977+977+9");
    }

    #[test]
    fn base64_med_rl_uni2() {
        base64_test("﷐﷑﷒﷓﷔﷕﷖﷗﷘﷙﷚﷛﷜﷝﷞﷟﷠﷡﷢﷣", "77eQ77eR77eS77eT77eU77eV77eW77eX77eY77eZ77ea77eb77ec77ed77ee77ef77eg77eh77ei77ej");
    }

    #[test]
    fn base64_sm_rl_all() {
        base64_test("EKN<", "wavzBEVL2048/+");
    }

    #[test]
    fn base64_med_rf0() {
        base64_test("abcjiawefjaiweawe", "YWJjamlhd2VmamFpd2Vhd2U=");
    }

    #[test]
    fn seg() {
        let re = Regex::new(REGEX_SEG_D2).unwrap();
        assert!(re.is_match("*(a)*").unwrap());
        assert!(re.is_match("*(a)* %C{}%").unwrap());
    }

    // #[test]
    // fn base64_lg_rl() {
    //     let content = MarkdownDoc::new("assi13.md").compile();
    //     let res4 = str2base64::<4>(&*content).unwrap();
    //     let res8 = str2base64::<8>(&*content).unwrap();
    //     let res16 = str2base64::<16>(&*content).unwrap();
    //     let res32 = str2base64::<32>(&*content).unwrap();
    //     let res64 = str2base64::<64>(&*content).unwrap();
    // }
}