//! The Isabelle/TLA+ object logic that tlapm ships: its constants, the theorems its theories
//! prove, and the order of the simpset and the classical rule nets. The theorems come from tlapm's
//! Isabelle/TLA+ theories, BSD licensed, see LICENSE-tlapm.
//!
//! `data/logic.bin` holds it in a compact binary form of the JSON the TypeScript Isabelle read,
//! beside the digest of that JSON, which the test below checks. Both are frozen: the script that
//! exported them from tlapm's heap read the TypeScript Isabelle, and went with it. Types, terms and
//! theorems refer to each other, and to `strings`, by their index (`u32`).

use std::sync::OnceLock;

/// A type node: `[0, name, ...args]`, `[1, name]` or `[2, name, index]`.
pub enum TypeNode {
    Type { name: u32, args: Vec<u32> },
    TFree { name: u32 },
    TVar { name: u32, index: i32 },
}

/// A term node: `[0, name, type]`, `[1, name, type]`, `[2, name, index, type]`, `[3, index]`,
/// `[4, name, type, body]` or `[5, function, argument]`.
pub enum TermNode {
    Const { name: u32, typ: u32 },
    Free { name: u32, typ: u32 },
    Var { name: u32, index: i32, typ: u32 },
    Bound { index: i32 },
    Abs { name: u32, typ: u32, body: u32 },
    App { function: u32, argument: u32 },
}

/// A constant, with its type and the right-hand side of an abbreviation, which parsing unfolds.
pub struct ConstEntry {
    pub name: String,
    pub typ: u32,
    pub abbreviation: Option<u32>,
}

pub struct Fact {
    pub name: String,
    pub thms: Vec<u32>,
}

pub struct Cong {
    pub is_const: bool,
    pub name: String,
    pub rule: u32,
}

pub struct WeakCong {
    pub is_const: bool,
    pub name: String,
}

pub struct Simproc {
    pub name: String,
    pub lhss: Vec<u32>,
}

/// A classical rule by theorem id: the rule, its internal form, its swapped forms, and the same
/// for its duplicating form.
pub struct LogicRule {
    pub rule: u32,
    pub internal: u32,
    pub swapped: Vec<u32>,
    pub dup: u32,
    pub dup_swapped: Vec<u32>,
}

/// A rule of a claset net, by theorem id, with its insertion tag.
pub struct NetItem {
    pub tag: i32,
    pub is_elim: bool,
    pub rule: u32,
}

/// A rule of the extra net or of the context rules, with its weight.
pub struct ExtraNetItem {
    pub weight: u32,
    pub tag: i32,
    pub is_elim: bool,
    pub rule: u32,
}

pub struct NetPair<Item> {
    pub intro: Vec<Item>,
    pub elim: Vec<Item>,
}

pub struct Claset {
    pub safe_is: Vec<LogicRule>,
    pub safe_es: Vec<LogicRule>,
    pub unsafe_is: Vec<LogicRule>,
    pub unsafe_es: Vec<LogicRule>,
    pub swrappers: Vec<String>,
    pub uwrappers: Vec<String>,
    pub safe0: NetPair<NetItem>,
    pub safep: NetPair<NetItem>,
    pub r#unsafe: NetPair<NetItem>,
    pub dup: NetPair<NetItem>,
    pub extra: NetPair<ExtraNetItem>,
}

pub struct ContextRules {
    pub bang: NetPair<ExtraNetItem>,
    pub plain: NetPair<ExtraNetItem>,
}

pub struct LogicData {
    pub strings: Vec<String>,
    pub types: Vec<TypeNode>,
    pub terms: Vec<TermNode>,
    /// The theorems' propositions, by term id.
    pub thms: Vec<u32>,
    pub consts: Vec<ConstEntry>,
    /// The constant each unqualified name stands for.
    pub names: Vec<(String, String)>,
    pub facts: Vec<Fact>,
    pub fact_names: Vec<(String, String)>,
    /// The simpset's rewrite rules, in the order of Net.entries.
    pub simps: Vec<u32>,
    pub congs: Vec<Cong>,
    pub weak_congs: Vec<WeakCong>,
    pub simprocs: Vec<Simproc>,
    pub loopers: Vec<String>,
    pub unsafe_solvers: Vec<String>,
    pub safe_solvers: Vec<String>,
    pub claset: Claset,
    pub context_rules: ContextRules,
}

/// The logic, decoded on first use.
pub fn logic_data() -> &'static LogicData {
    static LOGIC_DATA: OnceLock<LogicData> = OnceLock::new();
    LOGIC_DATA.get_or_init(|| decode(include_bytes!("../../data/logic.bin")))
}

struct Reader<'a> {
    bytes: &'a [u8],
    position: usize,
    table: Vec<String>,
}

impl Reader<'_> {
    fn byte(&mut self) -> u8 {
        let byte = *self
            .bytes
            .get(self.position)
            .expect("logic.bin is truncated");
        self.position += 1;
        byte
    }

    fn unsigned(&mut self) -> u32 {
        let mut value = 0u32;
        let mut shift = 0;
        loop {
            let byte = self.byte();
            let bits = u32::from(byte & 0x7f);
            value |= bits
                .checked_shl(shift)
                .filter(|shifted| shifted >> shift == bits)
                .expect("logic.bin holds a varint over 32 bits");
            if byte & 0x80 == 0 {
                return value;
            }
            shift += 7;
        }
    }

    fn length(&mut self) -> usize {
        usize::try_from(self.unsigned()).expect("a u32 fits a usize")
    }

    fn signed(&mut self) -> i32 {
        let value = self.unsigned();
        let magnitude = i32::try_from(value >> 1).expect("a u32 halved fits an i32");
        if value & 1 == 0 {
            magnitude
        } else {
            -magnitude - 1
        }
    }

    fn boolean(&mut self) -> bool {
        match self.unsigned() {
            0 => false,
            1 => true,
            _ => panic!("logic.bin holds a boolean other than 0 or 1"),
        }
    }

    fn string(&mut self) -> String {
        let id = self.length();
        self.table[id].clone()
    }

    fn array<Item>(&mut self, mut read_item: impl FnMut(&mut Self) -> Item) -> Vec<Item> {
        let length = self.length();
        (0..length).map(|_| read_item(self)).collect()
    }

    fn ids(&mut self) -> Vec<u32> {
        self.array(Self::unsigned)
    }

    fn strings(&mut self) -> Vec<String> {
        self.array(Self::string)
    }

    fn rule(&mut self) -> LogicRule {
        LogicRule {
            rule: self.unsigned(),
            internal: self.unsigned(),
            swapped: self.ids(),
            dup: self.unsigned(),
            dup_swapped: self.ids(),
        }
    }

    fn item(&mut self) -> NetItem {
        NetItem {
            tag: self.signed(),
            is_elim: self.boolean(),
            rule: self.unsigned(),
        }
    }

    fn extra_item(&mut self) -> ExtraNetItem {
        ExtraNetItem {
            weight: self.unsigned(),
            tag: self.signed(),
            is_elim: self.boolean(),
            rule: self.unsigned(),
        }
    }

    fn pair<Item>(&mut self, mut read_item: impl FnMut(&mut Self) -> Item) -> NetPair<Item> {
        NetPair {
            intro: self.array(&mut read_item),
            elim: self.array(&mut read_item),
        }
    }

    fn type_node(&mut self) -> TypeNode {
        match self.unsigned() {
            0 => TypeNode::Type {
                name: self.unsigned(),
                args: self.ids(),
            },
            1 => TypeNode::TFree {
                name: self.unsigned(),
            },
            2 => TypeNode::TVar {
                name: self.unsigned(),
                index: self.signed(),
            },
            _ => panic!("logic.bin holds an unknown type node"),
        }
    }

    fn term_node(&mut self) -> TermNode {
        match self.unsigned() {
            0 => TermNode::Const {
                name: self.unsigned(),
                typ: self.unsigned(),
            },
            1 => TermNode::Free {
                name: self.unsigned(),
                typ: self.unsigned(),
            },
            2 => TermNode::Var {
                name: self.unsigned(),
                index: self.signed(),
                typ: self.unsigned(),
            },
            3 => TermNode::Bound {
                index: self.signed(),
            },
            4 => TermNode::Abs {
                name: self.unsigned(),
                typ: self.unsigned(),
                body: self.unsigned(),
            },
            5 => TermNode::App {
                function: self.unsigned(),
                argument: self.unsigned(),
            },
            _ => panic!("logic.bin holds an unknown term node"),
        }
    }
}

fn decode(bytes: &[u8]) -> LogicData {
    let mut reader = Reader {
        bytes,
        position: 0,
        table: Vec::new(),
    };
    reader.table = reader.array(|reader| {
        let length = reader.length();
        let start = reader.position;
        reader.position += length;
        let text = reader
            .bytes
            .get(start..reader.position)
            .expect("logic.bin is truncated");
        String::from_utf8(text.to_vec()).expect("logic.bin holds a string that isn't UTF-8")
    });
    let string_count = reader.length();
    let pair = |reader: &mut Reader| (reader.string(), reader.string());
    let data = LogicData {
        strings: reader.table[..string_count].to_vec(),
        types: reader.array(Reader::type_node),
        terms: reader.array(Reader::term_node),
        thms: reader.ids(),
        consts: reader.array(|reader| ConstEntry {
            name: reader.string(),
            typ: reader.unsigned(),
            abbreviation: reader.boolean().then(|| reader.unsigned()),
        }),
        names: reader.array(pair),
        facts: reader.array(|reader| Fact {
            name: reader.string(),
            thms: reader.ids(),
        }),
        fact_names: reader.array(pair),
        simps: reader.ids(),
        congs: reader.array(|reader| Cong {
            is_const: reader.boolean(),
            name: reader.string(),
            rule: reader.unsigned(),
        }),
        weak_congs: reader.array(|reader| WeakCong {
            is_const: reader.boolean(),
            name: reader.string(),
        }),
        simprocs: reader.array(|reader| Simproc {
            name: reader.string(),
            lhss: reader.ids(),
        }),
        loopers: reader.strings(),
        unsafe_solvers: reader.strings(),
        safe_solvers: reader.strings(),
        claset: Claset {
            safe_is: reader.array(Reader::rule),
            safe_es: reader.array(Reader::rule),
            unsafe_is: reader.array(Reader::rule),
            unsafe_es: reader.array(Reader::rule),
            swrappers: reader.strings(),
            uwrappers: reader.strings(),
            safe0: reader.pair(Reader::item),
            safep: reader.pair(Reader::item),
            r#unsafe: reader.pair(Reader::item),
            dup: reader.pair(Reader::item),
            extra: reader.pair(Reader::extra_item),
        },
        context_rules: ContextRules {
            bang: reader.pair(Reader::extra_item),
            plain: reader.pair(Reader::extra_item),
        },
    };
    assert_eq!(
        reader.position,
        bytes.len(),
        "logic.bin has bytes after the logic"
    );
    data
}

#[cfg(test)]
mod tests {
    use std::fmt::Write;

    use super::*;

    /// Writes the data as JSON.stringify writes the LogicJson it was encoded from.
    struct Json(String);

    impl Json {
        fn raw(&mut self, text: &str) {
            self.0.push_str(text);
        }

        fn value(&mut self, value: impl std::fmt::Display) {
            write!(self.0, "{value}").expect("writing to a String succeeds");
        }

        fn string(&mut self, text: &str) {
            self.0.push('"');
            for character in text.chars() {
                match character {
                    '"' => self.raw("\\\""),
                    '\\' => self.raw("\\\\"),
                    '\u{8}' => self.raw("\\b"),
                    '\u{c}' => self.raw("\\f"),
                    '\n' => self.raw("\\n"),
                    '\r' => self.raw("\\r"),
                    '\t' => self.raw("\\t"),
                    control if u32::from(control) < 0x20 => {
                        write!(self.0, "\\u{:04x}", u32::from(control))
                            .expect("writing to a String succeeds");
                    }
                    other => self.0.push(other),
                }
            }
            self.0.push('"');
        }

        fn array<Item>(&mut self, items: &[Item], mut write_item: impl FnMut(&mut Self, &Item)) {
            self.raw("[");
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    self.raw(",");
                }
                write_item(self, item);
            }
            self.raw("]");
        }

        fn key(&mut self, key: &str) {
            if !self.0.ends_with('{') {
                self.raw(",");
            }
            self.string(key);
            self.raw(":");
        }

        fn ids(&mut self, ids: &[u32]) {
            self.array(ids, |json, id| json.value(id));
        }

        fn strings(&mut self, texts: &[String]) {
            self.array(texts, |json, text| json.string(text));
        }

        fn pairs(&mut self, pairs: &[(String, String)]) {
            self.array(pairs, |json, pair| {
                json.raw("[");
                json.string(&pair.0);
                json.raw(",");
                json.string(&pair.1);
                json.raw("]");
            });
        }

        fn rules(&mut self, rules: &[LogicRule]) {
            self.array(rules, |json, rule| {
                json.raw("[");
                json.value(rule.rule);
                json.raw(",");
                json.value(rule.internal);
                json.raw(",");
                json.ids(&rule.swapped);
                json.raw(",");
                json.value(rule.dup);
                json.raw(",");
                json.ids(&rule.dup_swapped);
                json.raw("]");
            });
        }

        fn pair<Item>(
            &mut self,
            pair: &NetPair<Item>,
            mut write_item: impl FnMut(&mut Self, &Item),
        ) {
            self.raw("[");
            self.array(&pair.intro, &mut write_item);
            self.raw(",");
            self.array(&pair.elim, &mut write_item);
            self.raw("]");
        }

        fn items(&mut self, pair: &NetPair<NetItem>) {
            self.pair(pair, |json, item| {
                write!(
                    json.0,
                    "[{},{},{}]",
                    item.tag,
                    u8::from(item.is_elim),
                    item.rule
                )
                .expect("writing to a String succeeds");
            });
        }

        fn extra_items(&mut self, pair: &NetPair<ExtraNetItem>) {
            self.pair(pair, |json, item| {
                write!(
                    json.0,
                    "[{},{},{},{}]",
                    item.weight,
                    item.tag,
                    u8::from(item.is_elim),
                    item.rule
                )
                .expect("writing to a String succeeds");
            });
        }
    }

    fn to_json(data: &LogicData) -> String {
        let mut json = Json(String::from("{"));
        json.key("strings");
        json.strings(&data.strings);
        json.key("types");
        json.array(&data.types, |json, node| {
            match node {
                TypeNode::Type { name, args } => {
                    write!(json.0, "[0,{name}").expect("writing to a String succeeds");
                    for arg in args {
                        write!(json.0, ",{arg}").expect("writing to a String succeeds");
                    }
                }
                TypeNode::TFree { name } => {
                    write!(json.0, "[1,{name}").expect("writing to a String succeeds");
                }
                TypeNode::TVar { name, index } => {
                    write!(json.0, "[2,{name},{index}").expect("writing to a String succeeds");
                }
            }
            json.raw("]");
        });
        json.key("terms");
        json.array(&data.terms, |json, node| {
            match node {
                TermNode::Const { name, typ } => write!(json.0, "[0,{name},{typ}]"),
                TermNode::Free { name, typ } => write!(json.0, "[1,{name},{typ}]"),
                TermNode::Var { name, index, typ } => write!(json.0, "[2,{name},{index},{typ}]"),
                TermNode::Bound { index } => write!(json.0, "[3,{index}]"),
                TermNode::Abs { name, typ, body } => write!(json.0, "[4,{name},{typ},{body}]"),
                TermNode::App { function, argument } => {
                    write!(json.0, "[5,{function},{argument}]")
                }
            }
            .expect("writing to a String succeeds");
        });
        json.key("thms");
        json.ids(&data.thms);
        json.key("consts");
        json.array(&data.consts, |json, entry| {
            json.raw("[");
            json.string(&entry.name);
            json.raw(",");
            json.value(entry.typ);
            if let Some(abbreviation) = entry.abbreviation {
                json.raw(",");
                json.value(abbreviation);
            }
            json.raw("]");
        });
        json.key("names");
        json.pairs(&data.names);
        json.key("facts");
        json.array(&data.facts, |json, fact| {
            json.raw("[");
            json.string(&fact.name);
            json.raw(",");
            json.ids(&fact.thms);
            json.raw("]");
        });
        json.key("factNames");
        json.pairs(&data.fact_names);
        json.key("simps");
        json.ids(&data.simps);
        json.key("congs");
        json.array(&data.congs, |json, cong| {
            json.raw("[");
            json.value(cong.is_const);
            json.raw(",");
            json.string(&cong.name);
            json.raw(",");
            json.value(cong.rule);
            json.raw("]");
        });
        json.key("weakCongs");
        json.array(&data.weak_congs, |json, cong| {
            json.raw("[");
            json.value(cong.is_const);
            json.raw(",");
            json.string(&cong.name);
            json.raw("]");
        });
        json.key("simprocs");
        json.array(&data.simprocs, |json, simproc| {
            json.raw("[");
            json.string(&simproc.name);
            json.raw(",");
            json.ids(&simproc.lhss);
            json.raw("]");
        });
        json.key("loopers");
        json.strings(&data.loopers);
        json.key("unsafeSolvers");
        json.strings(&data.unsafe_solvers);
        json.key("safeSolvers");
        json.strings(&data.safe_solvers);
        json.key("claset");
        json.raw("{");
        json.key("safeIs");
        json.rules(&data.claset.safe_is);
        json.key("safeEs");
        json.rules(&data.claset.safe_es);
        json.key("unsafeIs");
        json.rules(&data.claset.unsafe_is);
        json.key("unsafeEs");
        json.rules(&data.claset.unsafe_es);
        json.key("swrappers");
        json.strings(&data.claset.swrappers);
        json.key("uwrappers");
        json.strings(&data.claset.uwrappers);
        json.key("safe0");
        json.items(&data.claset.safe0);
        json.key("safep");
        json.items(&data.claset.safep);
        json.key("unsafe");
        json.items(&data.claset.r#unsafe);
        json.key("dup");
        json.items(&data.claset.dup);
        json.key("extra");
        json.extra_items(&data.claset.extra);
        json.raw("}");
        json.key("contextRules");
        json.raw("{");
        json.key("bang");
        json.extra_items(&data.context_rules.bang);
        json.key("plain");
        json.extra_items(&data.context_rules.plain);
        json.raw("}}");
        json.0
    }

    /// FNV-1a, 64 bits, in hexadecimal, as the script computed it.
    fn digest(text: &str) -> String {
        let hash = text.bytes().fold(0xcbf2_9ce4_8422_2325_u64, |hash, byte| {
            (hash ^ u64::from(byte)).wrapping_mul(0x0100_0000_01b3)
        });
        format!("{hash:016x}")
    }

    #[test]
    fn the_binary_is_the_json_it_was_exported_from() {
        assert_eq!(
            digest(&to_json(logic_data())),
            include_str!("../../data/logic.digest").trim()
        );
    }
}
