//! TLC's Java overrides of a module's operators, as `src/java-overrides.ts` reads them: the
//! public static methods of the class file named after the module, beside the spec, each of which
//! replaces the operator of the same name and arity with the constant value it returns.

use std::rc::Rc;

use crate::ast::{Definition, DefinitionKind, Expr, Expression, ExpressionKind, Location, Module};
use crate::environment::ClassLoader;
use crate::errors::FrontError;
use crate::resolve::Result;

/// A public static method of the class named after a module, which TLC reports as it loads the
/// class, with whether it overrides an operator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JavaOverride {
    pub module: String,
    pub operator: String,
    /// `Method#toString`, which TLC prints as the signature.
    pub signature: String,
    pub is_matched: bool,
}

#[derive(Clone, Default)]
struct PoolEntry {
    tag: u8,
    text: String,
    value: i32,
    first: u16,
    second: u16,
}

struct JavaMethod {
    name: String,
    arity: usize,
    signature: String,
    code: Option<Vec<u8>>,
}

const CLASS_MAGIC: u32 = 0xcafe_babe;
const ACCESS_PUBLIC: u16 = 0x0001;
const ACCESS_STATIC: u16 = 0x0008;
const VALUE_PACKAGE: &str = "tlc2/value/impl/";

// The constant pool tags of the JVM specification, section 4.4.
const UTF8: u8 = 1;
const INTEGER: u8 = 3;
const FLOAT: u8 = 4;
const LONG: u8 = 5;
const DOUBLE: u8 = 6;
const CLASS: u8 = 7;
const STRING: u8 = 8;
const FIELD_REF: u8 = 9;
const METHOD_REF: u8 = 10;
const INTERFACE_METHOD_REF: u8 = 11;
const NAME_AND_TYPE: u8 = 12;
const METHOD_HANDLE: u8 = 15;
const METHOD_TYPE: u8 = 16;
const MODULE: u8 = 19;
const PACKAGE: u8 = 20;
const DYNAMIC: u8 = 17;
const INVOKE_DYNAMIC: u8 = 18;

/// The newest class file version the front end reads, Java 25's.
const MAXIMUM_MAJOR_VERSION: u16 = 69;
/// ACC_INTERFACE, ACC_ABSTRACT, ACC_ANNOTATION, ACC_ENUM and ACC_MODULE: a class that isn't a
/// plain one.
const UNPLAIN_CLASS: u16 = 0x0200 | 0x0400 | 0x2000 | 0x4000 | 0x8000;
/// The Java names TLC maps to an operator's (`TLARegistry.mapName`), which its standard modules'
/// classes register: an override of one of these names overrides that operator.
const REGISTERED_NAMES: [&str; 18] = [
    "BagCup",
    "BagDiff",
    "CombineFcn",
    "Concat",
    "Divide",
    "DotDot",
    "Expt",
    "GEQ",
    "GT",
    "LE",
    "LT",
    "MakeFcn",
    "Minus",
    "Mod",
    "Neg",
    "Plus",
    "SqSubseteq",
    "Times",
];

// The modifiers Method#toString prints, in the order of Modifier#toString.
const METHOD_MODIFIERS: [(u16, &str); 9] = [
    (0x0001, "public"),
    (0x0004, "protected"),
    (0x0002, "private"),
    (0x0400, "abstract"),
    (0x0008, "static"),
    (0x0010, "final"),
    (0x0020, "synchronized"),
    (0x0100, "native"),
    (0x0800, "strictfp"),
];

fn not_yet(reason: &str) -> FrontError {
    FrontError::NotYet(reason.to_owned())
}

struct Reader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Reader<'a> {
    fn bytes(&mut self, length: usize) -> Result<&'a [u8]> {
        let slice = self
            .bytes
            .get(self.offset..self.offset + length)
            .ok_or_else(|| not_yet("a Java class file that ends early"))?;
        self.offset += length;
        Ok(slice)
    }

    fn u8(&mut self) -> Result<u8> {
        Ok(self.bytes(1)?[0])
    }

    fn u16(&mut self) -> Result<u16> {
        let bytes = self.bytes(2)?;
        Ok(u16::from_be_bytes([bytes[0], bytes[1]]))
    }

    fn u32(&mut self) -> Result<u32> {
        let bytes = self.bytes(4)?;
        Ok(u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }
}

// The Java names of the types a method descriptor lists.
fn get_type_names(descriptor: &str) -> Result<Vec<String>> {
    let mut names = Vec::new();
    let mut characters = descriptor.chars().peekable();
    while characters.peek().is_some() {
        let mut dimensions = 0;
        while characters.next_if_eq(&'[').is_some() {
            dimensions += 1;
        }
        let name = match characters.next() {
            Some('L') => characters
                .by_ref()
                .take_while(|character| *character != ';')
                .collect::<String>()
                .replace('/', "."),
            Some('B') => "byte".to_owned(),
            Some('C') => "char".to_owned(),
            Some('D') => "double".to_owned(),
            Some('F') => "float".to_owned(),
            Some('I') => "int".to_owned(),
            Some('J') => "long".to_owned(),
            Some('S') => "short".to_owned(),
            Some('Z') => "boolean".to_owned(),
            Some('V') => "void".to_owned(),
            _ => {
                return Err(not_yet(
                    "a Java method descriptor the front end doesn't read",
                ));
            }
        };
        names.push(format!("{name}{}", "[]".repeat(dimensions)));
    }
    Ok(names)
}

/// The annotations `Method#getAnnotation` finds that make TLC skip a method of the class named after
/// a module, which only a `TLCOverrides` index loads.
const SKIPPING_ANNOTATIONS: [&str; 2] = [
    "Ltlc2/overrides/TLAPlusOperator;",
    "Ltlc2/overrides/Evaluation;",
];

// Reads past an annotation's element_value (JVM specification, section 4.7.16.1).
fn skip_element_value(reader: &mut Reader) -> Result<()> {
    match reader.u8()? {
        b'e' => {
            reader.u32()?;
        }
        b'@' => {
            read_annotation(reader)?;
        }
        b'[' => {
            for _ in 0..reader.u16()? {
                skip_element_value(reader)?;
            }
        }
        _ => {
            reader.u16()?;
        }
    }
    Ok(())
}

// An annotation's type, past its elements.
fn read_annotation(reader: &mut Reader) -> Result<u16> {
    let type_index = reader.u16()?;
    for _ in 0..reader.u16()? {
        reader.u16()?;
        skip_element_value(reader)?;
    }
    Ok(type_index)
}

fn get_entry(pool: &[PoolEntry], index: u16) -> Result<&PoolEntry> {
    pool.get(index as usize)
        .ok_or_else(|| not_yet("a Java class file's constant out of its pool"))
}

fn get_class_name(pool: &[PoolEntry], index: u16) -> Result<String> {
    Ok(get_entry(pool, get_entry(pool, index)?.first)?.text.clone())
}

// A class file's constant pool (JVM specification, section 4.4).
fn read_pool(reader: &mut Reader) -> Result<Vec<PoolEntry>> {
    let pool_size = reader.u16()?;
    let mut pool = vec![PoolEntry::default(); pool_size as usize];
    let mut index = 1;
    while index < pool_size {
        let tag = reader.u8()?;
        let mut entry = PoolEntry {
            tag,
            ..PoolEntry::default()
        };
        match tag {
            UTF8 => {
                let length = reader.u16()? as usize;
                entry.text = String::from_utf8(reader.bytes(length)?.to_vec())
                    .map_err(|_| not_yet("a Java class file's modified UTF-8"))?;
            }
            INTEGER => entry.value = reader.u32()? as i32,
            FLOAT => {
                reader.u32()?;
            }
            LONG | DOUBLE => {
                reader.bytes(8)?;
                pool[index as usize] = entry;
                index += 2;
                continue;
            }
            CLASS | STRING | METHOD_TYPE | MODULE | PACKAGE => entry.first = reader.u16()?,
            METHOD_HANDLE => {
                reader.u8()?;
                entry.first = reader.u16()?;
            }
            FIELD_REF | METHOD_REF | INTERFACE_METHOD_REF | NAME_AND_TYPE | DYNAMIC
            | INVOKE_DYNAMIC => {
                entry.first = reader.u16()?;
                entry.second = reader.u16()?;
            }
            _ => {
                return Err(not_yet(
                    "a Java class file's constant the front end doesn't read",
                ));
            }
        }
        pool[index as usize] = entry;
        index += 1;
    }
    Ok(pool)
}

// The public static methods of a class file and their bytecode, in the order of the class file.
fn read_class_file(bytes: &[u8], has_index: bool) -> Result<(Vec<PoolEntry>, Vec<JavaMethod>)> {
    let mut reader = Reader { bytes, offset: 0 };
    if reader.u32()? != CLASS_MAGIC {
        return Err(not_yet("a module override that isn't a class file"));
    }
    reader.u16()?;
    if reader.u16()? > MAXIMUM_MAJOR_VERSION {
        return Err(not_yet(
            "a Java class file of a version the front end doesn't read",
        ));
    }
    let pool = read_pool(&mut reader)?;
    // Java runs a class's static initializer, its fields' and its superclasses', before it calls
    // an override, which the front end doesn't run: it reads only a plain class with none.
    if reader.u16()? & UNPLAIN_CLASS != 0 {
        return Err(not_yet("a Java override class that isn't a plain class"));
    }
    let class_name = get_class_name(&pool, reader.u16()?)?.replace('/', ".");
    if get_class_name(&pool, reader.u16()?)? != "java/lang/Object" {
        return Err(not_yet("a Java override class with a superclass"));
    }
    if reader.u16()? != 0 {
        return Err(not_yet(
            "a Java override class that implements an interface",
        ));
    }
    if reader.u16()? != 0 {
        return Err(not_yet("a Java override class with fields"));
    }
    let mut methods = Vec::new();
    for _ in 0..reader.u16()? {
        let access = reader.u16()?;
        let name = get_entry(&pool, reader.u16()?)?.text.clone();
        let descriptor = get_entry(&pool, reader.u16()?)?.text.clone();
        if name == "<clinit>" {
            return Err(not_yet("a Java override class with a static initializer"));
        }
        let mut code = None;
        let mut exceptions = Vec::new();
        let mut is_annotated = false;
        let mut is_skipped = false;
        for _ in 0..reader.u16()? {
            let attribute = get_entry(&pool, reader.u16()?)?.text.clone();
            let length = reader.u32()? as usize;
            let mut body = Reader {
                bytes: reader.bytes(length)?,
                offset: 0,
            };
            if attribute == "RuntimeVisibleAnnotations" {
                for _ in 0..body.u16()? {
                    let annotation = get_entry(&pool, read_annotation(&mut body)?)?;
                    is_skipped |= SKIPPING_ANNOTATIONS.contains(&annotation.text.as_str());
                }
            }
            if attribute.contains("Annotation") {
                is_annotated = true;
            } else if attribute == "Code" {
                // max_stack and max_locals come before the length of the bytecode.
                body.bytes(4)?;
                let length = body.u32()? as usize;
                code = Some(body.bytes(length)?.to_vec());
            } else if attribute == "Exceptions" {
                for _ in 0..body.u16()? {
                    exceptions.push(get_class_name(&pool, body.u16()?)?.replace('/', "."));
                }
            }
        }
        // `processModuleOverrides` skips a method annotated as an operator a TLCOverrides index
        // loads, which a class TLC finds beside the spec could be.
        if is_skipped {
            if has_index {
                return Err(not_yet(
                    "a Java override class TLC may load through a TLCOverrides index",
                ));
            }
            continue;
        }
        if is_annotated {
            return Err(not_yet("a Java override class with annotations"));
        }
        if access & ACCESS_PUBLIC == 0 || access & ACCESS_STATIC == 0 {
            continue;
        }
        let end = descriptor
            .find(')')
            .ok_or_else(|| not_yet("a Java method descriptor without parameters"))?;
        let parameters = get_type_names(&descriptor[1..end])?;
        let returned = get_type_names(&descriptor[end + 1..])?
            .into_iter()
            .next()
            .unwrap_or_default();
        let modifiers: Vec<&str> = METHOD_MODIFIERS
            .iter()
            .filter(|(flag, _)| access & flag != 0)
            .map(|(_, modifier)| *modifier)
            .collect();
        let throws = if exceptions.is_empty() {
            String::new()
        } else {
            format!(" throws {}", exceptions.join(","))
        };
        methods.push(JavaMethod {
            arity: parameters.len(),
            signature: format!(
                "{} {returned} {class_name}.{name}({}){throws}",
                modifiers.join(" "),
                parameters.join(",")
            ),
            name,
            code,
        });
    }
    for _ in 0..reader.u16()? {
        let attribute = get_entry(&pool, reader.u16()?)?.text.clone();
        let length = reader.u32()? as usize;
        reader.bytes(length)?;
        if attribute.contains("Annotation") {
            return Err(not_yet("a Java override class with annotations"));
        }
    }
    // TLC loads every public static method of a name, the one it loads last overriding the
    // others, in the order the JVM lists them, and maps a registered name to an operator's.
    for (position, method) in methods.iter().enumerate() {
        if methods[..position]
            .iter()
            .any(|other| other.name == method.name)
        {
            return Err(not_yet("a Java override class with methods of one name"));
        }
        if REGISTERED_NAMES.contains(&method.name.as_str()) {
            return Err(not_yet(
                "a Java override of a name TLC maps to an operator's",
            ));
        }
    }
    Ok((pool, methods))
}

// A class and a member of it that a constant names, with the member's descriptor.
fn get_member(pool: &[PoolEntry], index: u16) -> Result<(String, String)> {
    let reference = get_entry(pool, index)?;
    let name_and_type = get_entry(pool, reference.second)?;
    Ok((
        get_class_name(pool, reference.first)?,
        format!(
            "{}{}",
            get_entry(pool, name_and_type.first)?.text,
            get_entry(pool, name_and_type.second)?.text
        ),
    ))
}

enum Item {
    Integer(i32),
    Text(String),
    Literal(Expr),
    // An object `new` made: its class, and the literal its constructor gave it.
    Object(String, Option<Expr>),
}

fn literal(kind: ExpressionKind, location: &Location) -> Expr {
    Rc::new(Expression::new(kind, location.clone()))
}

// Runs the bytecode of an override that returns a constant TLC value, such as
// BoolValue.ValTrue, IntValue.gen(3), or new StringValue("a"), and returns that value as a literal.
// One that computes its value TLC runs as Java, which the front end doesn't. The instructions it
// runs, from the first to the first return, don't branch or throw, so no exception handler runs.
fn get_returned_literal(
    method: &JavaMethod,
    pool: &[PoolEntry],
    location: &Location,
) -> Result<Expr> {
    let unsupported = || not_yet("a Java override that computes its value");
    let code = method.code.as_ref().ok_or_else(unsupported)?;
    let mut stack: Vec<Item> = Vec::new();
    let constant = |index: u16| -> Result<Item> {
        let entry = get_entry(pool, index)?;
        match entry.tag {
            INTEGER => Ok(Item::Integer(entry.value)),
            STRING => Ok(Item::Text(get_entry(pool, entry.first)?.text.clone())),
            _ => Err(unsupported()),
        }
    };
    let mut offset = 0;
    while offset < code.len() {
        let opcode = code[offset];
        let index = || -> Result<u16> {
            let bytes = code.get(offset + 1..offset + 3).ok_or_else(unsupported)?;
            Ok(u16::from_be_bytes([bytes[0], bytes[1]]))
        };
        match opcode {
            // iconst_m1 to iconst_5
            0x02..=0x08 => {
                stack.push(Item::Integer(i32::from(opcode) - 3));
                offset += 1;
            }
            // bipush
            0x10 => {
                let byte = *code.get(offset + 1).ok_or_else(unsupported)?;
                stack.push(Item::Integer(i32::from(byte as i8)));
                offset += 2;
            }
            // sipush
            0x11 => {
                stack.push(Item::Integer(i32::from(index()? as i16)));
                offset += 3;
            }
            // ldc
            0x12 => {
                let byte = *code.get(offset + 1).ok_or_else(unsupported)?;
                stack.push(constant(u16::from(byte))?);
                offset += 2;
            }
            // ldc_w
            0x13 => {
                stack.push(constant(index()?)?);
                offset += 3;
            }
            // dup: only of an object, as `new` makes one for its constructor.
            0x59 => {
                let Some(Item::Object(class, None)) = stack.last() else {
                    return Err(unsupported());
                };
                let copy = Item::Object(class.clone(), None);
                stack.push(copy);
                offset += 1;
            }
            // getstatic
            0xb2 => {
                let (class, field) = get_member(pool, index()?)?;
                let name = match (class.strip_prefix(VALUE_PACKAGE), field.as_str()) {
                    (Some("BoolValue"), "ValTrueLtlc2/value/impl/BoolValue;") => "TRUE",
                    (Some("BoolValue"), "ValFalseLtlc2/value/impl/BoolValue;") => "FALSE",
                    _ => return Err(unsupported()),
                };
                stack.push(Item::Literal(literal(
                    ExpressionKind::Identifier {
                        name: Rc::from(name),
                        spelling: None,
                        selector_ranges: None,
                    },
                    location,
                )));
                offset += 3;
            }
            // invokestatic IntValue.gen
            0xb8 => {
                let (class, callee) = get_member(pool, index()?)?;
                let Some(Item::Integer(value)) = stack.pop() else {
                    return Err(unsupported());
                };
                if class.strip_prefix(VALUE_PACKAGE) != Some("IntValue")
                    || callee != "gen(I)Ltlc2/value/impl/IntValue;"
                {
                    return Err(unsupported());
                }
                stack.push(Item::Literal(literal(
                    ExpressionKind::Number {
                        value: f64::from(value),
                        text: Rc::from(value.to_string()),
                    },
                    location,
                )));
                offset += 3;
            }
            // new
            0xbb => {
                stack.push(Item::Object(get_class_name(pool, index()?)?, None));
                offset += 3;
            }
            // invokespecial StringValue.<init>(String)
            0xb7 => {
                let (class, constructor) = get_member(pool, index()?)?;
                let (Some(Item::Text(text)), Some(Item::Object(..))) = (stack.pop(), stack.pop())
                else {
                    return Err(unsupported());
                };
                if class.strip_prefix(VALUE_PACKAGE) != Some("StringValue")
                    || constructor != "<init>(Ljava/lang/String;)V"
                {
                    return Err(unsupported());
                }
                let value = literal(
                    ExpressionKind::String {
                        value: Rc::from(text),
                    },
                    location,
                );
                match stack.last_mut() {
                    Some(Item::Object(_, slot @ None)) => *slot = Some(value),
                    _ => return Err(unsupported()),
                }
                offset += 3;
            }
            // areturn, of the only value
            0xb0 => {
                let value = match stack.pop() {
                    Some(Item::Literal(value)) | Some(Item::Object(_, Some(value))) => value,
                    _ => return Err(unsupported()),
                };
                if !stack.is_empty() {
                    return Err(unsupported());
                }
                return Ok(value);
            }
            _ => return Err(unsupported()),
        }
    }
    Err(unsupported())
}

/// The package path of the index class TLC loads (`TLAClass.loadClass`).
pub const INDEX_CLASS: &str = "tlc2/overrides/TLCOverrides";
const ACCESS_FINAL: u16 = 0x0010;
const OPERATOR_ANNOTATION: &str = "Ltlc2/overrides/TLAPlusOperator;";
const EVALUATION_ANNOTATION: &str = "Ltlc2/overrides/Evaluation;";

// What an annotation's element gives: a string or a number, or a value the front end doesn't read.
enum ElementValue {
    Text(String),
    Number(i32),
    Other,
}

// A method of a class TLC reads through a TLCOverrides index: its access flags, its name and
// descriptor, its bytecode, and each runtime-visible annotation's type with its elements.
struct IndexedMethod {
    access: u16,
    name: String,
    descriptor: String,
    code: Option<Vec<u8>>,
    annotations: Vec<(String, Vec<(String, ElementValue)>)>,
}

fn read_element_value(reader: &mut Reader, pool: &[PoolEntry]) -> Result<ElementValue> {
    let tag = reader.u8()?;
    Ok(match tag {
        b's' => ElementValue::Text(get_entry(pool, reader.u16()?)?.text.clone()),
        b'Z' | b'I' | b'B' | b'C' | b'S' => {
            ElementValue::Number(get_entry(pool, reader.u16()?)?.value)
        }
        b'e' => {
            reader.u32()?;
            ElementValue::Other
        }
        b'@' => {
            read_annotation(reader)?;
            ElementValue::Other
        }
        b'[' => {
            for _ in 0..reader.u16()? {
                read_element_value(reader, pool)?;
            }
            ElementValue::Other
        }
        _ => {
            reader.u16()?;
            ElementValue::Other
        }
    })
}

// A plain class with no superclass, as TLC reads it through a TLCOverrides index.
struct IndexedClass {
    pool: Vec<PoolEntry>,
    access: u16,
    interfaces: Vec<String>,
    has_fields: bool,
    methods: Vec<IndexedMethod>,
}

fn read_indexed_class(bytes: &[u8]) -> Result<IndexedClass> {
    let mut reader = Reader { bytes, offset: 0 };
    if reader.u32()? != CLASS_MAGIC {
        return Err(not_yet(
            "a TLCOverrides index that lists a class that isn't a class file",
        ));
    }
    reader.u16()?;
    if reader.u16()? > MAXIMUM_MAJOR_VERSION {
        return Err(not_yet(
            "a Java class file of a version the front end doesn't read",
        ));
    }
    let pool = read_pool(&mut reader)?;
    let access = reader.u16()?;
    if access & UNPLAIN_CLASS != 0 {
        return Err(not_yet(
            "a TLCOverrides index of a class that isn't a plain class",
        ));
    }
    reader.u16()?;
    if get_class_name(&pool, reader.u16()?)? != "java/lang/Object" {
        return Err(not_yet("a TLCOverrides index of a class with a superclass"));
    }
    let mut interfaces = Vec::new();
    for _ in 0..reader.u16()? {
        interfaces.push(get_class_name(&pool, reader.u16()?)?);
    }
    let field_count = reader.u16()?;
    for _ in 0..field_count {
        reader.bytes(6)?;
        for _ in 0..reader.u16()? {
            reader.u16()?;
            let length = reader.u32()? as usize;
            reader.bytes(length)?;
        }
    }
    let mut methods = Vec::new();
    for _ in 0..reader.u16()? {
        let access = reader.u16()?;
        let name = get_entry(&pool, reader.u16()?)?.text.clone();
        let descriptor = get_entry(&pool, reader.u16()?)?.text.clone();
        let mut code = None;
        let mut annotations = Vec::new();
        for _ in 0..reader.u16()? {
            let attribute = get_entry(&pool, reader.u16()?)?.text.clone();
            let length = reader.u32()? as usize;
            let mut body = Reader {
                bytes: reader.bytes(length)?,
                offset: 0,
            };
            if attribute == "RuntimeVisibleAnnotations" {
                for _ in 0..body.u16()? {
                    let annotation = get_entry(&pool, body.u16()?)?.text.clone();
                    let mut elements = Vec::new();
                    for _ in 0..body.u16()? {
                        let element = get_entry(&pool, body.u16()?)?.text.clone();
                        elements.push((element, read_element_value(&mut body, &pool)?));
                    }
                    annotations.push((annotation, elements));
                }
            } else if attribute == "Code" {
                body.bytes(4)?;
                let length = body.u32()? as usize;
                code = Some(body.bytes(length)?.to_vec());
            }
        }
        methods.push(IndexedMethod {
            access,
            name,
            descriptor,
            code,
            annotations,
        });
    }
    Ok(IndexedClass {
        pool,
        access,
        interfaces,
        has_fields: field_count > 0,
        methods,
    })
}

// The number an instruction pushes and the instruction after it, where it pushes a small one.
fn read_pushed(code: &[u8], at: usize) -> Option<(i32, usize)> {
    match *code.get(at)? {
        opcode @ 0x03..=0x08 => Some((i32::from(opcode) - 3, at + 1)),
        0x10 => Some((i32::from(*code.get(at + 1)? as i8), at + 2)),
        0x11 => Some((
            i32::from(i16::from_be_bytes([*code.get(at + 1)?, *code.get(at + 2)?])),
            at + 3,
        )),
        _ => None,
    }
}

// The classes an index's `get` returns, where its bytecode is an array of class literals it
// returns as it builds it: `return new Class[] { A.class, ... };`.
fn get_listed_classes(pool: &[PoolEntry], code: &[u8]) -> Option<Vec<String>> {
    let (count, mut at) = read_pushed(code, 0)?;
    let index = |at: usize| u16::from_be_bytes([code[at], code[at + 1]]);
    if code.get(at) != Some(&0xbd)
        || code.len() < at + 3
        || get_class_name(pool, index(at + 1)).ok()? != "java/lang/Class"
    {
        return None;
    }
    at += 3;
    let mut classes = Vec::new();
    for position in 0..count {
        if code.get(at) != Some(&0x59) {
            return None;
        }
        let (pushed, after) = read_pushed(code, at + 1)?;
        let (constant, after) = match code.get(after)? {
            0x12 => (u16::from(*code.get(after + 1)?), after + 2),
            0x13 if code.len() >= after + 3 => (index(after + 1), after + 3),
            _ => return None,
        };
        let entry = get_entry(pool, constant).ok()?;
        if pushed != position || entry.tag != CLASS || code.get(after) != Some(&0x53) {
            return None;
        }
        classes.push(get_entry(pool, entry.first).ok()?.text.clone());
        at = after + 1;
    }
    (code[at..] == [0xb0]).then_some(classes)
}

/// The operators the `tlc2.overrides.TLCOverrides` index TLC loads replaces (`processSpec`), each
/// as its module, its identifier and the method's arity where TLC checks it, where TLC prints
/// nothing of them and runs none of their Java: the index is a plain class whose `get` returns class literals, and each method of those
/// classes annotated as an override is a `@TLAPlusOperator(warn = false)` or an
/// `@Evaluation(silent = true, warn = false)` TLC doesn't call as it loads it.
pub fn get_index_overrides(
    load_class: &ClassLoader,
) -> Result<Vec<(String, String, Option<usize>)>> {
    let Some(bytes) = load_class(INDEX_CLASS) else {
        return Ok(Vec::new());
    };
    let unsupported = || not_yet("a TLCOverrides index of Java overrides");
    let index = read_indexed_class(&bytes)?;
    let pool = &index.pool;
    let is_constructor_plain = |method: &IndexedMethod| {
        method.descriptor == "()V"
            && method.access & ACCESS_PUBLIC != 0
            && method.code.as_deref().is_some_and(|code| {
                code.len() == 5
                    && code[0] == 0x2a
                    && code[1] == 0xb7
                    && code[4] == 0xb1
                    && get_member(pool, u16::from_be_bytes([code[2], code[3]])).is_ok_and(
                        |(class, member)| class == "java/lang/Object" && member == "<init>()V",
                    )
            })
    };
    let listed = match &index.methods[..] {
        [first, second]
            if index.interfaces == ["tlc2/overrides/ITLCOverrides"] && !index.has_fields =>
        {
            let (constructor, get) = if first.name == "<init>" {
                (first, second)
            } else {
                (second, first)
            };
            let is_get = get.name == "get"
                && get.descriptor == "()[Ljava/lang/Class;"
                && get.access & ACCESS_PUBLIC != 0
                && get.access & ACCESS_STATIC == 0;
            if constructor.name != "<init>" || !is_constructor_plain(constructor) || !is_get {
                return Err(unsupported());
            }
            get.code
                .as_deref()
                .and_then(|code| get_listed_classes(pool, code))
                .ok_or_else(unsupported)?
        }
        _ => return Err(unsupported()),
    };
    let mut overrides = Vec::new();
    for class in listed {
        let bytes = load_class(&class).ok_or_else(unsupported)?;
        let class = read_indexed_class(&bytes)?;
        for method in &class.methods {
            for (annotation, elements) in &method.annotations {
                if SKIPPING_ANNOTATIONS.contains(&annotation.as_str())
                    || annotation == "Ltlc2/overrides/TLAPlusCallable;"
                {
                    let get_text = |wanted: &str| {
                        elements.iter().find_map(|(name, value)| match value {
                            ElementValue::Text(text) if name == wanted => Some(text.clone()),
                            _ => None,
                        })
                    };
                    let is_false = |wanted: &str| {
                        elements.iter().any(|(name, value)| {
                            name == wanted && matches!(value, ElementValue::Number(0))
                        })
                    };
                    let is_true = |wanted: &str| {
                        elements.iter().any(|(name, value)| {
                            name == wanted && matches!(value, ElementValue::Number(1))
                        })
                    };
                    // TLC fails to look up a method it can't reach, and calls a final one without
                    // parameters as it loads it (`MethodValue.get`).
                    let is_run_as_loaded = class.access & ACCESS_PUBLIC == 0
                        || method.access & ACCESS_PUBLIC == 0
                        || method.access & ACCESS_FINAL != 0;
                    // TLC rejects an evaluation of a name SANY builds in, which no identifier is.
                    let is_identifier = |name: &str| {
                        name.chars()
                            .all(|character| character.is_ascii_alphanumeric() || character == '_')
                    };
                    let module = get_text("module");
                    match annotation.as_str() {
                        // TLC prints nothing of an override that sets warn to false, and checks
                        // the method's arity against the operator's.
                        OPERATOR_ANNOTATION if is_false("warn") && !is_run_as_loaded => {
                            let (Some(module), Some(identifier)) = (module, get_text("identifier"))
                            else {
                                return Err(unsupported());
                            };
                            let end = method.descriptor.find(')').ok_or_else(unsupported)?;
                            let arity = get_type_names(&method.descriptor[1..end])?.len();
                            overrides.push((module, identifier, Some(arity)));
                        }
                        // An evaluation that is silent and sets warn to false prints nothing, and
                        // TLC replaces the operator whatever its arity.
                        EVALUATION_ANNOTATION
                            if is_true("silent") && is_false("warn") && !is_run_as_loaded =>
                        {
                            let (Some(module), Some(definition)) = (module, get_text("definition"))
                            else {
                                return Err(unsupported());
                            };
                            if !is_identifier(&definition) {
                                return Err(unsupported());
                            }
                            overrides.push((module, definition, None));
                        }
                        _ => return Err(unsupported()),
                    }
                }
            }
        }
    }
    Ok(overrides)
}

/// Whether TLC finds a `tlc2.overrides.TLCOverrides` index beside the spec or on the class path,
/// named as the class or at its package's path (`TLAClass.loadClass`).
pub fn has_index(load_class: &ClassLoader) -> bool {
    ["tlc2.overrides.TLCOverrides", "tlc2/overrides/TLCOverrides"]
        .iter()
        .any(|name| load_class(name).is_some())
}

/// `overrideDefinitions`: TLC loads a class named after each module and replaces each operator of
/// the module that the root module sees with the public static method of the same name and
/// arity. It reports whether each method matched an operator. TLC also loads the overrides a
/// `tlc2.overrides.TLCOverrides` index class lists (`has_index`).
pub fn override_definitions(
    module: &Rc<Module>,
    bytes: &[u8],
    is_root: bool,
    load_class: &ClassLoader,
) -> Result<(Rc<Module>, Vec<JavaOverride>)> {
    let (pool, methods) = read_class_file(bytes, has_index(load_class))?;
    let get_arity = |name: &str| {
        module
            .definitions
            .iter()
            .filter(|definition| is_root || !definition.is_hidden())
            .find(|definition| &*definition.name == name)
            .map(|definition| match &definition.kind {
                DefinitionKind::Operator { params, .. } => params.len(),
                DefinitionKind::Function { .. } => 0,
            })
    };
    let is_matched = |method: &JavaMethod| get_arity(&method.name) == Some(method.arity);
    let mut definitions = Vec::with_capacity(module.definitions.len());
    for definition in &module.definitions {
        let method = matches!(definition.kind, DefinitionKind::Operator { .. })
            .then(|| {
                methods
                    .iter()
                    .find(|method| *method.name == *definition.name && is_matched(method))
            })
            .flatten();
        // TLC evaluates each argument, in order, before it calls the method (`OpValue.eval`), so an
        // argument that fails or prints does so, which a literal in the operator's place skips.
        if method.is_some_and(|method| method.arity > 0) {
            return Err(not_yet(
                "a Java override with parameters, whose arguments TLC evaluates",
            ));
        }
        definitions.push(match method {
            Some(method) => Rc::new(Definition {
                body: get_returned_literal(method, &pool, &definition.location)?,
                ..(**definition).clone()
            }),
            None => definition.clone(),
        });
    }
    let overrides = methods
        .iter()
        .map(|method| JavaOverride {
            module: module.name.to_string(),
            operator: method.name.clone(),
            signature: method.signature.clone(),
            is_matched: is_matched(method),
        })
        .collect();
    Ok((
        Rc::new(Module {
            definitions,
            ..(**module).clone()
        }),
        overrides,
    ))
}
