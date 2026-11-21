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
const ACCESS_FINAL: u16 = 0x0010;
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

/// Whether TLC finds a `tlc2.overrides.TLCOverrides` index beside the spec or on the class path,
/// named as the class or at its package's path (`TLAClass.loadClass`).
pub fn has_index(load_class: &ClassLoader) -> bool {
    ["tlc2.overrides.TLCOverrides", "tlc2/overrides/TLCOverrides"]
        .iter()
        .any(|name| load_class(name).is_some())
}

/// A method of a class a `tlc2.overrides.TLCOverrides` index lists, annotated
/// `@TLAPlusOperator(identifier, module, warn = false)`, or `@Evaluation` or `@TLAPlusCallable`
/// with `definition` and `warn = false`: `processModuleOverrides` puts it in place of the body of
/// `module`'s definition of that name, if SANY loaded that module and it defines the name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexTarget {
    pub module: String,
    pub identifier: String,
    /// The `@TLAPlusOperator` method's number of parameters, which must be the operator's; an
    /// `@Evaluation` method replaces an operator of any arity.
    pub arity: Option<usize>,
    /// Whether TLC only calls the replacement when the model evaluates the operator, with
    /// nothing printed as it starts: a public method of a public class, which
    /// `MethodHandles.publicLookup` requires. `MethodValue.get` evaluates a final
    /// `@TLAPlusOperator` method without parameters as TLC starts.
    pub is_lazy: bool,
    /// Whether the method only makes a value or throws (`is_quiet_code`), so that a call TLC
    /// makes as it starts, whose value or exception it then drops, shows nothing.
    pub is_quiet: bool,
}

/// The methods an index class may call: `Class.forName` with the loader that loaded it, and
/// what wraps the `ClassNotFoundException` it declares. None of them prints or reads anything.
const INDEX_CALLS: [(&str, &str); 7] = [
    ("java/lang/Object", "<init>()V"),
    ("java/lang/Object", "getClass()Ljava/lang/Class;"),
    ("java/lang/Class", "getClassLoader()Ljava/lang/ClassLoader;"),
    (
        "java/lang/Class",
        "forName(Ljava/lang/String;)Ljava/lang/Class;",
    ),
    (
        "java/lang/Class",
        "forName(Ljava/lang/String;ZLjava/lang/ClassLoader;)Ljava/lang/Class;",
    ),
    (
        "java/lang/RuntimeException",
        "<init>(Ljava/lang/Throwable;)V",
    ),
    ("java/lang/RuntimeException", "<init>(Ljava/lang/String;)V"),
];

/// The annotations `processModuleOverrides` reads on each method of a class an index lists.
const INDEX_ANNOTATIONS: [&str; 3] = [
    "Ltlc2/overrides/TLAPlusOperator;",
    "Ltlc2/overrides/Evaluation;",
    "Ltlc2/overrides/TLAPlusCallable;",
];

/// The operators a `tlc2.overrides.TLCOverrides` index beside the spec can replace
/// (`processModuleOverrides`), or a decline where the front end can't tell them all.
/// `TLAClass.loadClass` loads the index at its package's path: a file named
/// `tlc2.overrides.TLCOverrides.class` only locates the directory the class loader then reads
/// at that path, and a class there named as TLC's built-in index loses to the jar's own.
/// `ITLCOverrides#get` runs as TLC starts, so the index may only build its array of classes from
/// class literals and `Class.forName` of string constants; any class it names must be beside
/// the spec, a plain class without a static initializer `Class.forName` runs, and any annotated
/// method of it must have `warn = false`, since TLC otherwise prints a message for it whether or
/// not the model ever evaluates the operator.
pub fn get_index_targets(load_class: &ClassLoader) -> Result<Vec<IndexTarget>> {
    let mut targets = Vec::new();
    let Some(bytes) = load_class("tlc2/overrides/TLCOverrides") else {
        return Ok(targets);
    };
    for (class, is_initialized) in read_index_classes(&bytes)?.unwrap_or_default() {
        let bytes = load_class(&class.replace('.', "/")).ok_or_else(|| {
            not_yet("a class a TLCOverrides index names that isn't beside the spec")
        })?;
        targets.extend(read_index_targets(&bytes, is_initialized)?);
    }
    Ok(targets)
}

// The header of a class file up to its pool, and the pool.
fn read_index_header<'a>(bytes: &'a [u8]) -> Result<(Reader<'a>, Vec<PoolEntry>)> {
    let mut reader = Reader { bytes, offset: 0 };
    if reader.u32()? != CLASS_MAGIC {
        return Err(not_yet(
            "a TLCOverrides index class that isn't a class file",
        ));
    }
    reader.u16()?;
    if reader.u16()? > MAXIMUM_MAJOR_VERSION {
        return Err(not_yet(
            "a Java class file of a version the front end doesn't read",
        ));
    }
    let pool = read_pool(&mut reader)?;
    Ok((reader, pool))
}

// Skips a class file's fields, which hold no code.
fn skip_fields(reader: &mut Reader) -> Result<()> {
    for _ in 0..reader.u16()? {
        reader.bytes(6)?;
        for _ in 0..reader.u16()? {
            reader.u16()?;
            let length = reader.u32()? as usize;
            reader.bytes(length)?;
        }
    }
    Ok(())
}

// The names of the classes an index class's code loads: each class literal and each string
// constant, which only `Class.forName` may read, and whether that runs the class's static
// initializer: a class literal doesn't, nor `forName(name, false, loader)`. Any other
// instruction or call declines. None for a plain class that implements no interface, which TLC
// skips as an index (`ITLCOverrides.class.isAssignableFrom`).
fn read_index_classes(bytes: &[u8]) -> Result<Option<Vec<(String, bool)>>> {
    let unread = || not_yet("a TLCOverrides index whose classes the front end doesn't read");
    let (mut reader, pool) = read_index_header(bytes)?;
    let access = reader.u16()?;
    if access & UNPLAIN_CLASS != 0 {
        return Err(unread());
    }
    reader.u16()?;
    if get_class_name(&pool, reader.u16()?)? != "java/lang/Object" {
        return Err(unread());
    }
    let interfaces = reader.u16()?;
    if interfaces == 0 {
        return Ok(None);
    }
    let mut is_index = false;
    for _ in 0..interfaces {
        is_index |= get_class_name(&pool, reader.u16()?)? == "tlc2/overrides/ITLCOverrides";
    }
    // `idx.newInstance()` throws, which TLC reports as an unexpected exception, for a class or
    // a constructor without parameters it can't reach from `SpecProcessor`.
    if !is_index || access & ACCESS_PUBLIC == 0 {
        return Err(unread());
    }
    skip_fields(&mut reader)?;
    let mut classes = Vec::new();
    let mut names = Vec::new();
    let mut is_initializing = false;
    let mut is_constructed = false;
    for _ in 0..reader.u16()? {
        let method_access = reader.u16()?;
        let method_name = get_entry(&pool, reader.u16()?)?.text.clone();
        let descriptor = get_entry(&pool, reader.u16()?)?.text.clone();
        is_constructed |=
            method_name == "<init>" && descriptor == "()V" && method_access & ACCESS_PUBLIC != 0;
        for _ in 0..reader.u16()? {
            let attribute = get_entry(&pool, reader.u16()?)?.text.clone();
            let length = reader.u32()? as usize;
            let mut body = Reader {
                bytes: reader.bytes(length)?,
                offset: 0,
            };
            if attribute != "Code" {
                continue;
            }
            body.bytes(4)?;
            let length = body.u32()? as usize;
            let code = body.bytes(length)?;
            let mut offset = 0;
            while offset < code.len() {
                let opcode = code[offset];
                let index = || -> Result<u16> {
                    let bytes = code.get(offset + 1..offset + 3).ok_or_else(unread)?;
                    Ok(u16::from_be_bytes([bytes[0], bytes[1]]))
                };
                offset += match opcode {
                    // iconst_m1 to iconst_5, aload_0 to aload_3, astore_0 to astore_3, aastore,
                    // dup, areturn, return and athrow. A null `get` returns, or holds, TLC
                    // dereferences.
                    0x02..=0x08 | 0x2a..=0x2d | 0x4b..=0x4e | 0x53 | 0x59 | 0xb0 | 0xb1 | 0xbf => 1,
                    // bipush, aload and astore
                    0x10 | 0x19 | 0x3a => 2,
                    // sipush
                    0x11 => 3,
                    // ldc and ldc_w
                    0x12 | 0x13 => {
                        let (constant, size) = if opcode == 0x12 {
                            (u16::from(*code.get(offset + 1).ok_or_else(unread)?), 2)
                        } else {
                            (index()?, 3)
                        };
                        let entry = get_entry(&pool, constant)?;
                        let name = get_entry(&pool, entry.first)?.text.replace('/', ".");
                        match entry.tag {
                            // A class of the JDK's, which declares no operator TLC replaces.
                            CLASS if name.starts_with("java.") => {}
                            CLASS => classes.push((name, false)),
                            STRING => names.push(name),
                            _ => return Err(unread()),
                        }
                        size
                    }
                    // new and anewarray, of the exception and of the array get returns
                    0xbb | 0xbd => {
                        let class = get_class_name(&pool, index()?)?;
                        if class
                            != if opcode == 0xbb {
                                "java/lang/RuntimeException"
                            } else {
                                "java/lang/Class"
                            }
                        {
                            return Err(unread());
                        }
                        3
                    }
                    // invokevirtual, invokespecial and invokestatic
                    0xb6..=0xb8 => {
                        let (class, member) = get_member(&pool, index()?)?;
                        if !INDEX_CALLS
                            .iter()
                            .any(|(known, signature)| *known == class && *signature == member)
                        {
                            return Err(unread());
                        }
                        is_initializing |= member == INDEX_CALLS[3].1;
                        3
                    }
                    _ => return Err(unread()),
                };
            }
        }
    }
    if !is_constructed {
        return Err(unread());
    }
    classes.extend(names.into_iter().map(|name| (name, is_initializing)));
    Ok(Some(classes))
}

// The operators the annotated methods of a class an index lists replace. `getDeclaredMethods`
// lists every method; `processModuleOverrides` reads `@Evaluation`, then `@TLAPlusCallable`,
// then `@TLAPlusOperator` (`definition` names the operator of the first two). Unless
// `warn = false`, each prints a warning for a module or operator SANY didn't load. Where one
// replaces an operator, an `@Evaluation` reports itself unless `silent`, and a
// `@TLAPlusCallable` always does.
fn read_index_targets(bytes: &[u8], is_initialized: bool) -> Result<Vec<IndexTarget>> {
    let unread = |reason: &str| not_yet(&format!("a class a TLCOverrides index names {reason}"));
    let (mut reader, pool) = read_index_header(bytes)?;
    let access = reader.u16()?;
    if access & UNPLAIN_CLASS != 0 {
        return Err(unread("that isn't a plain class"));
    }
    reader.u16()?;
    if get_class_name(&pool, reader.u16()?)? != "java/lang/Object" {
        return Err(unread("with a superclass"));
    }
    if reader.u16()? != 0 {
        return Err(unread("that implements an interface"));
    }
    skip_fields(&mut reader)?;
    let mut targets = Vec::new();
    for _ in 0..reader.u16()? {
        let method_access = reader.u16()?;
        let name = get_entry(&pool, reader.u16()?)?.text.clone();
        let descriptor = get_entry(&pool, reader.u16()?)?.text.clone();
        if name == "<clinit>" && is_initialized {
            return Err(unread("with a static initializer that Class.forName runs"));
        }
        let first = targets.len();
        let mut is_quiet = false;
        for _ in 0..reader.u16()? {
            let attribute = get_entry(&pool, reader.u16()?)?.text.clone();
            let length = reader.u32()? as usize;
            let mut body = Reader {
                bytes: reader.bytes(length)?,
                offset: 0,
            };
            if attribute == "Code" {
                is_quiet = is_quiet_code(&mut body, &pool).unwrap_or(false);
                continue;
            }
            if attribute != "RuntimeVisibleAnnotations" {
                continue;
            }
            for _ in 0..body.u16()? {
                let annotation = get_entry(&pool, body.u16()?)?.text.clone();
                let mut module = None;
                let mut identifier = None;
                let mut warn = true;
                let mut silent = false;
                for _ in 0..body.u16()? {
                    let element = get_entry(&pool, body.u16()?)?.text.clone();
                    let tag = body.u8()?;
                    if matches!(tag, b's' | b'Z') {
                        let entry = get_entry(&pool, body.u16()?)?;
                        match (element.as_str(), tag) {
                            ("module", b's') => module = Some(entry.text.clone()),
                            ("identifier" | "definition", b's') => {
                                identifier = Some(entry.text.clone());
                            }
                            ("warn", b'Z') => warn = entry.value != 0,
                            ("silent", b'Z') => silent = entry.value != 0,
                            _ => {}
                        }
                    } else {
                        body.offset -= 1;
                        skip_element_value(&mut body)?;
                    }
                }
                if !INDEX_ANNOTATIONS.contains(&annotation.as_str()) {
                    continue;
                }
                let is_operator = annotation == INDEX_ANNOTATIONS[0];
                let is_silent = is_operator || annotation == INDEX_ANNOTATIONS[1] && silent;
                let (Some(module), Some(identifier), false) = (module, identifier, warn) else {
                    return Err(unread("with a method TLC reports"));
                };
                let arity = descriptor
                    .find(')')
                    .map(|end| get_type_names(&descriptor[1..end]).map(|types| types.len()))
                    .ok_or_else(|| not_yet("a Java method descriptor without parameters"))??;
                targets.push(IndexTarget {
                    module,
                    identifier,
                    arity: is_operator.then_some(arity),
                    is_lazy: is_silent
                        && access & ACCESS_PUBLIC != 0
                        && method_access & ACCESS_PUBLIC != 0
                        && (arity > 0 || method_access & ACCESS_FINAL == 0),
                    is_quiet: false,
                });
            }
        }
        for target in &mut targets[first..] {
            target.is_quiet = is_quiet;
        }
    }
    Ok(targets)
}

/// The size of a JVM instruction of a fixed size (JVM specification, chapter 6), and None for a
/// branch, a switch, `wide` or an opcode that doesn't exist.
fn get_instruction_size(opcode: u8) -> Option<usize> {
    match opcode {
        0x00..=0x0f
        | 0x1a..=0x35
        | 0x3b..=0x83
        | 0x85..=0x98
        | 0xac..=0xb1
        | 0xbe
        | 0xbf
        | 0xc2
        | 0xc3 => Some(1),
        0x10 | 0x12 | 0x15..=0x19 | 0x36..=0x3a | 0xbc => Some(2),
        0x11 | 0x13 | 0x14 | 0x84 | 0xb2..=0xb8 | 0xbb | 0xbd | 0xc0 | 0xc1 => Some(3),
        0xc5 => Some(4),
        0xb9 | 0xba => Some(5),
        _ => None,
    }
}

/// Whether a method's code, read from its `Code` attribute, only builds a value of TLC's or
/// throws: TLC calls a replacement as it computes a definition as it starts
/// (`processConstantDefns`), and swallows what it throws there, so only what the method prints,
/// exits or changes shows. The code may not branch, which could loop, nor catch, and it may only
/// read the static fields of TLC's value classes, make TLC's values and exceptions of
/// `java.lang`, and call their constructors and `IntValue.gen`, none of which prints.
fn is_quiet_code(body: &mut Reader, pool: &[PoolEntry]) -> Result<bool> {
    body.bytes(4)?;
    let length = body.u32()? as usize;
    let code = body.bytes(length)?;
    if body.u16()? != 0 {
        return Ok(false);
    }
    let is_value_class = |class: &str| class.starts_with(VALUE_PACKAGE);
    let is_exception_class = |class: &str| {
        class
            .strip_prefix("java/lang/")
            .is_some_and(|name| !name.contains('/') && name.ends_with("Exception"))
    };
    let mut offset = 0;
    while offset < code.len() {
        let opcode = code[offset];
        let Some(size) = get_instruction_size(opcode) else {
            return Ok(false);
        };
        let index = || -> Result<u16> {
            let bytes = code
                .get(offset + 1..offset + 3)
                .ok_or_else(|| not_yet("a Java class file that ends early"))?;
            Ok(u16::from_be_bytes([bytes[0], bytes[1]]))
        };
        let is_quiet = match opcode {
            // monitorenter and monitorexit
            0xc2 | 0xc3 => false,
            // getstatic
            0xb2 => is_value_class(&get_member(pool, index()?)?.0),
            // putstatic, getfield, putfield, invokevirtual and invokeinterface
            0xb3..=0xb6 | 0xb9 | 0xba => false,
            // invokespecial: a constructor of a value or an exception
            0xb7 => {
                let (class, member) = get_member(pool, index()?)?;
                member.starts_with("<init>(")
                    && (is_value_class(&class) || is_exception_class(&class))
            }
            // invokestatic: IntValue.gen
            0xb8 => {
                let (class, member) = get_member(pool, index()?)?;
                class.strip_prefix(VALUE_PACKAGE) == Some("IntValue")
                    && member == "gen(I)Ltlc2/value/impl/IntValue;"
            }
            // new, which initializes the class
            0xbb => {
                let class = get_class_name(pool, index()?)?;
                is_value_class(&class) || is_exception_class(&class)
            }
            _ => true,
        };
        if !is_quiet {
            return Ok(false);
        }
        offset += size;
    }
    Ok(true)
}

/// Whether a user class for a standard module can cause TLC to print an override report.
pub fn standard_class_may_report(
    bytes: &[u8],
    module: &str,
    warnings: bool,
    visible: &dyn Fn(&str, &str, usize) -> bool,
) -> bool {
    scan_standard_reports(bytes, module, warnings, visible).unwrap_or(true)
}

fn scan_standard_reports(
    bytes: &[u8],
    module: &str,
    warnings: bool,
    visible: &dyn Fn(&str, &str, usize) -> bool,
) -> Result<bool> {
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
    reader.bytes(6)?;
    let interfaces = reader.u16()?;
    reader.bytes(usize::from(interfaces) * 2)?;
    let fields = reader.u16()?;
    for _ in 0..fields {
        reader.bytes(6)?;
        for _ in 0..reader.u16()? {
            reader.u16()?;
            let length = reader.u32()? as usize;
            reader.bytes(length)?;
        }
    }
    for _ in 0..reader.u16()? {
        let access = reader.u16()?;
        let name = get_entry(&pool, reader.u16()?)?.text.clone();
        let descriptor = get_entry(&pool, reader.u16()?)?.text.clone();
        let mut skipped = false;
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
                    skipped |= SKIPPING_ANNOTATIONS.contains(&annotation.text.as_str());
                }
            }
        }
        if access & ACCESS_PUBLIC == 0 || access & ACCESS_STATIC == 0 {
            continue;
        }
        if skipped {
            continue;
        }
        if warnings {
            return Ok(true);
        }
        let mapped = match name.as_str() {
            "BagCup" => Some("\\oplus"),
            "BagDiff" => Some("\\ominus"),
            "CombineFcn" => Some("@@"),
            "Concat" => Some("\\o"),
            "Divide" => Some("\\div"),
            "DotDot" => Some(".."),
            "Expt" => Some("^"),
            "GEQ" => Some(">="),
            "GT" => Some(">"),
            "LE" => Some("<="),
            "LT" => Some("<"),
            "MakeFcn" => Some(":>"),
            "Minus" => Some("-"),
            "Mod" => Some("%"),
            "Neg" => Some("-."),
            "Plus" => Some("+"),
            "SqSubseteq" => Some("\\sqsubseteq"),
            "Times" => Some("*"),
            _ => None,
        };
        let end = descriptor
            .find(')')
            .ok_or_else(|| not_yet("a Java method descriptor without parameters"))?;
        let arity = get_type_names(&descriptor[1..end])?.len();
        let mapping_unavailable = matches!(
            (module, name.as_str()),
            ("Integers", "Neg")
                | ("Sequences", "Concat")
                | ("Bags", "BagCup" | "BagDiff" | "SqSubseteq")
                | ("TLC", "MakeFcn" | "CombineFcn")
        );
        if visible(module, &name, arity)
            || !mapping_unavailable && mapped.is_some_and(|mapped| visible(module, mapped, arity))
        {
            return Ok(true);
        }
    }
    Ok(false)
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
