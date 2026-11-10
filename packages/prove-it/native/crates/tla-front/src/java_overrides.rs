//! TLC's Java overrides of a module's operators, as `src/java-overrides.ts` reads them: the
//! public static methods of the class file named after the module, beside the spec, each of which
//! replaces the operator of the same name and arity with the constant value it returns.

use std::rc::Rc;

use crate::ast::{Definition, DefinitionKind, Expr, Expression, ExpressionKind, Location, Module};
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
const METHOD_HANDLE: u8 = 15;
const METHOD_TYPE: u8 = 16;
const MODULE: u8 = 19;
const PACKAGE: u8 = 20;

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

fn get_entry(pool: &[PoolEntry], index: u16) -> Result<&PoolEntry> {
    pool.get(index as usize)
        .ok_or_else(|| not_yet("a Java class file's constant out of its pool"))
}

fn get_class_name(pool: &[PoolEntry], index: u16) -> Result<String> {
    Ok(get_entry(pool, get_entry(pool, index)?.first)?.text.clone())
}

// The public static methods of a class file and their bytecode, in the order of the class file.
fn read_class_file(bytes: &[u8]) -> Result<(Vec<PoolEntry>, Vec<JavaMethod>)> {
    let mut reader = Reader { bytes, offset: 0 };
    if reader.u32()? != CLASS_MAGIC {
        return Err(not_yet("a module override that isn't a class file"));
    }
    reader.bytes(4)?;
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
            _ => {
                entry.first = reader.u16()?;
                entry.second = reader.u16()?;
            }
        }
        pool[index as usize] = entry;
        index += 1;
    }
    reader.u16()?;
    let class_name = get_class_name(&pool, reader.u16()?)?.replace('/', ".");
    reader.u16()?;
    let interfaces = reader.u16()? as usize;
    reader.bytes(interfaces * 2)?;
    for _ in 0..reader.u16()? {
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
        let mut exceptions = Vec::new();
        for _ in 0..reader.u16()? {
            let attribute = get_entry(&pool, reader.u16()?)?.text.clone();
            let length = reader.u32()? as usize;
            let mut body = Reader {
                bytes: reader.bytes(length)?,
                offset: 0,
            };
            if attribute == "Code" {
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
    Ok((pool, methods))
}

// A class and a member of it that a constant names.
fn get_member(pool: &[PoolEntry], index: u16) -> Result<(String, String)> {
    let reference = get_entry(pool, index)?;
    let name_and_type = get_entry(pool, reference.second)?;
    Ok((
        get_class_name(pool, reference.first)?,
        get_entry(pool, name_and_type.first)?.text.clone(),
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
// One that computes its value TLC runs as Java, which the front end doesn't.
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
                    (Some("BoolValue"), "ValTrue") => "TRUE",
                    (Some("BoolValue"), "ValFalse") => "FALSE",
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
                if class.strip_prefix(VALUE_PACKAGE) != Some("IntValue") || callee != "gen" {
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
                    || constructor != "<init>"
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
            // areturn
            0xb0 => {
                return match stack.pop() {
                    Some(Item::Literal(value)) | Some(Item::Object(_, Some(value))) => Ok(value),
                    _ => Err(unsupported()),
                };
            }
            _ => return Err(unsupported()),
        }
    }
    Err(unsupported())
}

/// `overrideDefinitions`: TLC loads a class named after each module and replaces each operator of
/// the module that the root module sees with the public static method of the same name and
/// arity. It reports whether each method matched an operator.
pub fn override_definitions(
    module: &Rc<Module>,
    bytes: &[u8],
    is_root: bool,
) -> Result<(Rc<Module>, Vec<JavaOverride>)> {
    let (pool, methods) = read_class_file(bytes)?;
    let get_arity = |name: &str| {
        module
            .definitions
            .iter()
            .filter(|definition| is_root || !definition.is_local)
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
