//! SANY's XMLExporter (`tla2sany.xml.XMLExporter`), ported from `src/sany/xml.ts`: the XML of a
//! specification SANY accepts, as TLC master's SANY writes it.
//!
//! JavaScript strings are UTF-16, as Java's are, so the comments are processed as UTF-16 code
//! units: an index into a line is a code unit's, and a slice of a line may split a surrogate pair,
//! whose lone half the export then reports as a character XML cannot represent.

use crate::errors::FrontError;
use crate::hash::FastSet;
use crate::sany::nodes::{
    CONSTANT_DECL_KIND, DefKind, Graph, NodeId, NodeKind, OpAppl, SanyLocation, Subst,
    VARIABLE_DECL_KIND,
};
use crate::sany::{Result, SanySpecification, not_yet};

/// `XML_EXPORT_EXIT_CODE`: XMLExporterExitCode, and the status Java exits with on an exception
/// that nothing catches.
pub const XML_EXPORT_UNCAUGHT_EXCEPTION: i32 = 1;
pub const XML_EXPORT_ARGS_PARSING_FAILURE: i32 = 1;
pub const XML_EXPORT_SPEC_PARSING_FAILURE: i32 = 2;
pub const XML_EXPORT_UNREPRESENTABLE_CHARACTER: i32 = 7;

/// `XmlExportOptions`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct XmlExportOptions {
    /// -r: only the root module, and only the declarations and definitions a module makes itself.
    pub is_restricted: bool,
    /// -u: the pre-comments without the boxes and \* that format them.
    pub is_uncommented: bool,
    /// -t: the XML on one line.
    pub is_terse: bool,
}

/// What the TypeScript throws with `setExitCode`. An exception (`is_exception`) is one that
/// nothing catches, which the CLI prints as `Exception in thread "main" <message>`; otherwise it
/// prints `ERROR: <message>`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct XmlExportError {
    pub message: String,
    pub exit_code: i32,
    pub is_exception: bool,
}

/// What stops the export: an error the exporter reports, or what the port doesn't cover.
enum Thrown {
    Export(XmlExportError),
    Front(FrontError),
}

impl From<FrontError> for Thrown {
    fn from(error: FrontError) -> Thrown {
        Thrown::Front(error)
    }
}

type Exported = std::result::Result<Element, Thrown>;

/// The content of an element: none, text, or character data, which a comment's processing may
/// leave with a lone surrogate.
enum Data {
    None,
    Text(String),
    Cdata(Vec<u16>),
}

struct Element {
    tag: &'static str,
    data: Data,
    children: Vec<Element>,
}

fn create_element(tag: &'static str, children: Vec<Element>) -> Element {
    Element {
        tag,
        data: Data::None,
        children,
    }
}

fn create_text(tag: &'static str, text: impl ToString) -> Element {
    Element {
        tag,
        data: Data::Text(text.to_string()),
        children: Vec::new(),
    }
}

/// The exception that SANY's XMLExporter throws for a node of a kind it can't export.
fn get_unsupported_kind(kind: u32) -> String {
    format!("java.lang.IllegalArgumentException: unsupported kind: {kind} in xml export")
}

/// `escapeXml`: Java's serializer also writes a character outside the Basic Multilingual Plane,
/// which a Java string holds as two chars, as a character reference.
fn escape_xml(text: &str) -> String {
    let mut escaped = String::with_capacity(text.len());
    for character in text.chars() {
        match character {
            '&' => escaped.push_str("&amp;"),
            '<' => escaped.push_str("&lt;"),
            '>' => escaped.push_str("&gt;"),
            '\r' => escaped.push_str("&#13;"),
            '\u{10000}'.. => escaped.push_str(&format!("&#{};", u32::from(character))),
            _ => escaped.push(character),
        }
    }
    escaped
}

/// `UNREPRESENTABLE_CHARACTER`: a code point outside XML 1.0's Char production. A lone surrogate
/// is one.
fn is_unrepresentable(code_point: u32) -> bool {
    !matches!(code_point, 0x9 | 0xA | 0xD | 0x20..=0xD7FF | 0xE000..=0xFFFD | 0x10000..=0x10FFFF)
}

/// The first code point XML 1.0 cannot represent in an element's own content.
fn find_unrepresentable_in(data: &Data) -> Option<u32> {
    match data {
        Data::None => None,
        Data::Text(text) => text
            .chars()
            .map(u32::from)
            .find(|&code_point| is_unrepresentable(code_point)),
        Data::Cdata(units) => char::decode_utf16(units.iter().copied())
            .map(|decoded| {
                decoded.map_or_else(|lone| u32::from(lone.unpaired_surrogate()), u32::from)
            })
            .find(|&code_point| is_unrepresentable(code_point)),
    }
}

/// `findUnrepresentable`: XMLExporter.findUnrepresentableCharacterData, the first element, in
/// document order, whose character data XML 1.0 cannot represent, with the character.
fn find_unrepresentable(element: &Element) -> Option<(&'static str, u32)> {
    find_unrepresentable_in(&element.data)
        .map(|code_point| (element.tag, code_point))
        .or_else(|| element.children.iter().find_map(find_unrepresentable))
}

/// The message of the error for a character XML 1.0 cannot represent in the element `tag`.
fn get_unrepresentable_message(tag: &str, code_point: u32) -> String {
    format!(
        "The spec contains the character U+{code_point:04X} in the {tag} element. XML 1.0 cannot represent that character in character data, not even as a numeric character reference, so the spec cannot be exported until the character is removed from it."
    )
}

/// `printElement`: the lines of Java's identity Transformer, which pretty prints with an indent
/// amount of 2. An element whose text or character data is empty has no content, like an element
/// without children.
fn print_element(element: &Element, depth: usize, indent_amount: usize, lines: &mut Vec<String>) {
    let indent = " ".repeat(depth * indent_amount);
    let tag = element.tag;
    match &element.data {
        Data::Cdata(units) if !units.is_empty() => {
            let data = String::from_utf16_lossy(units).replace("]]>", "]]]]><![CDATA[>");
            lines.push(format!("{indent}<{tag}><![CDATA[{data}]]></{tag}>"));
        }
        Data::Text(text) if !text.is_empty() => {
            lines.push(format!("{indent}<{tag}>{}</{tag}>", escape_xml(text)));
        }
        _ if element.children.is_empty() => lines.push(format!("{indent}<{tag}/>")),
        _ => {
            lines.push(format!("{indent}<{tag}>"));
            for child in &element.children {
                print_element(child, depth + 1, indent_amount, lines);
            }
            lines.push(format!("{indent}</{tag}>"));
        }
    }
}

fn get_location_element(location: &SanyLocation) -> Element {
    create_element(
        "location",
        vec![
            create_element(
                "column",
                vec![
                    create_text("begin", location.begin_column),
                    create_text("end", location.end_column),
                ],
            ),
            create_element(
                "line",
                vec![
                    create_text("begin", location.begin_line),
                    create_text("end", location.end_line),
                ],
            ),
            create_text("filename", &location.file),
        ],
    )
}

/// `getReferenceTag`, for the nodes a context holds: symbols, theorems and assumptions.
fn get_reference_tag(kind: &NodeKind) -> Option<&'static str> {
    match kind {
        NodeKind::FormalParam(_) => Some("FormalParamNodeRef"),
        NodeKind::OpDecl(_) => Some("OpDeclNodeRef"),
        NodeKind::Module(_) => Some("ModuleNodeRef"),
        NodeKind::Theorem(_) => Some("TheoremNodeRef"),
        NodeKind::Assume { .. } => Some("AssumeNodeRef"),
        NodeKind::ThmOrAssumpDef(node) if node.is_theorem => Some("TheoremDefRef"),
        NodeKind::ThmOrAssumpDef(_) => Some("AssumeDefRef"),
        NodeKind::OpDef(node) => Some(match node.def_kind {
            DefKind::UserDefined => "UserDefinedOpKindRef",
            DefKind::BuiltIn => "BuiltInKindRef",
            _ => "ModuleInstanceKindRef",
        }),
        _ => None,
    }
}

/// `getHashMapCapacity`: the capacity of a `java.util.HashMap`, which holds SymbolContext's
/// entries, once `size` entries are in it.
fn get_hash_map_capacity(size: usize) -> usize {
    let mut capacity = 16;
    while size * 4 > capacity * 3 {
        capacity *= 2;
    }
    capacity
}

/// `getHashMapBucket`: the bucket of an Integer key, by which a HashMap lists its entries, and
/// those of a bucket in the order they were added.
fn get_hash_map_bucket(key: u32, capacity: usize) -> usize {
    (key ^ (key >> 16)) as usize & (capacity - 1)
}

fn get_utf16(text: &str) -> Vec<u16> {
    text.encode_utf16().collect()
}

fn index_of(text: &[u16], pattern: &str) -> Option<usize> {
    let pattern = get_utf16(pattern);
    text.windows(pattern.len())
        .position(|window| window == pattern)
}

fn last_index_of(text: &[u16], pattern: &str) -> Option<usize> {
    let pattern = get_utf16(pattern);
    text.windows(pattern.len())
        .rposition(|window| window == pattern)
}

fn join_lines(lines: &[Vec<u16>]) -> Vec<u16> {
    lines.join(&u16::from(b'\n'))
}

/// `splitLines`: Java's String.split, which drops the empty strings at the end.
fn split_lines(text: &[u16]) -> Vec<&[u16]> {
    let mut lines: Vec<&[u16]> = text.split(|&unit| unit == u16::from(b'\n')).collect();
    let last = lines.len() - 1;
    for line in &mut lines[..last] {
        if let Some(rest) = line.strip_suffix(&[u16::from(b'\r')]) {
            *line = rest;
        }
    }
    while lines.last().is_some_and(|line| line.is_empty()) {
        lines.pop();
    }
    lines
}

/// `trimJava`: Java's String.trim, which removes the control characters and spaces at either end.
fn trim_java(text: &[u16]) -> &[u16] {
    let start = text
        .iter()
        .position(|&unit| unit > 0x20)
        .unwrap_or(text.len());
    let end = text
        .iter()
        .rposition(|&unit| unit > 0x20)
        .map_or(start, |index| index + 1);
    &text[start..end]
}

/// `TRAILING_WHITESPACE`: the characters of Java's Character.isWhitespace, which include four
/// control characters.
fn trim_trailing_whitespace(text: &[u16]) -> &[u16] {
    let is_whitespace = |unit: u16| {
        matches!(unit, 0x9..=0xD | 0x1C..=0x20 | 0x1680 | 0x2000..=0x2006 | 0x2008..=0x200A
            | 0x2028 | 0x2029 | 0x205F | 0x3000)
    };
    let end = text
        .iter()
        .rposition(|&unit| !is_whitespace(unit))
        .map_or(0, |index| index + 1);
    &text[..end]
}

/// JavaScript's `String.prototype.trimEnd`, whose white space is not Rust's: it has U+FEFF and
/// not U+0085.
fn trim_end_javascript(text: &str) -> &str {
    text.trim_end_matches(|character: char| {
        character == '\u{FEFF}' || (character.is_whitespace() && character != '\u{85}')
    })
}

/// `unboxComment`: SyntaxTreeNode.unboxComment, the lines of a comment boxed in (** and **),
/// without the box.
fn unbox_comment(text: &[u16]) -> Vec<u16> {
    let (Some(start), Some(end)) = (index_of(text, "(**"), last_index_of(text, "**)")) else {
        return text.to_vec();
    };
    if end <= start {
        return text.to_vec();
    }
    let lines = split_lines(text);
    let begin_line = lines
        .iter()
        .position(|line| index_of(line, "(**").is_some());
    let end_line = lines
        .iter()
        .rposition(|line| index_of(line, "**)").is_some());
    let (Some(begin_line), Some(end_line)) = (begin_line, end_line) else {
        return text.to_vec();
    };
    if begin_line >= end_line {
        return text.to_vec();
    }
    let unboxed: Vec<Vec<u16>> = lines[begin_line + 1..end_line]
        .iter()
        .map(|line| {
            let (Some(begin), Some(finish)) = (index_of(line, "(*"), index_of(line, "*)")) else {
                return line.to_vec();
            };
            if finish <= begin {
                return line.to_vec();
            }
            let content_start = (begin + 3).min(line.len());
            trim_trailing_whitespace(&line[content_start..finish.max(content_start)]).to_vec()
        })
        .collect();
    join_lines(&unboxed)
}

/// `unboxBackslashStarComment`: SyntaxTreeNode.unboxBackslashStarComment, the lines of a comment
/// without the \* that starts them, when at least half of them start with one.
fn unbox_backslash_star_comment(text: &[u16]) -> Vec<u16> {
    let lines = split_lines(text);
    let backslash_star = get_utf16("\\*");
    let is_comment_line = |line: &[u16]| trim_java(line).starts_with(&backslash_star);
    let comment_lines = lines.iter().filter(|line| is_comment_line(line)).count();
    if comment_lines < lines.len() / 2 {
        return text.to_vec();
    }
    let unboxed: Vec<Vec<u16>> = lines
        .iter()
        .map(|line| {
            if !is_comment_line(line) {
                return line.to_vec();
            }
            let start = index_of(line, "\\*").map_or(0, |index| index + 2);
            let start = if line.get(start) == Some(&u16::from(b' ')) {
                start + 1
            } else {
                start
            };
            line[start..].to_vec()
        })
        .collect();
    join_lines(&unboxed)
}

/// `withLevel`: the element with the node's location and, once it is level-checked, its level.
fn with_level(
    graph: &Graph,
    element: Element,
    id: NodeId,
    location: Option<&SanyLocation>,
) -> Element {
    let levels = graph.levels(id);
    let head = location
        .map(get_location_element)
        .into_iter()
        .chain((levels.level_checked != 0).then(|| create_text("level", levels.level)));
    Element {
        children: head.chain(element.children).collect(),
        ..element
    }
}

/// `exportSpecification`'s state. SymbolContext: SANY marks a node's UID as exported before it
/// exports the node's definition, which can export other definitions, and adds the definition to
/// its entries after them.
struct Exporter<'a> {
    graph: &'a Graph,
    options: &'a XmlExportOptions,
    keys: FastSet<u32>,
    entries: Vec<(u32, Element)>,
    /// SymbolContext's OTHER_BUG flag, which every copy of the context shares, so that from the
    /// first CASE with an OTHER arm on, a node missing its first operand exports it as $Other.
    is_other_bug: bool,
}

impl<'a> Exporter<'a> {
    fn get_reference(&mut self, id: NodeId) -> Exported {
        let node = self.graph.node(id);
        let Some(tag) = get_reference_tag(&node.kind) else {
            not_yet("a reference to a node outside a context")?
        };
        if self.keys.insert(node.uid) {
            let definition = self.export_definition(id)?;
            self.entries.push((node.uid, definition));
        }
        Ok(create_element(tag, vec![create_text("UID", node.uid)]))
    }

    fn get_references(&mut self, ids: &[NodeId]) -> std::result::Result<Vec<Element>, Thrown> {
        ids.iter().map(|&id| self.get_reference(id)).collect()
    }

    fn export_expressions(&mut self, ids: &[NodeId]) -> std::result::Result<Vec<Element>, Thrown> {
        ids.iter().map(|&id| self.export_expression(id)).collect()
    }

    fn get_params_element(
        &mut self,
        params: &[NodeId],
        is_leibniz_arg: Option<&[bool]>,
    ) -> Exported {
        let mut children = Vec::with_capacity(params.len());
        for (index, &param) in params.iter().enumerate() {
            let mut leibniz_param = vec![self.get_reference(param)?];
            if is_leibniz_arg.and_then(|args| args.get(index)) == Some(&true) {
                leibniz_param.push(create_element("leibniz", Vec::new()));
            }
            children.push(create_element("leibnizparam", leibniz_param));
        }
        Ok(create_element("params", children))
    }

    fn get_pre_comments_element(&self, comments: &[String]) -> Option<Element> {
        let text = comments
            .iter()
            .map(|comment| trim_end_javascript(comment))
            .filter(|comment| !comment.is_empty())
            .collect::<Vec<_>>()
            .join("\n");
        let text = get_utf16(&text);
        let cdata = if self.options.is_uncommented {
            unbox_backslash_star_comment(&unbox_comment(&text))
        } else {
            text
        };
        (!comments.is_empty()).then(|| Element {
            tag: "pre-comments",
            data: Data::Cdata(cdata),
            children: Vec::new(),
        })
    }

    /// `exportDefinition`: the definition of a node a context holds.
    fn export_definition(&mut self, id: NodeId) -> Exported {
        let graph = self.graph;
        match graph.kind(id) {
            NodeKind::FormalParam(node) => Ok(with_level(
                graph,
                create_element(
                    "FormalParamNode",
                    vec![
                        create_text("uniquename", &node.name),
                        create_text("arity", node.arity),
                    ],
                ),
                id,
                node.location.as_ref(),
            )),
            NodeKind::OpDecl(node) => Ok(with_level(
                graph,
                create_element(
                    "OpDeclNode",
                    vec![
                        create_text("uniquename", &node.name),
                        create_text("arity", node.arity),
                        create_text("kind", node.decl_kind),
                    ],
                ),
                id,
                Some(&node.location),
            )),
            NodeKind::OpDef(node) => match node.def_kind {
                // SANY's XMLExporter fails on the definition of a proof step that a DEF clause
                // names.
                DefKind::NumberedProofStep => Err(Thrown::Export(XmlExportError {
                    message: get_unsupported_kind(37),
                    exit_code: XML_EXPORT_UNCAUGHT_EXCEPTION,
                    is_exception: true,
                })),
                DefKind::ModuleInstance => {
                    let mut children = vec![create_text("uniquename", &node.name)];
                    if node.is_local {
                        children.push(create_element("local", Vec::new()));
                    }
                    Ok(with_level(
                        graph,
                        create_element("ModuleInstanceKind", children),
                        id,
                        Some(&node.location),
                    ))
                }
                DefKind::BuiltIn => {
                    let mut children = vec![
                        create_text("uniquename", &node.name),
                        create_text("arity", node.arity),
                    ];
                    if let Some(params) = &node.params {
                        children
                            .push(self.get_params_element(params, node.is_leibniz_arg.as_deref())?);
                    }
                    Ok(with_level(
                        graph,
                        create_element("BuiltInKind", children),
                        id,
                        Some(&node.location),
                    ))
                }
                DefKind::UserDefined => {
                    let (Some(body), Some(module)) = (node.body, node.module) else {
                        not_yet(format!("The definition of {} has no body", node.name))?
                    };
                    let mut children = vec![
                        create_text("uniquename", &node.name),
                        create_text("arity", node.arity),
                        create_element(
                            "originalOperator",
                            vec![self.get_reference(node.source.unwrap_or(id))?],
                        ),
                        create_element(
                            "originallyDefinedInModule",
                            vec![self.get_reference(module)?],
                        ),
                        create_element("body", vec![self.export_expression(body)?]),
                        self.get_params_element(
                            node.params.as_deref().unwrap_or_default(),
                            node.is_leibniz_arg.as_deref(),
                        )?,
                    ];
                    children.extend(self.get_pre_comments_element(&node.pre_comments));
                    if node.in_recursive {
                        children.push(create_element("recursive", Vec::new()));
                    }
                    if node.recursive_section >= 0 {
                        children.push(create_text("recursiveSection", node.recursive_section));
                    }
                    if node.is_local {
                        children.push(create_element("local", Vec::new()));
                    }
                    Ok(with_level(
                        graph,
                        create_element("UserDefinedOpKind", children),
                        id,
                        Some(&node.location),
                    ))
                }
            },
            NodeKind::ThmOrAssumpDef(node) => Ok(with_level(
                graph,
                create_element(
                    if node.is_theorem {
                        "TheoremDefNode"
                    } else {
                        "AssumeDef"
                    },
                    vec![
                        create_text("uniquename", &node.name),
                        self.export_expression(node.body)?,
                    ],
                ),
                id,
                Some(&node.location),
            )),
            NodeKind::Module(node) => {
                let mut children = vec![get_location_element(&node.location)];
                children.extend(self.export_module_children(id)?);
                Ok(create_element("ModuleNode", children))
            }
            NodeKind::Theorem(node) => {
                let mut children = Vec::new();
                if let Some(definition) = node.definition {
                    children.push(create_element(
                        "definition",
                        vec![self.get_reference(definition)?],
                    ));
                }
                children.push(create_element(
                    "body",
                    vec![self.export_expression(node.body)?],
                ));
                if let Some(proof) = node.proof {
                    children.push(self.export_expression(proof)?);
                }
                if node.is_suffices {
                    children.push(create_element("suffices", Vec::new()));
                }
                Ok(with_level(
                    graph,
                    create_element("TheoremNode", children),
                    id,
                    Some(&node.location),
                ))
            }
            NodeKind::Assume {
                definition,
                body,
                location,
            } => {
                // AssumeNode#getLevel is its body's, which fails before the body is level-checked.
                let levels = graph.levels(*body);
                let mut children = vec![get_location_element(location)];
                if levels.level_checked != 0 {
                    children.push(create_text("level", levels.level));
                }
                if let Some(definition) = definition {
                    children.push(create_element(
                        "definition",
                        vec![self.get_reference(*definition)?],
                    ));
                }
                children.push(create_element("body", vec![self.export_expression(*body)?]));
                Ok(create_element("AssumeNode", children))
            }
            _ => not_yet("the definition of a node outside a context")?,
        }
    }

    /// XMLExporter's filter for -r: a declaration or definition that the module makes itself.
    fn is_exported(&self, id: NodeId, module: NodeId) -> bool {
        !self.options.is_restricted
            || match self.graph.kind(id) {
                NodeKind::OpDecl(node) => node.module == module,
                NodeKind::OpDef(node) => node.module == Some(module),
                _ => false,
            }
    }

    /// `exportModuleChildren`: the children of a ModuleNode element after its location, built in
    /// the order SANY builds them so that the context entries they add appear in the same order.
    fn export_module_children(&mut self, id: NodeId) -> std::result::Result<Vec<Element>, Thrown> {
        let graph = self.graph;
        let Some(module) = graph.module(id) else {
            not_yet("a module that is no module")?
        };
        let mut names: Vec<&str> = module
            .extendees
            .iter()
            .filter_map(|&extendee| graph.node(extendee).symbol_name().map(|name| &**name))
            .collect();
        names.sort_by(|first, second| first.encode_utf16().cmp(second.encode_utf16()));
        names.dedup();
        let mut children = vec![
            create_text("uniquename", &module.name),
            create_element(
                "extends",
                names
                    .into_iter()
                    .map(|name| create_text("uniquename", name))
                    .collect(),
            ),
        ];
        let exported: Vec<NodeId> = [
            graph.get_declarations(id, CONSTANT_DECL_KIND),
            graph.get_declarations(id, VARIABLE_DECL_KIND),
            graph.get_op_defs(id),
        ]
        .concat()
        .into_iter()
        .filter(|&declaration| self.is_exported(declaration, id))
        .collect();
        children.extend(self.get_references(&exported)?);
        for &top_level in &module.top_level {
            children.push(match graph.kind(top_level) {
                NodeKind::Instance(_) | NodeKind::UseOrHide(_) => {
                    self.export_expression(top_level)?
                }
                _ => self.get_reference(top_level)?,
            });
        }
        let inner_modules: Vec<NodeId> = module
            .definitions
            .iter()
            .copied()
            .filter(|&definition| matches!(graph.kind(definition), NodeKind::Module(_)))
            .collect();
        children.extend(self.get_references(&inner_modules)?);
        Ok(children)
    }

    fn export_substs(&mut self, substs: &[Subst]) -> std::result::Result<Vec<Element>, Thrown> {
        substs
            .iter()
            .map(|subst| {
                Ok(create_element(
                    "Subst",
                    vec![
                        self.get_reference(subst.op)?,
                        self.export_expression(subst.expr)?,
                    ],
                ))
            })
            .collect()
    }

    fn is_operator(&self, id: NodeId, name: &str) -> bool {
        self.graph
            .node(id)
            .symbol_name()
            .is_some_and(|operator| &**operator == name)
    }

    fn export_application(&mut self, node: &OpAppl) -> Exported {
        let graph = self.graph;
        if self.is_operator(node.operator, "$Case")
            && node.operands.len() > 1
            && let Some(Some(last)) = node.operands.last()
            && let NodeKind::OpAppl(last) = graph.kind(*last)
            && self.is_operator(last.operator, "$Pair")
            && last.operands.first().copied().flatten().is_none()
        {
            self.is_other_bug = true;
        }
        let operator = self.get_reference(node.operator)?;
        let mut operands = Vec::with_capacity(node.operands.len());
        for (index, operand) in node.operands.iter().enumerate() {
            operands.push(match operand {
                Some(operand)
                    if !(index == 0 && self.is_other_bug && graph.node(*operand).is_absent()) =>
                {
                    self.export_expression(*operand)?
                }
                _ => create_element("StringNode", vec![create_text("StringValue", "$Other")]),
            });
        }
        let mut children = vec![
            create_element("operator", vec![operator]),
            create_element("operands", operands),
        ];
        if node.unbounded.is_some() || node.bounded.is_some() {
            let is_tuple = |index: usize| {
                node.tuple_ors
                    .as_ref()
                    .and_then(|tuple_ors| tuple_ors.get(index))
                    == Some(&true)
            };
            let mut bound_symbols = Vec::new();
            for (index, &symbol) in node.unbounded.iter().flatten().enumerate() {
                let mut unbound = vec![self.get_reference(symbol)?];
                if is_tuple(index) {
                    unbound.push(create_element("tuple", Vec::new()));
                }
                bound_symbols.push(create_element("unbound", unbound));
            }
            for (index, symbols) in node.bounded.iter().flatten().enumerate() {
                let mut bound = self.get_references(symbols)?;
                if is_tuple(index) {
                    bound.push(create_element("tuple", Vec::new()));
                }
                let Some(&range) = node.ranges.get(index) else {
                    not_yet("a bound without a range")?
                };
                bound.push(self.export_expression(range)?);
                bound_symbols.push(create_element("bound", bound));
            }
            children.push(create_element("boundSymbols", bound_symbols));
        }
        Ok(create_element("OpApplNode", children))
    }

    fn export_facts(&mut self, facts: &[NodeId]) -> std::result::Result<Vec<Element>, Thrown> {
        facts
            .iter()
            .map(|&fact| match self.graph.kind(fact) {
                NodeKind::Module(_) | NodeKind::OpDef(_) => self.get_reference(fact),
                _ => self.export_expression(fact),
            })
            .collect()
    }

    /// `exportExpression` and `exportLevelNode`.
    fn export_expression(&mut self, id: NodeId) -> Exported {
        let graph = self.graph;
        let location = graph.node(id).location();
        let element = match graph.kind(id) {
            NodeKind::OpAppl(node) => self.export_application(node)?,
            NodeKind::Numeral { value, .. } => {
                create_element("NumeralNode", vec![create_text("IntValue", value)])
            }
            NodeKind::String { value, .. } => {
                create_element("StringNode", vec![create_text("StringValue", value)])
            }
            NodeKind::Decimal(node) => create_element(
                "DecimalNode",
                vec![
                    create_text("mantissa", &node.mantissa),
                    create_text("exponent", &node.exponent),
                    create_text("integralPart", &node.integral_part),
                    create_text("fractionalPart", &node.fractional_part),
                ],
            ),
            NodeKind::LetIn(node) => {
                let body = self.export_expression(node.body)?;
                create_element(
                    "LetInNode",
                    vec![
                        create_element("body", vec![body]),
                        create_element("opDefs", self.get_references(&node.op_defs)?),
                    ],
                )
            }
            NodeKind::Label(node) => create_element(
                "LabelNode",
                vec![
                    create_text("uniquename", &node.name),
                    create_text("arity", node.params.len()),
                    create_element("body", vec![self.export_expression(node.body)?]),
                    create_element("params", self.get_references(&node.params)?),
                ],
            ),
            NodeKind::OpArg { op, .. } => create_element(
                "OpArgNode",
                vec![create_element("argument", vec![self.get_reference(*op)?])],
            ),
            NodeKind::At {
                except, component, ..
            } => {
                let get_first_operand = |application: NodeId| match graph.kind(application) {
                    NodeKind::OpAppl(node) => node.operands.first().copied().flatten(),
                    _ => None,
                };
                let (Some(object), Some(components)) =
                    (get_first_operand(*except), get_first_operand(*component))
                else {
                    not_yet("An @ refers to an incomplete EXCEPT")?
                };
                create_element(
                    "AtNode",
                    vec![
                        self.export_expression(object)?,
                        self.export_expression(components)?,
                    ],
                )
            }
            NodeKind::SubstIn(node) => {
                let substs = self.export_substs(&node.substs)?;
                let body = self.export_expression(node.body)?;
                create_element(
                    if node.is_assume_prove {
                        "APSubstInNode"
                    } else {
                        "SubstInNode"
                    },
                    vec![
                        create_element("substs", substs),
                        create_element("body", vec![body]),
                        create_element(
                            "instFrom",
                            vec![self.get_reference(node.instantiating_module)?],
                        ),
                        create_element(
                            "instTo",
                            vec![self.get_reference(node.instantiated_module)?],
                        ),
                    ],
                )
            }
            NodeKind::Instance(node) => {
                let substs = self.export_substs(&node.substs)?;
                let params = self.get_references(&node.params)?;
                let Some(module) = graph.node(node.module).symbol_name() else {
                    not_yet("an instance of no module")?
                };
                let mut children = vec![
                    get_location_element(&node.location),
                    create_text("level", 0),
                ];
                children.extend(
                    node.name
                        .as_ref()
                        .map(|name| create_text("uniquename", name)),
                );
                children.push(create_text("module", module));
                children.push(create_element("substs", substs));
                children.push(create_element("params", params));
                if node.is_local {
                    children.push(create_element("local", Vec::new()));
                }
                return Ok(create_element("InstanceNode", children));
            }
            NodeKind::UseOrHide(node) => {
                let mut children = vec![
                    create_element("facts", self.export_facts(&node.facts)?),
                    create_element("defs", self.get_references(&node.defs)?),
                ];
                if node.is_only {
                    children.push(create_element("only", Vec::new()));
                }
                if node.is_hide {
                    children.push(create_element("hide", Vec::new()));
                }
                create_element("UseOrHideNode", children)
            }
            NodeKind::NewSymb {
                declaration, set, ..
            } => {
                let mut children = vec![self.get_reference(*declaration)?];
                if let Some(set) = set {
                    children.push(self.export_expression(*set)?);
                }
                create_element("NewSymbNode", children)
            }
            NodeKind::AssumeProve(node) => {
                let mut children = vec![
                    create_element("assumes", self.export_expressions(&node.assumptions)?),
                    create_element("prove", vec![self.export_expression(node.goal)?]),
                ];
                if node.is_suffices {
                    children.push(create_element("suffices", Vec::new()));
                }
                if node.is_boxed {
                    children.push(create_element("boxed", Vec::new()));
                }
                create_element("AssumeProveNode", children)
            }
            NodeKind::LeafProof(node) if node.is_omitted => create_element("omitted", Vec::new()),
            NodeKind::LeafProof(node) if node.facts.is_empty() && node.defs.is_empty() => {
                create_element("obvious", Vec::new())
            }
            NodeKind::LeafProof(node) => {
                let mut children = vec![
                    create_element("facts", self.export_facts(&node.facts)?),
                    create_element("defs", self.get_references(&node.defs)?),
                ];
                if node.is_only {
                    children.push(create_element("only", Vec::new()));
                }
                create_element("by", children)
            }
            NodeKind::NonLeafProof(node) => {
                let mut children = vec![create_text("proofLevel", node.proof_level)];
                for &step in &node.steps {
                    children.push(match graph.kind(step) {
                        NodeKind::Theorem(_) => self.get_reference(step)?,
                        _ => self.export_expression(step)?,
                    });
                }
                create_element("steps", children)
            }
            NodeKind::DefStep { defs, .. } => {
                create_element("DefStepNode", self.get_references(defs)?)
            }
            _ => not_yet("the export of a node that is no expression")?,
        };
        Ok(with_level(graph, element, id, location))
    }
}

/// `exportSpecification`: the XML of SANY's XMLExporter, every module of the specification, and a
/// context with an entry for each symbol, theorem and assumption that the modules refer to.
fn export_specification(specification: &SanySpecification, options: &XmlExportOptions) -> Exported {
    let mut exporter = Exporter {
        graph: &specification.graph,
        options,
        keys: FastSet::default(),
        entries: Vec::new(),
        is_other_bug: false,
    };
    let modules = if options.is_restricted {
        std::slice::from_ref(&specification.root)
    } else {
        &specification.modules
    };
    let module_references = exporter.get_references(modules)?;
    let capacity = get_hash_map_capacity(exporter.entries.len());
    let mut entries = exporter.entries;
    entries.sort_by_key(|&(uid, _)| get_hash_map_bucket(uid, capacity));
    let context = create_element(
        "context",
        entries
            .into_iter()
            .map(|(uid, element)| create_element("entry", vec![create_text("UID", uid), element]))
            .collect(),
    );
    let Some(root) = specification.graph.node(specification.root).symbol_name() else {
        not_yet("a root module that is no module")?
    };
    let mut children = vec![create_text("RootModule", root), context];
    children.extend(module_references);
    Ok(create_element("modules", children))
}

/// `exportSanyXml`: the specification SANY accepts, level-checked, as SANY's
/// tla2sany.xml.XMLExporter prints it with -o and the given options: every module the root module
/// depends on, the standard modules among them, with the level of every expression. The outer
/// result is the port's, `NotYet` where the TypeScript throws an internal error; the inner is the
/// exporter's, an error it reports with an exit code.
pub fn export_sany_xml(
    specification: &SanySpecification,
    options: &XmlExportOptions,
) -> Result<std::result::Result<String, XmlExportError>> {
    let document = match export_specification(specification, options) {
        Ok(document) => document,
        Err(Thrown::Export(error)) => return Ok(Err(error)),
        Err(Thrown::Front(error)) => return Err(error),
    };
    if let Some((tag, code_point)) = find_unrepresentable(&document) {
        return Ok(Err(XmlExportError {
            message: get_unrepresentable_message(tag, code_point),
            exit_code: XML_EXPORT_UNREPRESENTABLE_CHARACTER,
            is_exception: false,
        }));
    }
    let mut lines = vec![r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>"#.to_owned()];
    let indent_amount = if options.is_terse { 0 } else { 2 };
    print_element(&document, 0, indent_amount, &mut lines);
    Ok(Ok(if options.is_terse {
        lines.concat()
    } else {
        format!("{}\n", lines.join("\n"))
    }))
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::{
        Data, Element, XmlExportOptions, create_element, create_text, escape_xml, export_sany_xml,
        find_unrepresentable_in, get_hash_map_bucket, get_hash_map_capacity,
        get_unrepresentable_message, get_utf16, print_element, trim_end_javascript, trim_java,
        unbox_backslash_star_comment, unbox_comment,
    };
    use crate::sany::SanySpecification;
    use crate::sany::nodes::{Context, Graph, Module, NodeKind, SanyLocation};

    fn get_text(units: &[u16]) -> String {
        String::from_utf16(units).expect("no lone surrogate")
    }

    // The expected outputs are those of the helpers of `xml.ts`, run with Bun.
    #[test]
    fn unboxes_comments_by_utf16_index() {
        let cases = [
            (
                "(*****)\n(* Hello  *)\n(* wörld\u{A0}\u{3000}\u{2007} *)\n(*****)",
                "Hello\nwörld\u{A0}\u{3000}\u{2007}",
            ),
            ("(**)\n(* x *)", "(**)\n(* x *)"),
            ("no box", "no box"),
            ("(**\r\n(* ab\u{2001}\t *)\r\n**)\r\n\r\n", "ab"),
            ("(** a **)\n(* b *)", "(** a **)\n(* b *)"),
            ("(**\n(*)\n(* a\n**)", "\n(* a"),
        ];
        for (text, expected) in cases {
            assert_eq!(get_text(&unbox_comment(&get_utf16(text))), expected);
        }
    }

    #[test]
    fn unboxing_a_comment_may_split_a_surrogate_pair() {
        let unboxed = unbox_comment(&get_utf16("(**\n(*é é*)\n(*\u{1F600} rest *)\n**)"));
        assert_eq!(unboxed, [32, 233, 10, 56832, 32, 114, 101, 115, 116]);
        assert_eq!(find_unrepresentable_in(&Data::Cdata(unboxed)), Some(0xDE00));
    }

    #[test]
    fn unboxes_backslash_star_comments() {
        let cases = [
            (
                "\\* one\n\\*two\nplain\n  \\*  three",
                "one\ntwo\nplain\n three",
            ),
            ("a\nb\nc\n\\* d", "a\nb\nc\n\\* d"),
            ("\u{1}\\* ctrl\n\u{A0}\\* nbsp", "ctrl\n\u{A0}\\* nbsp"),
            ("\\*", ""),
            ("\\* x\n\n\n", "x"),
            ("é\\* é\r\n\\*\u{1F600}", "é\\* é\n\u{1F600}"),
        ];
        for (text, expected) in cases {
            assert_eq!(
                get_text(&unbox_backslash_star_comment(&get_utf16(text))),
                expected
            );
        }
    }

    #[test]
    fn trims_as_java_and_javascript_do() {
        assert_eq!(
            get_text(trim_java(&get_utf16("\u{0}\u{1F} a b \u{20}\u{1}"))),
            "a b"
        );
        assert_eq!(
            get_text(trim_java(&get_utf16("\u{A0}x\u{A0}"))),
            "\u{A0}x\u{A0}"
        );
        assert_eq!(trim_end_javascript("a \u{85}"), "a \u{85}");
        assert_eq!(trim_end_javascript("b\u{FEFF}\t\u{A0}"), "b");
        assert_eq!(trim_end_javascript("c\u{180E}"), "c\u{180E}");
    }

    #[test]
    fn escapes_characters_outside_the_basic_plane() {
        assert_eq!(
            escape_xml("a&b<c>d\r\n\u{1F600}é\u{10FFFF}"),
            "a&amp;b&lt;c&gt;d&#13;\n&#128512;é&#1114111;"
        );
    }

    #[test]
    fn finds_unrepresentable_characters() {
        let text = |text: &str| find_unrepresentable_in(&Data::Text(text.to_owned()));
        assert_eq!(text("x\u{1}"), Some(0x1));
        assert_eq!(text("\u{FFFE}"), Some(0xFFFE));
        assert_eq!(text("ok\u{FFFF}"), Some(0xFFFF));
        assert_eq!(text("\u{1F600}\u{8}"), Some(0x8));
        assert_eq!(text("\t\n\r\u{D7FF}\u{E000}\u{FFFD}\u{10FFFF}"), None);
        let lone = |units: &[u16]| find_unrepresentable_in(&Data::Cdata(units.to_vec()));
        assert_eq!(lone(&[97, 0xD83D]), Some(0xD83D));
        assert_eq!(lone(&[0xDE00, 98]), Some(0xDE00));
        assert_eq!(
            get_unrepresentable_message("StringValue", 0x1),
            "The spec contains the character U+0001 in the StringValue element. XML 1.0 cannot represent that character in character data, not even as a numeric character reference, so the spec cannot be exported until the character is removed from it."
        );
        assert!(get_unrepresentable_message("x", 0xDE00).contains("U+DE00 in the x element"));
    }

    #[test]
    fn lists_keys_as_java_hash_map_key_set_does() {
        // Recorded from OpenJDK 21: the keySet of a HashMap<Integer, Integer> after putIfAbsent
        // of the first `size` keys, a bucket holding its keys in the order they were added.
        let keys = [
            227, 256, 1, 65536, 65537, 131_071, 300, 5000, 12, 99999, 70000, 15, 31, 47, 63,
            1_000_003, 2048, 4096, 4095, 8191, 256, 512, 33, 17,
        ];
        let recorded: [(usize, &[u32]); 4] = [
            (1, &[227]),
            (
                12,
                &[
                    256, 65537, 1, 65536, 70000, 227, 5000, 300, 12, 131_071, 99999, 15,
                ],
            ),
            (
                13,
                &[
                    256, 65537, 1, 65536, 227, 5000, 300, 12, 15, 70000, 131_071, 99999, 31,
                ],
            ),
            (
                24,
                &[
                    256, 65537, 2048, 4096, 512, 1, 65536, 33, 227, 5000, 300, 12, 1_000_003, 15,
                    47, 70000, 17, 131_071, 99999, 31, 63, 4095, 8191,
                ],
            ),
        ];
        for (size, expected) in recorded {
            let mut added: Vec<u32> = Vec::new();
            for &key in &keys[..size] {
                if !added.contains(&key) {
                    added.push(key);
                }
            }
            let capacity = get_hash_map_capacity(added.len());
            added.sort_by_key(|&key| get_hash_map_bucket(key, capacity));
            assert_eq!(added, expected, "the first {size} keys");
        }
    }

    #[test]
    fn orders_entries_as_a_java_hash_map() {
        let sizes = [(0, 16), (12, 16), (13, 32), (24, 32), (25, 64), (100, 256)];
        for (size, capacity) in sizes {
            assert_eq!(get_hash_map_capacity(size), capacity);
        }
        let keys = [1, 17, 65536, 65537, 123_456_789, u32::MAX, 33, 2, 16];
        let get_order = |capacity: usize| {
            let mut sorted = keys;
            sorted.sort_by_key(|&key| get_hash_map_bucket(key, capacity));
            sorted
        };
        assert_eq!(
            get_order(16),
            [65537, u32::MAX, 16, 1, 17, 65536, 33, 2, 123_456_789]
        );
        assert_eq!(
            get_order(64),
            [65537, u32::MAX, 1, 65536, 2, 123_456_789, 16, 17, 33]
        );
    }

    #[test]
    fn prints_empty_content_as_an_empty_element() {
        let cdata = |units: Vec<u16>| Element {
            tag: "pre-comments",
            data: Data::Cdata(units),
            children: Vec::new(),
        };
        let document = create_element(
            "modules",
            vec![
                create_text("RootModule", "M"),
                create_element("context", Vec::new()),
                cdata(get_utf16("a]]>b")),
                cdata(Vec::new()),
                create_text("x", ""),
                create_text("StringValue", "<&>"),
            ],
        );
        let mut lines = Vec::new();
        print_element(&document, 0, 2, &mut lines);
        assert_eq!(
            lines,
            [
                "<modules>",
                "  <RootModule>M</RootModule>",
                "  <context/>",
                "  <pre-comments><![CDATA[a]]]]><![CDATA[>b]]></pre-comments>",
                "  <pre-comments/>",
                "  <x/>",
                "  <StringValue>&lt;&amp;&gt;</StringValue>",
                "</modules>",
            ]
        );
    }

    #[test]
    fn exports_a_module_and_its_context() {
        let mut graph = Graph::default();
        let root = graph.add(
            5,
            NodeKind::Module(Box::new(Module {
                name: Rc::from("M"),
                location: SanyLocation {
                    file: Rc::from("M"),
                    begin_line: 1,
                    begin_column: 1,
                    end_line: 3,
                    end_column: 2,
                },
                extendees: Vec::new(),
                context: Context::default(),
                top_level: Vec::new(),
                definitions: Vec::new(),
                op_defs_in_recursive_section: Vec::new(),
                is_level_checked: true,
                records: Vec::new(),
            })),
        );
        let specification = SanySpecification {
            graph,
            root,
            modules: vec![root],
            messages: Vec::new(),
            builtins: Vec::new(),
        };
        let lines = [
            r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>"#,
            "<modules>",
            "  <RootModule>M</RootModule>",
            "  <context>",
            "    <entry>",
            "      <UID>5</UID>",
            "      <ModuleNode>",
            "        <location>",
            "          <column>",
            "            <begin>1</begin>",
            "            <end>2</end>",
            "          </column>",
            "          <line>",
            "            <begin>1</begin>",
            "            <end>3</end>",
            "          </line>",
            "          <filename>M</filename>",
            "        </location>",
            "        <uniquename>M</uniquename>",
            "        <extends/>",
            "      </ModuleNode>",
            "    </entry>",
            "  </context>",
            "  <ModuleNodeRef>",
            "    <UID>5</UID>",
            "  </ModuleNodeRef>",
            "</modules>",
        ];
        let export = |options: XmlExportOptions| {
            export_sany_xml(&specification, &options)
                .expect("exported")
                .expect("no export error")
        };
        assert_eq!(
            export(XmlExportOptions::default()),
            format!("{}\n", lines.join("\n"))
        );
        let terse = XmlExportOptions {
            is_terse: true,
            ..XmlExportOptions::default()
        };
        assert_eq!(export(terse), lines.map(str::trim_start).concat());
    }
}
