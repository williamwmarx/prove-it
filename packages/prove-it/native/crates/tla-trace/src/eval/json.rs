use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Value,
    Array,
    Object,
}

impl Evaluator<'_> {
    pub(super) fn json_conversion(&mut self, name: &str, value: &Value) -> Evaluated<Value> {
        let (method, mode) = match name {
            "ToJsonArray" => ("toJsonArray", Mode::Array),
            "ToJsonObject" => ("toJsonObject", Mode::Object),
            _ => ("toJson", Mode::Value),
        };
        let signature = format!(
            "public static tlc2.value.impl.StringValue tlc2.module.Json.{method}(tlc2.value.IValue) throws java.io.IOException"
        );
        let mut text = Vec::new();
        let converted = self.json_node(value, mode, 0, &mut text);
        let is_null_pointer = converted
            .as_ref()
            .is_err_and(|error| error.runtime_exception == RuntimeException::NullPointer);
        as_java_runtime_failure(&signature, converted).map_err(|mut error| {
            if is_null_pointer && let Some(message) = &mut error.message {
                message.is_eval_exception = true;
            }
            error
        })?;
        Ok(Value::Str(self.made_text(text.into_boxed_slice())))
    }

    fn json_node(
        &mut self,
        value: &Value,
        mode: Mode,
        depth: usize,
        out: &mut Vec<u16>,
    ) -> Evaluated<()> {
        if depth > 256 {
            return fail("a Json conversion nested too deeply");
        }
        if matches!(value, Value::Null) {
            return fail_runtime(
                "a Json conversion of an uninitialized tool value",
                "Cannot invoke \"tlc2.value.IValue.getClass()\" because \"value\" is null".into(),
            )
            .map_err(|mut error| {
                error.runtime_exception = RuntimeException::NullPointer;
                error
            });
        }
        if let Value::Function(function) = value {
            let Some(class) = function.java_class.get() else {
                return fail("a Json conversion whose physical function class was not retained");
            };
            if class == Class::Record && mode == Mode::Array {
                return match function.is_counter_example.get() {
                    Some(true) => unsupported_class("CounterExample"),
                    Some(false) => unsupported_class("RecordValue"),
                    None => fail("a Json conversion whose record subtype was not retained"),
                };
            }
            let all_ints = function
                .domain
                .iter()
                .all(|key| matches!(key, Value::Int(_)));
            let array = class == Class::Tuple && mode != Mode::Object
                || matches!(class, Class::Plain | Class::Lambda)
                    && function.domain.iter().enumerate().all(|(index, key)| {
                        matches!(key, Value::Int(number) if i64::from(*number) == index as i64 + 1)
                    });
            let order: Vec<usize> = if class == Class::Tuple
                || class == Class::Lambda
                || class == Class::Plain && all_ints
            {
                (0..function.range.len()).collect()
            } else {
                if !function_order_is_known(function) {
                    return fail(
                        "a Json conversion whose physical function order was not retained",
                    );
                }
                match &*function.written.borrow() {
                    Some(order) => order.iter().map(|&index| index as usize).collect(),
                    None => (0..function.range.len()).collect(),
                }
            };
            out.push(u16::from(if array { b'[' } else { b'{' }));
            let mut fields: Vec<(Vec<u16>, Vec<u16>)> = Vec::new();
            for (index, position) in order.into_iter().enumerate() {
                if array && index > 0 {
                    out.push(u16::from(b','));
                }
                if !array {
                    let key = if class == Class::Tuple {
                        index.to_string().encode_utf16().collect::<Vec<_>>()
                    } else if let Value::Str(text) = &function.domain[position] {
                        text.units.to_vec()
                    } else {
                        let key = &function.domain[position];
                        check_merge_argument_format(key)?;
                        if holds_unknown_function_order(key) || holds_unknown_key(key) {
                            return fail(
                                "a Json conversion key whose default text was not retained",
                            );
                        }
                        format_units(key)
                    };
                    let mut text = Vec::new();
                    self.json_node(&function.range[position], Mode::Value, depth + 1, &mut text)?;
                    if let Some((_, previous)) = fields.iter_mut().find(|(name, _)| *name == key) {
                        *previous = text;
                    } else {
                        fields.push((key, text));
                    }
                } else {
                    self.json_node(&function.range[position], Mode::Value, depth + 1, out)?;
                }
            }
            for (index, (key, text)) in fields.into_iter().enumerate() {
                if index > 0 {
                    out.push(u16::from(b','));
                }
                write_string(&key, out)?;
                out.push(u16::from(b':'));
                out.extend(text);
            }
            out.push(u16::from(if array { b']' } else { b'}' }));
            return Ok(());
        }
        if let Value::Lambda(lambda) = value {
            return lambda_as_function(lambda);
        }
        if value.is_set() || matches!(value, Value::Unsorted(_)) {
            let Some(class) = java_set_class(value) else {
                return fail("a Json conversion whose physical set class was not retained");
            };
            if mode == Mode::Object || class == SetClass::Overridden {
                return unsupported_class(class.java_name());
            }
            let input = self.filter_input(value)?;
            let enumeration = Value::set(input.as_ref().clone());
            let elements = elements(&enumeration)?;
            out.push(u16::from(b'['));
            for (index, element) in elements.iter().enumerate() {
                if index > 0 {
                    out.push(u16::from(b','));
                }
                self.json_node(element, Mode::Value, depth + 1, out)?;
            }
            out.push(u16::from(b']'));
            return Ok(());
        }
        if mode != Mode::Value {
            return unsupported_class(java_value_class(value));
        }
        match value {
            Value::Bool(value) => out.extend(if *value { "true" } else { "false" }.encode_utf16()),
            Value::Int(value) => out.extend(value.to_string().encode_utf16()),
            Value::Str(text) | Value::Model(text) => write_string(&text.units, out)?,
            _ => return fail("a Json conversion of an unsupported value"),
        }
        Ok(())
    }
}

fn unsupported_class<T>(class: &str) -> Evaluated<T> {
    fail_runtime(
        "a Json conversion of an unsupported physical value class",
        format!("Cannot convert value: unsupported value type tlc2.value.impl.{class}"),
    )
}

fn write_string(text: &[u16], out: &mut Vec<u16>) -> Evaluated<()> {
    if String::from_utf16(text).is_err() {
        return fail("a Json conversion of a string with a lone surrogate");
    }
    out.push(u16::from(b'"'));
    for &unit in text {
        let escape = match unit {
            0x22 => Some("\\\""),
            0x5c => Some("\\\\"),
            8 => Some("\\b"),
            9 => Some("\\t"),
            10 => Some("\\n"),
            12 => Some("\\f"),
            13 => Some("\\r"),
            _ => None,
        };
        if let Some(escape) = escape {
            out.extend(escape.encode_utf16());
        } else if unit < 0x20 || matches!(unit, 0x2028 | 0x2029) {
            out.extend(format!("\\u{unit:04x}").encode_utf16());
        } else {
            out.push(unit);
        }
    }
    out.push(u16::from(b'"'));
    Ok(())
}

const DESERIALIZE: &str = "public static tlc2.value.IValue tlc2.module.Json.deserialize(tlc2.value.impl.StringValue) throws java.io.IOException";
const ND_DESERIALIZE: &str = "public static tlc2.value.IValue tlc2.module.Json.ndDeserialize(tlc2.value.impl.StringValue) throws java.io.IOException";
const SERIALIZE: &str = "public static synchronized tlc2.value.impl.BoolValue tlc2.module.Json.serialize(tlc2.value.impl.StringValue,tlc2.value.impl.Value) throws java.io.IOException";
const ND_SERIALIZE: &str = "public static synchronized tlc2.value.impl.BoolValue tlc2.module.Json.ndSerialize(tlc2.value.impl.StringValue,tlc2.value.impl.Value) throws java.io.IOException";

/// The builtins whose effect TLC repeats where it computes a constant definition again.
const STARTUP_EFFECTS: &[&str] = &[
    "Print",
    "PrintT",
    "AssertEq",
    "TLCSet",
    "TLCGetAndSet",
    "RandomElement",
    "RandomSubset",
    "RandomSubsetSet",
    "RandomSetOfSubsets",
    "TestRandomSetOfSubsets",
    "JavaTime",
];

/// The builtins by which a model may write a file before the replay reads it.
const FILE_WRITERS: &[&str] = &[
    "JsonSerialize",
    "ndJsonSerialize",
    "IOExec",
    "IOEnvExec",
    "IOExecTemplate",
    "IOEnvExecTemplate",
];

impl Evaluator<'_> {
    /// What fails as TLC applies one of the Json module's operators that read and write files to
    /// its arguments' values: `MethodValue`'s cast of the file to a StringValue, the check of
    /// what `Json.serialize` and `Json.ndSerialize` write, writing to a directory, and what
    /// `Json.deserialize` and `Json.ndDeserialize` throw reading a file. Where it finds none,
    /// the replay doesn't follow the operator.
    pub(super) fn json_file_failure(&mut self, name: &str, values: &[Value]) -> Evaluated<()> {
        let failure = self.json_file_failure_unchecked(name, values);
        if failure.as_ref().is_err_and(|error| error.message.is_some())
            || failure.is_ok() && name.ends_with("Serialize")
        {
            // TLC computes a constant definition as it starts and again where it's used, where
            // that fails (`processConstantDefns`): what such a definition printed, drew or set
            // before it failed it does twice, which the replay doesn't.
            if self
                .ir
                .builtins
                .iter()
                .any(|builtin| STARTUP_EFFECTS.contains(&&*self.ir.texts[builtin.name as usize]))
                || self.ir.model.is_warning_enabled
                    && self
                        .ir
                        .nodes
                        .arena
                        .iter()
                        .any(|node| matches!(node.kind, NodeKind::Except { .. }))
            {
                return fail("a Json operator's failure in a model with effects");
            }
        }
        failure?;
        if name.ends_with("Serialize") {
            return self.json_written_failure(name, values);
        }
        Ok(())
    }

    /// `Json.serialize` and `Json.ndSerialize` past what fails before the file opens: they make
    /// the file's directories (`File.mkdirs`) and open it (`FileWriter`), emptying it, then write
    /// what `getNode` converts, ndJsonSerialize a line for each element, which fails on a value
    /// of a class it can't convert. Where the conversion fails, the replay does to the file what
    /// TLC did, writing the lines before the one that fails, which `BufferedWriter.close`
    /// flushes, and words the failure; where it doesn't, or the file doesn't open, the replay
    /// finds no failure.
    fn json_written_failure(&mut self, name: &str, values: &[Value]) -> Evaluated<()> {
        let [Value::Str(path), value] = values else {
            return Ok(());
        };
        if !self.reads_files {
            return Ok(());
        }
        let is_lines = name == "ndJsonSerialize";
        let payload = if is_lines {
            let Some(elements) = as_tuple(value) else {
                return Ok(());
            };
            elements.to_vec()
        } else {
            vec![value.clone()]
        };
        let mut written = Vec::new();
        let mut failure = None;
        for element in &payload {
            let mut text = Vec::new();
            match self.json_node(element, Mode::Value, 0, &mut text) {
                Ok(()) => {
                    written.extend(text);
                    if is_lines {
                        written.push(u16::from(b'\n'));
                    }
                }
                Err(error) => {
                    failure = Some(error);
                    break;
                }
            }
        }
        let Some(error) = failure else {
            return Ok(());
        };
        if error.message.is_none() {
            return Err(error);
        }
        let Ok(path) = String::from_utf16(&path.units) else {
            return fail("a Json operator's file with a lone surrogate");
        };
        if path.is_empty() || path.contains("//") || path.ends_with('/') {
            return fail("a Json operator's file that Java's File holds otherwise");
        }
        let Ok(written) = String::from_utf16(&written) else {
            return fail("a Json operator's text with a lone surrogate");
        };
        let file = std::path::Path::new(&path);
        if let Some(parent) = file
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
        {
            let _ = tla_values::written::create_dir_all(parent);
        }
        if tla_values::written::keep_file(file).is_err() {
            return fail("a Json operator's file that can't be read before it is written");
        }
        if std::fs::write(file, written).is_err() {
            return fail("a Json operator's file that TLC may fail to open");
        }
        let signature = if is_lines { ND_SERIALIZE } else { SERIALIZE };
        let is_null_pointer = error.runtime_exception == RuntimeException::NullPointer;
        as_java_runtime_failure(signature, Err(error)).map_err(|mut error| {
            if is_null_pointer && let Some(message) = &mut error.message {
                message.is_eval_exception = true;
            }
            error
        })
    }

    fn json_file_failure_unchecked(&mut self, name: &str, values: &[Value]) -> Evaluated<()> {
        let signature = match name {
            "JsonDeserialize" => DESERIALIZE,
            "ndJsonDeserialize" => ND_DESERIALIZE,
            "JsonSerialize" => SERIALIZE,
            _ => ND_SERIALIZE,
        };
        let path = match &values[0] {
            Value::Str(text) => text.units.clone(),
            value => {
                let Some(class) = numeric_value_class(value) else {
                    return fail("a Json operator's file of an unknown physical class");
                };
                return as_java_runtime_failure(
                    signature,
                    fail_runtime(
                        "a Json operator's file that isn't a string",
                        format!(
                            "Cannot cast tlc2.value.impl.{class} to tlc2.value.impl.StringValue"
                        ),
                    ),
                );
            }
        };
        let Ok(path) = String::from_utf16(&path) else {
            return fail("a Json operator's file with a lone surrogate");
        };
        if path.contains('\0') {
            return fail("a Json operator's file that Java's File holds invalid");
        }
        if let [_, value] = values {
            // `Value.toTuple`, then for JsonSerialize `Value.toRcd`.
            let is_written = match value {
                Value::Function(function) => {
                    let mut keys = Vec::with_capacity(function.domain.len());
                    for key in function.domain.iter() {
                        match key {
                            Value::Int(key) => keys.push(i64::from(*key)),
                            _ => break,
                        }
                    }
                    keys.sort_unstable();
                    let is_tuple = keys.len() == function.domain.len()
                        && keys
                            .iter()
                            .enumerate()
                            .all(|(index, key)| *key == index as i64 + 1);
                    is_tuple
                        || name == "JsonSerialize"
                            && function
                                .domain
                                .iter()
                                .all(|key| matches!(key, Value::Str(_)))
                }
                Value::Lambda(_) | Value::Null => {
                    return fail("a Json operator's value of a lazy function");
                }
                _ => false,
            };
            if !is_written {
                if crate::value::contains_uninitialized(value) {
                    return fail(
                        "formatting a Json operator's value containing an uninitialized literal",
                    );
                }
                let expected = if name == "JsonSerialize" {
                    "sequence or record"
                } else {
                    "sequence"
                };
                return module_argument("second", name, expected, value);
            }
            // `FileWriter` fails on a directory, before the value is converted.
            if self.reads_files && std::path::Path::new(&path).is_dir() {
                return as_java_runtime_failure(
                    signature,
                    fail_runtime(
                        "a Json operator's file that can't be written",
                        format!("{} (Is a directory)", tla_values::java_file_path(&path)),
                    ),
                );
            }
            return Ok(());
        }
        // Where the model may write a file, what the replay reads needn't be what TLC read.
        // IOUtils's Serialize, a definition TLC overrides, writes one too.
        if !self.reads_files
            || self
                .ir
                .builtins
                .iter()
                .any(|builtin| FILE_WRITERS.contains(&&*self.ir.texts[builtin.name as usize]))
            || self.ir.texts.iter().any(|text| &**text == "Serialize")
        {
            return Ok(());
        }
        let message = match std::fs::read(&path) {
            Err(error) => {
                let Some(code) = error.raw_os_error() else {
                    return fail("a Json operator's file that can't be read");
                };
                let reason = std::io::Error::from_raw_os_error(code).to_string();
                let Some(reason) = reason.strip_suffix(&format!(" (os error {code})")) else {
                    return fail("a Json operator's file that can't be read");
                };
                format!("{} ({reason})", tla_values::java_file_path(&path))
            }
            Ok(bytes) => {
                let text = tla_values::json::decode_file_text(&bytes);
                let is_lines = name == "ndJsonDeserialize";
                let failure = tla_values::json::read_failure(&text, is_lines);
                let Some(message) = failure.or_else(|bail| fail(bail.0))? else {
                    return Ok(());
                };
                let Ok(message) = String::from_utf16(&message) else {
                    return fail("a Json operator's failure with a lone surrogate");
                };
                message
            }
        };
        as_java_runtime_failure(
            signature,
            fail_runtime("a Json operator's file that TLC fails to read", message),
        )
    }
}

/// The names `StandardOpenOption.valueOf` takes.
const OPEN_OPTIONS: &[&str] = &[
    "READ",
    "WRITE",
    "APPEND",
    "TRUNCATE_EXISTING",
    "CREATE",
    "CREATE_NEW",
    "DELETE_ON_CLOSE",
    "SPARSE",
    "SYNC",
    "DSYNC",
];

/// `(StringValue) value` of an option `Json.textSerialize` reads, which fails with Java's
/// ClassCastException where the value is no string.
pub(super) fn string_cast<T>(value: &Value) -> Evaluated<T> {
    class_cast(value, "StringValue")
}

fn class_cast<T>(value: &Value, class: &str) -> Evaluated<T> {
    let Some(from) = numeric_value_class(value) else {
        return fail("a cast in Serialize of a value whose TLC class is unknown");
    };
    fail_runtime(
        "a cast in Serialize of a value of another class",
        format!(
            "class tlc2.value.impl.{from} cannot be cast to class tlc2.value.impl.{class} (tlc2.value.impl.{from} and tlc2.value.impl.{class} are in unnamed module of loader 'app')"
        ),
    )
}

impl Evaluator<'_> {
    /// `opts.apply(new StringValue(name))` of the record `Json.textSerialize` makes of its
    /// options (`Value.toRcd`), which fails on a field the record lacks.
    pub(super) fn serialize_option(
        &mut self,
        options: &Value,
        fields: &Function,
        name: &str,
    ) -> Evaluated<Value> {
        // `RecordValue.apply` takes a field whose value TLC never initialized, null, for one
        // the record lacks.
        if let Some(position) = fields
            .domain
            .iter()
            .position(|key| matches!(key, Value::Str(text) if is_text(text, name)))
            && !matches!(fields.range[position], Value::Null)
        {
            return Ok(fields.range[position].clone());
        }
        // A RecordValue prints as it holds its fields; another function `toRcd` converts.
        if fields.java_class.get() != Some(Class::Record) {
            return fail("an option Serialize's options lack, of a function TLC converts");
        }
        // Json.textSerialize reports the NullPointerException `toString` throws as its own
        // failure, as it does the EvalException.
        if let Some(npe) = record_null_failure(options) {
            return match npe {
                Some(message) => fail_runtime("an option Serialize's options lack", message),
                None => fail("an option Serialize's options lack, printing a nested null"),
            };
        }
        let key = Value::Str(self.text_of(name.encode_utf16().collect()));
        match describe_missing(options, Class::Record, &key) {
            Some(message) => fail_runtime("an option Serialize's options lack", message),
            None => fail("an option Serialize's options lack"),
        }
    }

    /// `Json.textSerialize` with the NDJSON format, up to where it opens the file: its payload,
    /// which `Value.toTuple` takes, its file, its options and charset, each cast as it reads
    /// them, then `Charset.forName`, `StandardOpenOption.valueOf` and the open, whose exceptions
    /// it throws as a RuntimeException's cause. A file it would write declines: the replay
    /// doesn't write.
    pub(super) fn text_serialize_lines(
        &mut self,
        args: &[NodeId],
        context: &Context,
        options: &Value,
        fields: &Function,
    ) -> Evaluated<Value> {
        let first = self.evaluate(args[0], context)?;
        if matches!(first, Value::Lambda(_) | Value::Null) {
            return fail("Serialize of a lazy function");
        }
        if as_tuple(&first).is_none() {
            if crate::value::contains_uninitialized(&first) {
                return fail("formatting Serialize's payload containing an uninitialized literal");
            }
            return module_argument("first", "Serialize", "sequence", &first);
        }
        let second = self.evaluate(args[1], context)?;
        let Value::Str(path) = &second else {
            if crate::value::contains_uninitialized(&second) {
                return fail("formatting Serialize's file containing an uninitialized literal");
            }
            return module_argument("second", "ndJsonSerialize", "sequence", &second);
        };
        let open_options = self.serialize_option(options, fields, "openOptions")?;
        let open_options = match &open_options {
            Value::Function(function) if function.java_class.get() == Some(Class::Tuple) => {
                function.range.clone()
            }
            other => return class_cast(other, "TupleValue"),
        };
        let charset = match self.serialize_option(options, fields, "charset")? {
            Value::Str(charset) => charset,
            other => return string_cast(&other),
        };
        let mut names = Vec::with_capacity(open_options.len());
        for option in &open_options {
            match option {
                Value::Str(name) => names.push(String::from_utf16_lossy(&name.units)),
                other => return string_cast(other),
            }
        }
        let Ok(path) = String::from_utf16(&path.units) else {
            return fail("Serialize's file with a lone surrogate");
        };
        // `Paths.get` drops a repeated or final slash, which the exception's path would show.
        if path.is_empty() || path.contains('\0') || path.contains("//") || path.ends_with('/') {
            return fail("Serialize's file that Java's Paths holds otherwise");
        }
        let failure =
            |message: String| fail_runtime("Serialize's file that TLC fails to open", message);
        // `Charset.forName` finds a charset the JVM knows by its name or an alias, whatever the
        // case of its ASCII letters, and otherwise checks the name (`Charset.checkName`): a
        // letter or digit, then letters, digits and `-+:_.`.
        let Ok(charset) = String::from_utf16(&charset.units) else {
            return fail("Serialize's charset with a lone surrogate");
        };
        if super::charsets::JVM_CHARSETS
            .binary_search(&charset.to_ascii_lowercase().as_str())
            .is_err()
        {
            let is_legal = charset.char_indices().all(|(index, letter)| {
                letter.is_ascii_alphanumeric()
                    || index > 0 && matches!(letter, '-' | '+' | ':' | '_' | '.')
            }) && !charset.is_empty();
            let exception = if is_legal {
                "UnsupportedCharsetException"
            } else {
                "IllegalCharsetNameException"
            };
            return failure(format!("java.nio.charset.{exception}: {charset}"));
        }
        // `Files.newBufferedWriter` makes the charset's encoder before it opens the file, which a
        // charset that only decodes refuses.
        if matches!(
            charset.to_ascii_lowercase().as_str(),
            "iso-2022-cn" | "csiso2022cn" | "iso2022cn" | "x-jisautodetect" | "jisautodetect"
        ) {
            return fail("Serialize's charset, which only decodes");
        }
        if let Some(name) = names
            .iter()
            .find(|name| !OPEN_OPTIONS.contains(&name.as_str()))
        {
            return failure(format!(
                "java.lang.IllegalArgumentException: No enum constant java.nio.file.StandardOpenOption.{name}"
            ));
        }
        // `Files.newOutputStream` and the channel it opens check the options' combinations, then
        // open the file, which fails where the file or its directory is missing.
        let is_followed = names.iter().all(|name| {
            matches!(
                name.as_str(),
                "WRITE" | "CREATE" | "CREATE_NEW" | "TRUNCATE_EXISTING" | "APPEND"
            )
        }) && !(names.iter().any(|name| name == "APPEND")
            && names.iter().any(|name| name == "TRUNCATE_EXISTING"));
        if !is_followed
            || !self.reads_files
            || self.ir.builtins.iter().any(|builtin| {
                let name = &*self.ir.texts[builtin.name as usize];
                FILE_WRITERS.contains(&name) || STARTUP_EFFECTS.contains(&name)
            })
        {
            return fail("IOUtils's Serialize with the NDJSON format");
        }
        let is_created = names
            .iter()
            .any(|name| matches!(name.as_str(), "CREATE" | "CREATE_NEW"))
            || names.is_empty();
        if let Some(made_paths) = &self.made_paths
            && let Some(missing) = count_missing(std::path::Path::new(&path))
            && (missing > 1 || (missing == 1 && !is_created))
            && !is_made_path(std::path::Path::new(&path), made_paths)
        {
            return failure(format!("java.nio.file.NoSuchFileException: {path}"));
        }
        fail("IOUtils's Serialize with the NDJSON format")
    }
}

/// How many of the path's last names nothing is at, where the nearest path above them that is there
/// is a directory, so that opening the file fails on the first of them with ENOENT, which Java
/// reports as a `NoSuchFileException`. `None` where something on the path is there and isn't a
/// directory (ENOTDIR, or EISDIR for the file itself), where a dangling link is, or where the system
/// fails otherwise, whose exceptions Java words otherwise.
fn count_missing(path: &std::path::Path) -> Option<usize> {
    let mut missing = 0;
    for ancestor in path.ancestors() {
        let ancestor = if ancestor.as_os_str().is_empty() {
            std::path::Path::new(".")
        } else {
            ancestor
        };
        match std::fs::metadata(ancestor) {
            Ok(metadata) => return (metadata.is_dir() && missing > 0).then_some(missing),
            Err(error)
                if error.kind() == std::io::ErrorKind::NotFound
                    && std::fs::symlink_metadata(ancestor).is_err() =>
            {
                missing += 1;
            }
            Err(_) => return None,
        }
    }
    None
}

/// Whether the path is, holds, or is held by one TLC made before it evaluated anything, where TLC
/// finds a directory or a file the replay doesn't. Each is compared by its real path, as far as it
/// is there; a path through `..` counts as made, since what it names depends on what is there.
fn is_made_path(path: &std::path::Path, made_paths: &[std::path::PathBuf]) -> bool {
    let Some(path) = get_real_path(path) else {
        return true;
    };
    made_paths.iter().any(|made| {
        get_real_path(made).is_none_or(|made| path.starts_with(&made) || made.starts_with(&path))
    })
}

/// The path's real path: that of the nearest path above it that is there, followed by the names
/// that aren't. `None` where a name that isn't there is `..`, or no path above it is there.
fn get_real_path(path: &std::path::Path) -> Option<std::path::PathBuf> {
    let path = std::path::absolute(path).ok()?;
    let mut rest = Vec::new();
    for ancestor in path.ancestors() {
        if let Ok(real) = std::fs::canonicalize(ancestor) {
            let mut real = real;
            for name in rest.iter().rev() {
                match name {
                    std::path::Component::Normal(name) => real.push(name),
                    _ => return None,
                }
            }
            return Some(real);
        }
        rest.push(ancestor.components().next_back()?);
    }
    None
}
