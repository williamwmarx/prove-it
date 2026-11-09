//! The command line, as `src/cli/run.ts` and `src/cli/options.ts` read it: the TLC options of
//! `prove-it <Spec>`, and the Java launch `prove-it [<JVM option>]... tlc2.TLC <option>... <Spec>`
//! that tools running TLC with Java use.

pub const USAGE: &str = "Usage: tla-ts <Spec.tla|Spec.cfg|glob>... [-config <Spec.cfg>] [-continue] [-deadlock] [-dump [<format>] <file>] [-fp <num>] [-lncheck <final|default>] [-metadir <directory>] [-nowarning] [-seed <num>] [-tool] [-workers <count|auto>]
       tla-ts tlapm [-N] [--summary] [--strict] [--toolbox <start> <end>] [--line <num>] [--printallobs] [--threads <num>] [--version] [-I <directory>]... [-k] [--noproving] [--nofp] [--nofpl <start> <end>] [--safefp] [--cleanfp] [--usefp <file>] [--cache-dir <directory>] <Module.tla|glob>...
       tla-ts [<JVM option>]... tlc2.TLC <TLC option>... <Spec>
       (-cp tla2tools.jar or -Dtla-ts.tlc=1.7.4 picks the TLC to reproduce)
       tla-ts [<JVM option>]... tla2sany.xml.XMLExporter [-I <directory>]... [-o] [-t] [-r] [-u] <Module.tla>";

const JAVA_MAIN_CLASSES: [&str; 2] = ["tlc2.TLC", "tla2sany.xml.XMLExporter"];

/// What the JVM options in front of TLC's set.
#[derive(Debug, Default, PartialEq)]
pub struct Java {
    pub libraries: Vec<String>,
    pub class_path: Option<String>,
    pub is_174: bool,
}

/// A Java launch: the main class, its arguments and the JVM's options.
#[derive(Debug, PartialEq)]
pub struct Launch {
    pub main_class: String,
    pub args: Vec<String>,
    pub java: Java,
}

pub fn get_java_launch(args: &[String]) -> Option<Launch> {
    let mut java = Java::default();
    let mut index = 0;
    while index < args.len() {
        let arg = &args[index];
        let rest = |from: usize| args.get(from..).unwrap_or_default().to_vec();
        if arg == "-cp" || arg == "-classpath" || arg == "--class-path" {
            index += 1;
            java.class_path = args.get(index).cloned();
        } else if arg == "-jar" {
            java.class_path = args.get(index + 1).cloned();
            return Some(Launch {
                main_class: "tlc2.TLC".into(),
                args: rest(index + 2),
                java,
            });
        } else if let Some(libraries) = arg.strip_prefix("-DTLA-Library=") {
            java.libraries
                .extend(libraries.split(':').map(String::from));
        } else if let Some(version) = arg.strip_prefix("-Dtla-ts.tlc=") {
            java.is_174 = version == "1.7.4";
        } else if !arg.starts_with("-D") && !arg.starts_with("-X") {
            let is_launch = index > 0 || JAVA_MAIN_CLASSES.contains(&arg.as_str());
            return is_launch.then(|| Launch {
                main_class: arg.clone(),
                args: rest(index + 1),
                java,
            });
        }
        index += 1;
    }
    None
}

/// The TLC options `CHECK_COMMAND` reads, with how many arguments each takes.
fn get_arity(flag: &str, rest: &[String]) -> Option<usize> {
    match flag {
        "-config" | "-fp" | "-lncheck" | "-metadir" | "-seed" | "-workers" => Some(1),
        "-continue" | "-deadlock" | "-nowarning" | "-tool" => Some(0),
        // Like TLC, -dump takes a format only when the next argument starts with dot and a file
        // follows.
        "-dump" => Some(if rest.len() > 1 && rest[0].starts_with("dot") {
            2
        } else {
            1
        }),
        _ => None,
    }
}

/// The options and specs of a check. Options TLC has that Prove It doesn't read are ignored.
#[derive(Debug, Default)]
pub struct Parsed {
    pub options: Vec<(String, Vec<String>)>,
    pub positionals: Vec<String>,
    pub unknown: Vec<String>,
}

impl Parsed {
    pub fn parse(args: &[String]) -> Self {
        let mut parsed = Self::default();
        let mut index = 0;
        while index < args.len() {
            let arg = &args[index];
            index += 1;
            let Some(arity) = get_arity(arg, &args[index..]) else {
                if arg.starts_with('-') {
                    parsed.unknown.push(arg.clone());
                } else {
                    parsed.positionals.push(arg.clone());
                }
                continue;
            };
            let end = (index + arity).min(args.len());
            parsed
                .options
                .push((arg.clone(), args[index..end].to_vec()));
            index += arity;
        }
        parsed
    }

    pub fn has(&self, name: &str) -> bool {
        self.options.iter().any(|(option, _)| option == name)
    }

    /// The values of the last time the option is given.
    pub fn get(&self, name: &str) -> Option<&[String]> {
        self.options
            .iter()
            .rev()
            .find(|(option, _)| option == name)
            .map(|(_, values)| values.as_slice())
    }

    pub fn first(&self, name: &str) -> Option<&str> {
        self.get(name)?.first().map(String::as_str)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(|&arg| arg.to_string()).collect()
    }

    #[test]
    fn reads_a_java_launch() {
        let launch = get_java_launch(&strings(&[
            "-DTLA-Library=/a:/b",
            "-Xmx4g",
            "tlc2.TLC",
            "-tool",
            "Spec",
        ]))
        .expect("a launch");
        assert_eq!(launch.main_class, "tlc2.TLC");
        assert_eq!(launch.args, strings(&["-tool", "Spec"]));
        assert_eq!(launch.java.libraries, strings(&["/a", "/b"]));
        assert_eq!(get_java_launch(&strings(&["Spec.tla", "-tool"])), None);
        let jar = get_java_launch(&strings(&["-jar", "tla2tools.jar", "Spec"])).expect("a jar");
        assert_eq!(jar.java.class_path.as_deref(), Some("tla2tools.jar"));
        assert_eq!(jar.args, strings(&["Spec"]));
    }

    #[test]
    fn reads_options_as_check_command() {
        let parsed = Parsed::parse(&strings(&[
            "-seed", "5", "-noTE", "-dump", "dot", "out", "Spec.tla", "-seed", "7", "-workers",
        ]));
        assert_eq!(parsed.positionals, strings(&["Spec.tla"]));
        assert_eq!(parsed.unknown, strings(&["-noTE"]));
        assert_eq!(parsed.first("-seed"), Some("7"));
        assert_eq!(
            parsed.get("-dump"),
            Some(strings(&["dot", "out"]).as_slice())
        );
        assert!(parsed.has("-workers"));
        assert_eq!(parsed.first("-workers"), None);
        assert_eq!(
            Parsed::parse(&strings(&["-dump", "dot"])).get("-dump"),
            Some(strings(&["dot"]).as_slice())
        );
    }
}
