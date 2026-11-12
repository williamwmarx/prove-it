//! The tla2tools.jar a Java launch names on its class path: which TLC it is, as `getTlcVersion` in
//! `src/tlc/version.ts` reads it, and the URL of its standard modules, which TLC names the files it
//! copies from it by (`getStandardModulesUrl` in `src/cli/shared.ts`).

use std::path::Path;

use crate::host::Host;
use crate::host_path::Platform;
use crate::zip::read_entry;

const MANIFEST: &str = "META-INF/MANIFEST.MF";

/// The jar on the class path: its first entry that ends with `.jar` (`getToolsJar`).
pub fn get_tools_jar(class_path: &str, platform: Platform) -> Option<&str> {
    class_path
        .split(platform.delimiter())
        .find(|entry| entry.ends_with(".jar"))
}

/// Whether the jar is TLC 1.7.4, by the Git tag its manifest records; any other tag, or no jar at
/// the path, is the master build. Otherwise why its manifest can't be read with certainty.
pub fn is_174(host: &dyn Host, jar: &str) -> Result<bool, String> {
    let Some(archive) = host.read_bytes(Path::new(jar)) else {
        return Ok(false);
    };
    let manifest = read_entry(&archive, MANIFEST)?.ok_or("a jar without META-INF/MANIFEST.MF")?;
    let manifest = String::from_utf8(manifest).map_err(|_| "a manifest that isn't UTF-8")?;
    // The first line `X-Git-Tag: *(\S*)` matches, as JavaScript's multiline mode finds lines.
    let tag = manifest
        .split(['\n', '\r', '\u{2028}', '\u{2029}'])
        .find_map(|line| line.strip_prefix("X-Git-Tag:"))
        .map(|tag| {
            tag.trim_start_matches(' ')
                .split(char::is_whitespace)
                .next()
                .unwrap_or_default()
        });
    Ok(tag == Some("v1.7.4"))
}

/// `jar:file:<absolute path>!/tla2sany/StandardModules/`, with the path written and encoded as
/// Node's `pathToFileURL` writes the pathname.
pub fn get_standard_modules_url(jar: &Path) -> String {
    format!(
        "jar:file:{}!/tla2sany/StandardModules/",
        get_url_path(&jar.display().to_string(), cfg!(windows))
    )
}

// A path as a file URL's pathname: on Windows with forward slashes, a drive's path from the root
// (`C:\work` as `/C:/work`), then percent-encoded.
fn get_url_path(path: &str, is_windows: bool) -> String {
    let path = if is_windows {
        let slashed = path.replace('\\', "/");
        if slashed.starts_with('/') {
            slashed
        } else {
            format!("/{slashed}")
        }
    } else {
        path.to_owned()
    };
    path.bytes()
        .map(|byte| match byte {
            b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' => char::from(byte).to_string(),
            b'/' | b'!' | b'$' | b'&' | b'\'' | b'(' | b')' | b'*' | b'+' | b',' | b'-' | b'.'
            | b':' | b';' | b'=' | b'@' | b'_' => char::from(byte).to_string(),
            _ => format!("%{byte:02X}"),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::host::SystemHost;

    #[test]
    fn reads_which_tlc_a_jar_is() {
        let host = SystemHost::new(None);
        let fixture = |name: &str| format!("{}/fixtures/{name}", env!("CARGO_MANIFEST_DIR"));
        assert_eq!(is_174(&host, &fixture("tla2tools.jar")), Ok(false));
        assert_eq!(is_174(&host, &fixture("tla2tools-1.7.4.jar")), Ok(true));
        // getTlcVersion takes a path without a jar for the master build.
        assert_eq!(is_174(&host, &fixture("missing.jar")), Ok(false));
        assert_eq!(
            is_174(&host, &format!("{}/Cargo.toml", env!("CARGO_MANIFEST_DIR"))),
            Err("no end of central directory record".into())
        );
    }

    #[test]
    fn names_the_jar_and_its_standard_modules_as_the_typescript_cli_does() {
        assert_eq!(
            get_tools_jar("classes:lib/tla2tools.jar:other.jar", Platform::Unix),
            Some("lib/tla2tools.jar")
        );
        assert_eq!(
            get_tools_jar("C:\\classes;C:\\lib\\tla2tools.jar", Platform::Windows),
            Some("C:\\lib\\tla2tools.jar")
        );
        assert_eq!(get_tools_jar("classes", Platform::Unix), None);
        assert_eq!(
            get_standard_modules_url(Path::new("/lib/tla2tools.jar")),
            "jar:file:/lib/tla2tools.jar!/tla2sany/StandardModules/"
        );
        // What Node's pathToFileURL encodes of a Unix path, and what it leaves.
        assert_eq!(
            get_url_path("/a b/%#?[]^|~\"<>`{}\\\u{e9}/x!$&'()*+,-.:;=@_.jar", false),
            "/a%20b/%25%23%3F%5B%5D%5E%7C%7E%22%3C%3E%60%7B%7D%5C%C3%A9/x!$&'()*+,-.:;=@_.jar"
        );
        // What it writes of a Windows path.
        assert_eq!(
            get_url_path(r"C:\work dir\tla2tools.jar", true),
            "/C:/work%20dir/tla2tools.jar"
        );
    }
}
