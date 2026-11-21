//! Static facts about the explicitly modeled parent of TLC's URLClassLoader.
//!
//! `TLAClass.loadClass` uses a parent-first URLClassLoader. Resolver bytes alone cannot prove
//! that this loader selects a provider: a parent class can shadow those bytes. The tables here
//! describe the pinned TLC jar and every package of the pinned JDK's system modules. They do
//! not inspect the machine running prove-it and do not run a JVM.

use crate::TlcVersion;
use crate::model::ClassOrigin;

#[path = "java_parent/data.rs"]
mod data;

/// A caller-supplied execution contract, separate from a default-looking command line.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ParentProfile {
    /// Generic/source callers, opaque launches, and contexts without the complete witness.
    #[default]
    Unknown,
    /// TLC master d8fb231 with Linux x86_64 Temurin 21.0.13+9, before user class initialization or any user
    /// mutation of the parent loader. There are no extra parent classpath entries, agents,
    /// patched modules, or manifest companions (CommunityModules-deps.jar/CommunityModules.jar).
    ///
    /// The index owner establishes this contract after the active constant/legacy error
    /// boundary and before user initialization. A quiet verified index, all providers without
    /// class initializers, and no preceding named override execution are one sufficient witness.
    /// Alternatively, it can capture all exact-name parent facts before any user initialization
    /// and carry those immutable facts only across a verified prefix that cannot mutate the
    /// parent namespace. This does not permit new queries after unverified initialization,
    /// moving class-file reads, or changing initializer effects/order. JavaProfile::Default
    /// alone is not this witness.
    ModeledTlcMasterJdk21,
}

/// What the closed parent namespace proves about a Java binary name.
///
/// A TLC class entry blocks absence regardless of whether loading/initialization would work.
/// A JDK package blocks absence even when the particular class is absent; we do not embed an
/// exact JDK class list. Only absence from both sources proves absence. Dynamic proxy packages
/// remain unknown because the JDK can create them outside the static module package tables.
/// A non-master version or unsupported name never acquires an absence certificate.
pub fn class_origin(profile: ParentProfile, version: TlcVersion, binary_name: &str) -> ClassOrigin {
    if profile != ParentProfile::ModeledTlcMasterJdk21 || version != TlcVersion::Master {
        return ClassOrigin::Unknown;
    }
    if data::TLC_CLASSES.binary_search(&binary_name).is_ok() {
        return ClassOrigin::Present;
    }
    if binary_name.ends_with(".class") || !binary_name.split('.').all(is_identifier) {
        return ClassOrigin::Unknown;
    }
    let package = binary_name
        .rsplit_once('.')
        .map_or("", |(package, _)| package);
    if dynamic_proxy_package(package) || data::JDK_PACKAGES.binary_search(&package).is_ok() {
        ClassOrigin::Unknown
    } else {
        ClassOrigin::Absent
    }
}

fn is_identifier(text: &str) -> bool {
    let mut bytes = text.bytes();
    let Some(first) = bytes.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || matches!(first, b'_' | b'$'))
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'$'))
}

fn dynamic_proxy_package(package: &str) -> bool {
    // Pinned Proxy.getDynamicModule creates these two packages (Proxy.java:907-912).
    // ReflectUtil.PROXY_PACKAGE is exactly "com.sun.proxy". This is a source-backed
    // exception to the static package table, not a guess about package prefixes.
    let suffix = package
        .strip_prefix("jdk.proxy")
        .or_else(|| package.strip_prefix("com.sun.proxy.jdk.proxy"));
    suffix.is_some_and(|digits| !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()))
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    fn modeled(name: &str) -> ClassOrigin {
        class_origin(
            ParentProfile::ModeledTlcMasterJdk21,
            TlcVersion::Master,
            name,
        )
    }

    #[test]
    fn does_not_turn_an_unwitnessed_or_legacy_context_into_absence() {
        for name in [
            "Provider",
            "example.Provider",
            "tlc2.value.impl.TupleValue",
            "java.lang.String",
        ] {
            assert_eq!(
                class_origin(ParentProfile::Unknown, TlcVersion::Master, name),
                ClassOrigin::Unknown
            );
            assert_eq!(
                class_origin(
                    ParentProfile::ModeledTlcMasterJdk21,
                    TlcVersion::V1_7_4,
                    name
                ),
                ClassOrigin::Unknown
            );
        }
        assert_eq!(ParentProfile::default(), ParentProfile::Unknown);
    }

    #[test]
    fn distinguishes_exact_jar_presence_package_presence_and_bounded_absence() {
        assert_eq!(modeled("tlc2.value.impl.TupleValue"), ClassOrigin::Present);
        assert_eq!(modeled("tlc2.tool.impl.TLAClass"), ClassOrigin::Present);
        assert_eq!(modeled("java.lang.String"), ClassOrigin::Unknown);
        assert_eq!(modeled("java.lang.NoSuchClass"), ClassOrigin::Unknown);
        assert_eq!(
            modeled("com.sun.crypto.provider.NoSuchClass"),
            ClassOrigin::Unknown
        );
        assert_eq!(modeled("Provider"), ClassOrigin::Absent);
        assert_eq!(modeled("example.Provider"), ClassOrigin::Absent);
        assert_eq!(modeled("tlc2.value.impl.NoSuchClass"), ClassOrigin::Absent);
        assert_eq!(
            modeled("java.not_a_module_package.Provider"),
            ClassOrigin::Absent
        );
    }

    #[test]
    fn keeps_generated_proxy_names_and_unsupported_names_unknown() {
        for name in [
            "jdk.proxy1.$Proxy0",
            "jdk.proxy123.$Proxy456",
            "com.sun.proxy.jdk.proxy2.$Proxy0",
            "jdk.proxy0.Provider",
            "",
            ".Provider",
            "example..Provider",
            "example/Provider",
            "[Ljava.lang.String;",
            "Provider.class",
            "module-info",
            "\u{3bb}.Provider",
        ] {
            assert_eq!(modeled(name), ClassOrigin::Unknown, "{name}");
        }
        // A name merely beginning similarly is an ordinary absent package, not a prefix guess.
        assert_eq!(modeled("jdk.proxyfiction.Provider"), ClassOrigin::Absent);
        assert_eq!(modeled("jdk.proxy1.extra.Provider"), ClassOrigin::Absent);
    }

    #[test]
    fn tables_are_sorted_unique_and_match_the_recorded_manifests() {
        assert_eq!(data::TLC_CLASSES.len(), 2012);
        assert_eq!(data::JDK_PACKAGES.len(), 887);
        assert!(data::TLC_CLASSES.windows(2).all(|pair| pair[0] < pair[1]));
        assert!(data::JDK_PACKAGES.windows(2).all(|pair| pair[0] < pair[1]));
        let entries = include_str!("java_parent/tlc-class-entries.txt");
        let expected: Vec<_> = entries
            .lines()
            .filter(|entry| !entry.ends_with("module-info.class"))
            .map(|entry| entry.strip_suffix(".class").unwrap().replace('/', "."))
            .collect();
        assert_eq!(expected.len(), data::TLC_CLASSES.len());
        for name in expected {
            assert_eq!(modeled(&name), ClassOrigin::Present, "{name}");
        }
        assert_eq!(
            include_str!("java_parent/jdk-module-packages.txt")
                .lines()
                .collect::<Vec<_>>(),
            data::JDK_PACKAGES
        );
        let bytes = data::TLC_CLASSES
            .iter()
            .chain(data::JDK_PACKAGES)
            .map(|name| name.len())
            .sum::<usize>()
            + (data::TLC_CLASSES.len() + data::JDK_PACKAGES.len()) * std::mem::size_of::<&str>();
        assert!(bytes < 160 * 1024, "{bytes} bytes of static tables");
    }

    /// FIPS 180-4's SHA-256 of these bytes, in lowercase hexadecimal, as `scripts/java-parent.ts`
    /// records the files it writes in `provenance.json`.
    pub(crate) fn sha256(bytes: &[u8]) -> String {
        const K: [u32; 64] = [
            0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
            0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
            0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
            0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
            0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
            0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
            0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
            0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
            0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
            0xc67178f2,
        ];
        let mut state: [u32; 8] = [
            0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
            0x5be0cd19,
        ];
        let mut message = bytes.to_vec();
        message.push(0x80);
        while message.len() % 64 != 56 {
            message.push(0);
        }
        message.extend_from_slice(&((bytes.len() as u64) * 8).to_be_bytes());
        for block in message.as_chunks::<64>().0 {
            let mut words = [0u32; 64];
            for (word, chunk) in words.iter_mut().zip(block.as_chunks::<4>().0) {
                *word = u32::from_be_bytes(*chunk);
            }
            for index in 16..64 {
                let low = words[index - 15];
                let high = words[index - 2];
                let s0 = low.rotate_right(7) ^ low.rotate_right(18) ^ (low >> 3);
                let s1 = high.rotate_right(17) ^ high.rotate_right(19) ^ (high >> 10);
                words[index] = words[index - 16]
                    .wrapping_add(s0)
                    .wrapping_add(words[index - 7])
                    .wrapping_add(s1);
            }
            let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = state;
            for (constant, word) in K.iter().zip(words) {
                let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
                let choice = (e & f) ^ (!e & g);
                let first = h
                    .wrapping_add(s1)
                    .wrapping_add(choice)
                    .wrapping_add(*constant)
                    .wrapping_add(word);
                let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
                let majority = (a & b) ^ (a & c) ^ (b & c);
                let second = s0.wrapping_add(majority);
                h = g;
                g = f;
                f = e;
                e = d.wrapping_add(first);
                d = c;
                c = b;
                b = a;
                a = first.wrapping_add(second);
            }
            for (value, added) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
                *value = value.wrapping_add(added);
            }
        }
        state.iter().map(|word| format!("{word:08x}")).collect()
    }

    /// The string `provenance.json` gives a key, which it names once.
    fn get_recorded(key: &str) -> &'static str {
        let provenance = include_str!("java_parent/provenance.json");
        let pattern = format!("\"{key}\": \"");
        assert_eq!(provenance.matches(&pattern).count(), 1, "{key}");
        let start = provenance.find(&pattern).unwrap() + pattern.len();
        let length = provenance[start..].find('"').unwrap();
        &provenance[start..start + length]
    }

    #[test]
    fn provenance_records_the_hashes_of_the_committed_tables() {
        assert_eq!(
            sha256(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        for (key, bytes) in [
            (
                "generated_data_sha256",
                &include_bytes!("java_parent/data.rs")[..],
            ),
            (
                "class_entries_sha256",
                include_bytes!("java_parent/tlc-class-entries.txt"),
            ),
            (
                "packages_sha256",
                include_bytes!("java_parent/jdk-module-packages.txt"),
            ),
        ] {
            assert_eq!(sha256(bytes), get_recorded(key), "{key}");
        }
    }
}
