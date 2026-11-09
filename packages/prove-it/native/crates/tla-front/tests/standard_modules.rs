//! The standard modules compiled into the crate, which `scripts/front-modules.ts --check` holds to
//! the TypeScript front end's texts.

use tla_front::parser::parse_sany_module;
use tla_front::standard_modules::{BUNDLED, MASTER, TLC_174};
use tla_front::{TlcVersion, get_standard_module};

#[test]
fn parses_every_standard_module() {
    for (name, text) in MASTER.iter().chain(TLC_174).chain(BUNDLED) {
        let module = parse_sany_module(text, None, TlcVersion::Master).expect("a module");
        assert_eq!(&*module.name, *name);
    }
}

#[test]
fn finds_each_version_s_modules() {
    assert!(get_standard_module("TLCExt", TlcVersion::Master).is_some());
    assert!(get_standard_module("TLCExt", TlcVersion::V1_7_4).is_none());
    assert_ne!(
        get_standard_module("Bags", TlcVersion::Master),
        get_standard_module("Bags", TlcVersion::V1_7_4)
    );
}
