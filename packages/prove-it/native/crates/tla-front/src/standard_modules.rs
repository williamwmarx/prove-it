//! The standard modules of SANY for each TLC version, and the modules TLC bundles, as
//! `src/sany/modules.ts` and `src/bundled-modules.ts` hold them. `scripts/front-modules.ts`
//! writes this file and the texts it includes; don't edit them by hand.

macro_rules! module {
    ($directory:literal, $name:literal) => {
        (
            $name,
            include_str!(concat!("../modules/", $directory, "/", $name, ".tla")),
        )
    };
}

pub const MASTER: &[(&str, &str)] = &[
    module!("master", "Bags"),
    module!("master", "FiniteSets"),
    module!("master", "Integers"),
    module!("master", "Json"),
    module!("master", "Naturals"),
    module!("master", "Randomization"),
    module!("master", "RealTime"),
    module!("master", "Reals"),
    module!("master", "Sequences"),
    module!("master", "TLC"),
    module!("master", "TLCExt"),
    module!("master", "Toolbox"),
    module!("master", "_DotTrace"),
    module!("master", "_JsonTrace"),
    module!("master", "_Possible"),
    module!("master", "_TLAPlusCounterExample"),
    module!("master", "_TLCActionTrace"),
    module!("master", "_TLCTESpec"),
    module!("master", "_TLCTrace"),
    module!("master", "_TLCTracePlain"),
];

pub const TLC_174: &[(&str, &str)] = &[
    module!("1.7.4", "FiniteSets"),
    module!("1.7.4", "Integers"),
    module!("1.7.4", "Naturals"),
    module!("1.7.4", "RealTime"),
    module!("1.7.4", "Reals"),
    module!("1.7.4", "Sequences"),
    module!("1.7.4", "TLC"),
    module!("1.7.4", "Bags"),
    module!("1.7.4", "Randomization"),
    module!("1.7.4", "Toolbox"),
];

pub const BUNDLED: &[(&str, &str)] = &[
    module!("bundled", "Reals"),
    module!("bundled", "RealTime"),
    module!("bundled", "Toolbox"),
];
