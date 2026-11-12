//! The standard modules of SANY for each TLC version, and the modules TLC bundles.

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

pub const TLC_SOURCES: &[(&str, &str)] = &[
    module!("tlc", "Naturals"),
    module!("tlc", "Integers"),
    module!("tlc", "Sequences"),
    module!("tlc", "FiniteSets"),
    module!("tlc", "TLC"),
    module!("tlc", "TLCExt"),
    module!("tlc", "Bags"),
    module!("tlc", "Json"),
    module!("tlc", "Randomization"),
    module!("tlc", "Reals"),
    module!("tlc", "RealTime"),
    module!("tlc", "Toolbox"),
    module!("tlc", "_Possible"),
];
