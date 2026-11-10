//! WTF-8, the IR's encoding of its texts, which holds the lone surrogates a string TLC computes may
//! have, as `src/engine/ir.ts` writes them.

use tla_ir::{decode, encode, wtf8};

#[test]
fn reads_back_what_it_writes_lone_surrogates_and_all() {
    let texts: [&[u16]; 4] = [&[0x61], &[0xD83D, 0xDE00], &[0xDE00, 0x61], &[0x62, 0xD83D]];
    for units in texts {
        let mut bytes = Vec::new();
        wtf8::encode(units, &mut bytes);
        assert_eq!(wtf8::decode(&bytes), Ok(units.to_vec()));
    }
    let mut bytes = Vec::new();
    wtf8::encode(&[0xDE00], &mut bytes);
    assert_eq!(bytes, [0xED, 0xB8, 0x80]);
}

#[test]
fn refuses_a_pair_written_as_two_surrogates() {
    let mut bytes = Vec::new();
    wtf8::encode(&[0xD83D], &mut bytes);
    wtf8::encode(&[0xDE00], &mut bytes);
    assert_eq!(wtf8::decode(&bytes), Err(3));
    assert_eq!(wtf8::decode(&[0xC0, 0x80]), Err(0));
}

#[test]
fn keeps_the_units_of_a_text_with_a_lone_surrogate() {
    let golden = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../../tests/conformance/ir/examples/specifications/transaction_commit/TCommit.ir"
    );
    let mut ir = decode(&std::fs::read(golden).expect("the golden file")).expect("an IR");
    // Half an emoji, then the other half: two texts whose units join as one character.
    let first = ir.texts.len() as u32;
    for units in [vec![0x61, 0xD83D], vec![0xDE00]] {
        let id = ir.texts.len() as u32;
        ir.texts.push(String::from_utf16_lossy(&units).into());
        ir.wide_texts.insert(id, units.into());
    }
    let read = decode(&encode(&ir)).expect("the IR reads back");
    assert_eq!(read, ir);
    assert_eq!(read.get_text_units(first), [0x61, 0xD83D]);
    assert_eq!(&*read.texts[first as usize], "a\u{FFFD}");
}
