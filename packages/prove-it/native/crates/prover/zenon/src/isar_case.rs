// Ported from Zenon's isar_case.ml and enum.ml, as shipped in tlapm. Copyright 2009 INRIA, see
// LICENSE.
//! The lemmas for CASE expressions and record sets with more arms or fields than Zenon.thy covers.
//! Each one is a template that Zenon's Enum expands for the arity: the text between @@@ and ...
//! repeats counting up, the text between ... and @@@ repeats counting down.
//!
//! The templates are ASCII, so the byte offsets here are the TypeScript's UTF-16 offsets.

use crate::ZenonError;

/// A run of digits or of other characters.
#[derive(Clone, Copy)]
struct Lexeme<'a> {
    is_number: bool,
    text: &'a str,
}

/// A piece of a pattern: text, or a number that grows by its step at each repetition.
#[derive(Clone, Copy)]
enum Piece<'a> {
    Text(&'a str),
    Number { base: i64, step: i64 },
}

struct Pattern<'a> {
    pieces: Vec<Piece<'a>>,
    separator: &'a str,
}

fn lex(text: &str) -> Vec<Lexeme<'_>> {
    let mut lexemes = Vec::new();
    let mut start = 0;
    let bytes = text.as_bytes();
    while start < bytes.len() {
        let is_number = bytes[start].is_ascii_digit();
        let end = bytes[start..]
            .iter()
            .position(|byte| byte.is_ascii_digit() != is_number)
            .map_or(bytes.len(), |length| start + length);
        lexemes.push(Lexeme {
            is_number,
            text: &text[start..end],
        });
        start = end;
    }
    lexemes
}

/// JavaScript's `Number` of a run of digits.
fn to_number(digits: &str) -> i64 {
    digits.bytes().fold(0, |value: i64, digit| {
        value.wrapping_mul(10).wrapping_add(i64::from(digit - b'0'))
    })
}

/// The repeated text and the separator of a pattern without numbers: its two equal halves.
fn split_text(text: &str) -> Pattern<'_> {
    let half = text.len() / 2;
    let odd = text.len() % 2;
    for offset in 0..half {
        let first = &text[..half - offset];
        if Some(first) == text.get(half + offset + odd..half + offset + odd + half - offset) {
            return Pattern {
                pieces: vec![Piece::Text(first)],
                separator: &text[half - offset..half + offset + odd],
            };
        }
    }
    Pattern {
        pieces: Vec::new(),
        separator: text,
    }
}

fn correlate<'a>(
    first: &[Lexeme<'a>],
    second: &[Lexeme<'a>],
) -> Result<Option<Vec<Piece<'a>>>, ZenonError> {
    if first.len() != second.len() {
        return Err(ZenonError::new("Zenon: an uneven template"));
    }
    Ok(first
        .iter()
        .zip(second)
        .map(|(lexeme, other)| {
            if !lexeme.is_number && !other.is_number && lexeme.text == other.text {
                return Some(Piece::Text(lexeme.text));
            }
            if lexeme.is_number && other.is_number {
                return Some(Piece::Number {
                    base: to_number(lexeme.text),
                    step: to_number(other.text) - to_number(lexeme.text),
                });
            }
            None
        })
        .collect())
}

type Split<'a> = (Vec<Lexeme<'a>>, &'a str, Vec<Lexeme<'a>>);

/// Zenon's split_sep: the separator inside the middle text, after the end of the first instance's
/// last lexeme and before the start of the second instance's first.
fn split_separator<'a>(
    before: Lexeme<'a>,
    middle: &'a str,
    after: Lexeme<'a>,
) -> Option<Split<'a>> {
    if !before.is_number && !middle.starts_with(before.text) {
        return None;
    }
    if !after.is_number && !middle.ends_with(after.text) {
        return None;
    }
    let start = if before.is_number {
        0
    } else {
        before.text.len()
    };
    let end = if after.is_number { 0 } else { after.text.len() };
    if start + end > middle.len() {
        return None;
    }
    Some((
        if before.is_number {
            Vec::new()
        } else {
            vec![before]
        },
        &middle[start..middle.len() - end],
        if after.is_number {
            Vec::new()
        } else {
            vec![after]
        },
    ))
}

/// Zenon's split_sep2, for two instances that meet between two numbers.
fn split_separator_between<'a>(
    before: Lexeme<'a>,
    first: Lexeme<'a>,
    second: Lexeme<'a>,
    after: Lexeme<'a>,
) -> Result<Split<'a>, ZenonError> {
    if !before.is_number
        && !first.is_number
        && second.is_number
        && after.is_number
        && first.text.starts_with(before.text)
    {
        return Ok((vec![before], &first.text[before.text.len()..], vec![second]));
    }
    if before.is_number
        && first.is_number
        && !second.is_number
        && !after.is_number
        && second.text.ends_with(after.text)
    {
        return Ok((
            vec![first],
            &second.text[..second.text.len() - after.text.len()],
            vec![after],
        ));
    }
    Err(ZenonError::new(
        "Zenon: a template whose instances don't meet",
    ))
}

/// Zenon's Enum.parse: a template's text holds two instances of the pattern and the separator.
fn parse_pattern(text: &str) -> Result<Option<Pattern<'_>>, ZenonError> {
    let lexemes = lex(text);
    let length = lexemes.len();
    if length == 0 {
        return Ok(Some(Pattern {
            pieces: Vec::new(),
            separator: "",
        }));
    }
    if length == 1 {
        let only = lexemes[0];
        if !only.is_number {
            return Ok(Some(split_text(only.text)));
        }
        if only.text.len() % 2 == 1 {
            return Ok(None);
        }
        let half = only.text.len() / 2;
        let base = to_number(&only.text[..half]);
        return Ok(Some(Pattern {
            pieces: vec![Piece::Number {
                base,
                step: to_number(&only.text[half..]) - base,
            }],
            separator: "",
        }));
    }
    let half = length / 2;
    let split = if length.is_multiple_of(4) {
        let prefix = &lexemes[..half - 1];
        let suffix = &lexemes[half + 1..];
        let split = split_separator_between(
            suffix[suffix.len() - 1],
            lexemes[half - 1],
            lexemes[half],
            prefix[0],
        )?;
        (prefix, suffix, split)
    } else {
        if length.is_multiple_of(2) {
            return Ok(None);
        }
        let middle = lexemes[half];
        if middle.is_number {
            return Ok(None);
        }
        let prefix = &lexemes[..half];
        let suffix = &lexemes[half + 1..];
        let Some(split) = split_separator(suffix[suffix.len() - 1], middle.text, prefix[0]) else {
            return Ok(None);
        };
        (prefix, suffix, split)
    };
    let (prefix, suffix, split) = split;
    let pieces = correlate(&[prefix, &split.0].concat(), &[&split.2, suffix].concat())?;
    Ok(pieces.map(|pieces| Pattern {
        pieces,
        separator: split.1,
    }))
}

fn get_instance(pieces: &[Piece], value: impl Fn(i64, i64) -> i64) -> String {
    pieces
        .iter()
        .map(|piece| match piece {
            Piece::Text(text) => (*text).to_string(),
            Piece::Number { base, step } => value(*base, *step).to_string(),
        })
        .collect()
}

/// Zenon's expand_string and expand_string_rev: the pattern repeated count times.
fn expand_pattern(count: i64, text: &str, is_reversed: bool) -> Result<Option<String>, ZenonError> {
    let Some(pattern) = parse_pattern(text)? else {
        return Ok(None);
    };
    let positions = (0..count.max(0)).map(|position| {
        if is_reversed {
            count - 1 - position
        } else {
            position
        }
    });
    Ok(Some(
        positions
            .map(|position| {
                get_instance(&pattern.pieces, |base, step| {
                    if is_reversed {
                        base + step - position * step
                    } else {
                        base + position * step
                    }
                })
            })
            .collect::<Vec<_>>()
            .join(pattern.separator),
    ))
}

/// Zenon's read_suffix: a count adjustment such as [n-1] after the end marker.
fn read_adjustment(text: &str, position: usize) -> (i64, usize) {
    let Some(rest) = text
        .get(position..)
        .and_then(|rest| rest.strip_prefix("[n"))
    else {
        return (0, position);
    };
    if rest.starts_with(']') {
        return (0, position + 3);
    }
    let sign = match rest.as_bytes().first() {
        Some(b'-') => -1,
        Some(b'+') => 1,
        _ => return (0, position),
    };
    let digits = rest[1..].bytes().take_while(u8::is_ascii_digit).count();
    if rest.as_bytes().get(1 + digits) != Some(&b']') {
        return (0, position);
    }
    (
        sign * to_number(&rest[1..1 + digits]),
        position + 2 + 1 + digits + 1,
    )
}

fn trim_newlines(text: &str) -> Result<&str, ZenonError> {
    if text.len() >= 2 && text.starts_with('\n') && text.ends_with('\n') {
        return Ok(&text[1..text.len() - 1]);
    }
    if text.len() >= 4 && text.starts_with("\r\n") && text.ends_with("\r\n") {
        return Ok(&text[2..text.len() - 2]);
    }
    Err(ZenonError::new("Zenon: a bad template"))
}

fn find(template: &str, needle: &str, from: usize) -> Option<usize> {
    template
        .get(from..)
        .and_then(|rest| rest.find(needle))
        .map(|offset| from + offset)
}

/// Zenon's Enum.expand_text.
fn expand_template(count: i64, template: &str) -> Result<String, ZenonError> {
    let mut parts = String::new();
    let mut position = 0;
    loop {
        let up = find(template, "@@@", position);
        let down = find(template, "...", position);
        let (start, is_reversed) = match (up, down) {
            (None, None) => break,
            (None, Some(down)) => (down, true),
            (Some(up), Some(down)) if down < up => (down, true),
            (Some(up), _) => (up, false),
        };
        let Some(end) = find(template, if is_reversed { "@@@" } else { "..." }, start + 3) else {
            return Err(ZenonError::new("Zenon: a bad template"));
        };
        parts.push_str(&template[position..start]);
        let text = &template[start + 3..end];
        let adjustment = read_adjustment(template, end + 3);
        let expanded = match expand_pattern(count + adjustment.0, text, is_reversed)? {
            Some(expanded) => Some(expanded),
            None => expand_pattern(count + adjustment.0, trim_newlines(text)?, is_reversed)?,
        };
        let Some(expanded) = expanded else {
            return Err(ZenonError::new("Zenon: a bad template"));
        };
        parts.push_str(&expanded);
        position = adjustment.1;
    }
    parts.push_str(&template[position..]);
    Ok(parts)
}

pub fn print_case_lemma(arity: i64, is_other: bool) -> Result<String, ZenonError> {
    Ok(format!(
        "have zenon_case{}{arity} :{}",
        if is_other { "other" } else { "" },
        expand_template(
            arity,
            if is_other {
                CASE_OTHER_TEMPLATE
            } else {
                CASE_TEMPLATE
            }
        )?
    ))
}

pub fn print_record_lemma(arity: i64) -> Result<String, ZenonError> {
    Ok(format!(
        "have zenon_inrecordsetI{arity} :{}",
        expand_template(arity, &get_record_template(arity))?
    ))
}

fn get_record_template(arity: i64) -> String {
    format!("{RECORD_TEMPLATE_HEAD}{arity}{RECORD_TEMPLATE_TAIL}")
}

const CASE_TEMPLATE: &str = r#"
  "!! P @@@c1x e1x c2x e2x... .
    P (CASE @@@c1x -> e1x [] c2x -> e2x...) ==>
@@@
    (c1x ==> P (e1x) ==> FALSE) ==>
    (c2x ==> P (e2x) ==> FALSE) ==>
...
    (...~c2x & ~c1x@@@ & TRUE ==> FALSE) ==>
    FALSE"
proof -
  fix P @@@c1x e1x c2x e2x...
  assume h: "P (CASE @@@c1x -> e1x [] c2x -> e2x...)"
            (is "P (?cas)")
@@@
  assume h1: "c1x ==> P (e1x) ==> FALSE"
  assume h2: "c2x ==> P (e2x) ==> FALSE"
...
  assume hoth: "...~c2x & ~c1x@@@ & TRUE ==> FALSE"
  def cs == "<<@@@c1x, c2x...>>" (is "?cs")
  def es == "<<@@@e1x, e2x...>>" (is "?es")
  def arms == "UNION {CaseArm (?cs[i], ?es[i]) : i \\in DOMAIN ?cs}"
              (is "?arms")
  def cas == "?cas"
  have h0: "P (cas)" using h by (fold cas_def)
  def dcs == "...c2x | c1x@@@" (is "?dcs")
  show FALSE
  proof (rule zenon_em [of "?dcs"])
    assume ha: "~(?dcs)"
@@@
    have hh1: "~c1x" using ha by blast
    have hh2: "~c2x" using ha by blast
...
    show FALSE
      using hoth @@@hh1 hh2... by blast
  next
    assume ha: "?dcs"
    def scs == "zenon_seqify (@@@zenon_appseq (zenon_appseq (...
                               <<>>, @@@c1x), c2x)...)"
               (is "?scs")
    def ses == "zenon_seqify (@@@zenon_appseq (zenon_appseq (...
                               <<>>, @@@e1x), e2x)...)"
               (is "?ses")
    have ha1: "\<exists> i \<in> DOMAIN ?scs : ?scs[i]"
      using ha zenon_case_seq_empty
      by (simp only: zenon_case_seq_simpl zenon_seqify_empty, blast)
    have ha2: "\<exists> i \<in> DOMAIN ?cs : ?cs[i]"
      using ha1 by (simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hb: "\\E x : x \\in arms"
      using zenon_case_domain [OF ha2, where es = "?es"]
      by (unfold arms_def, blast)
    have hc: "(CHOOSE x : x \\in arms) \\in arms"
      using hb by (unfold Ex_def, auto)
    have hf0: "?cas \\in arms"
      using hc by (unfold arms_def, fold Case_def)
    have hf3: "cas \\in UNION {CaseArm (?scs[i], ?ses[i])
                                  : i \\in DOMAIN ?scs}"
              (is "?hf3")
      using hf0 by (fold cas_def, unfold arms_def,
                    simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hf4: "Len (?scs) = Len (?ses)" (is "?hf4")
      by (simp only: zenon_case_len_simpl)
    have hf5: "?hf4 & ?hf3"
      by (rule conjI [OF hf4 hf3])
    have hf: "
               ...cas \\in CaseArm (c2x, e2x)
             | cas \\in CaseArm (c1x, e1x)@@@
             | cas \\in UNION {CaseArm (zenon_seqify (<<>>)[i],
                                          zenon_seqify (<<>>)[i])
                                 : i \\in DOMAIN zenon_seqify (<<>>)}
             " (is "_ | ?gxx")
      using hf5 by (simp only: zenon_case_union_simpl, blast)
@@@
    have hg1x: "cas \\in CaseArm (c1x, e1x) => FALSE"
      using h0 h1 by auto
    have hg2x: "cas \\in CaseArm (c2x, e2x) => FALSE"
      using h0 h2 by auto
...
    from hf
    have hh0: "?gxx" ...(is "_ | ?g1")
      by (rule zenon_disjE1 [OF _ hg3x])
    then have hh1: "?g1" (is "_ | ?g0")
      by (rule zenon_disjE1 [OF _ hg2x])
    then have hh0: "?g0"@@@[n-1]
      by (rule zenon_disjE1 [OF _ hg1x])
    have hi: "cas \\in UNION {CaseArm (<<>>[i], <<>>[i])
                                 : i \\in DOMAIN <<>>}"
      using hh0 by (simp only: zenon_seqify_empty)
    show FALSE
      by (rule zenon_case_empty_union [OF hi])
  qed
qed
"#;

const CASE_OTHER_TEMPLATE: &str = r#"
  "!! P oth @@@c1x e1x c2x e2x... .
    P (CASE @@@c1x -> e1x [] c2x -> e2x... [] OTHER -> oth) ==>
@@@
    (c1x ==> P (e1x) ==> FALSE) ==>
    (c2x ==> P (e2x) ==> FALSE) ==>
...
    (...~c2x & ~c1x@@@ & TRUE ==> P (oth) ==> FALSE) ==>
    FALSE"
proof -
  fix P oth @@@c1x e1x c2x e2x...
  assume h: "P (CASE @@@c1x -> e1x [] c2x -> e2x... [] OTHER -> oth)"
            (is "P (?cas)")
@@@
  assume h1: "c1x ==> P (e1x) ==> FALSE"
  assume h2: "c2x ==> P (e2x) ==> FALSE"
...
  assume hoth: "...~c2x & ~c1x@@@ & TRUE ==> P (oth) ==> FALSE"
  def cs == "<<@@@c1x, c2x...>>" (is "?cs")
  def es == "<<@@@e1x, e2x...>>" (is "?es")
  def arms == "UNION {CaseArm (?cs[i], ?es[i]) : i \\in DOMAIN ?cs}"
              (is "?arms")
  def cas == "?cas"
  have h0: "P (cas)" using h by (fold cas_def)
  def dcs == "...c2x | c1x@@@ | FALSE" (is "?dcs")
  def scs == "zenon_seqify (@@@zenon_appseq (zenon_appseq (...
                             <<>>, @@@c1x), c2x)...)"
             (is "?scs")
  have hscs : "?cs = ?scs"
    by (simp only: zenon_seqify_appseq zenon_seqify_empty)
  def ses == "zenon_seqify (@@@zenon_appseq (zenon_appseq (...
                             <<>>, @@@e1x), e2x)...)"
             (is "?ses")
  have hses : "?es = ?ses"
    by (simp only: zenon_seqify_appseq zenon_seqify_empty)
  have hlen: "Len (?scs) = Len (?ses)" (is "?hlen")
    by (simp only: zenon_case_len_simpl)
  def armoth == "CaseArm (\<forall> i \<in> DOMAIN ?cs : ~?cs[i], oth)"
                (is "?armoth")
  show FALSE
  proof (rule zenon_em [of "?dcs"])
    assume ha: "~(?dcs)"
    have hb: "P (CHOOSE x : x \\in arms \<union> armoth)"
      using h by (unfold CaseOther_def, fold arms_def armoth_def)
    have hc: "arms \\cup armoth
              = UNION {CaseArm (?scs[i], ?ses[i]) : i \\in DOMAIN ?scs}
                \\cup CaseArm (\<forall> i \<in> DOMAIN ?scs : ~?scs[i],
                                 oth)"
             (is "_ = ?sarmsoth")
      using hscs hses by (unfold arms_def armoth_def, auto)
    have hd: "~(?dcs) & ?hlen & arms \<union> armoth = ?sarmsoth"
      using ha hlen hc by blast
    have he: "arms \<union> armoth = {oth}"
      using hd by (simp only: zenon_case_oth_simpl zenon_case_oth_empty)
    have hf: "(CHOOSE x : x \\in arms \\cup armoth) = oth"
      using he by auto
    have hg: "P (oth)"
      using hb hf by auto
@@@
    have hh1: "~c1x" using ha by blast
    have hh2: "~c2x" using ha by blast
...
    show FALSE
      using hg hoth @@@hh1 hh2... by blast
  next
    assume ha: "?dcs"
    have ha1: "\<exists> i \<in> DOMAIN ?scs : ?scs[i]"
      using ha zenon_case_seq_empty
      by (simp only: zenon_case_seq_simpl zenon_seqify_empty, blast)
    have ha2: "\<exists> i \<in> DOMAIN ?cs : ?cs[i]"
      using ha1 hscs by auto
    have ha3: "~ (\<forall> i \<in> DOMAIN ?cs : ~?cs[i])"
      using ha2 by blast
    have ha4: "armoth = {}"
      using ha3 condElse [OF ha3, where t = "{oth}" and e = "{}"]
      by (unfold armoth_def CaseArm_def, blast)
    have hb: "\\E x : x \\in arms \\cup armoth"
      using zenon_case_domain [OF ha2, where es = "?es"]
      by (unfold arms_def, blast)
    have hc: "(CHOOSE x : x \\in arms \\cup armoth)
               \\in arms \\cup armoth"
      using hb by (unfold Ex_def, auto)
    have hf0: "?cas \\in arms \\cup armoth"
      using hc by (unfold arms_def armoth_def, fold CaseOther_def)
    have hf1: "cas \\in arms \\cup armoth"
      using hf0 by (fold cas_def)
    have hf2: "cas \\in arms"
      using hf1 ha4 by auto
    have hf3: "cas \\in UNION {CaseArm (?scs[i], ?ses[i])
                                  : i \\in DOMAIN ?scs}"
              (is "?hf3")
      using hf2 by (unfold arms_def,
                    simp only: zenon_seqify_appseq zenon_seqify_empty)
    have hf5: "?hlen & ?hf3"
      by (rule conjI [OF hlen hf3])
    have hf: "
               ...cas \\in CaseArm (c2x, e2x)
             | cas \\in CaseArm (c1x, e1x)@@@
             | cas \\in UNION {CaseArm (zenon_seqify (<<>>)[i],
                                          zenon_seqify (<<>>)[i])
                                 : i \\in DOMAIN zenon_seqify (<<>>)}
             " (is "_ | ?gxx")
      using hf5 by (simp only: zenon_case_union_simpl, blast)
@@@
    have hg1x: "cas \\in CaseArm (c1x, e1x) => FALSE"
      using h0 h1 by auto
    have hg2x: "cas \\in CaseArm (c2x, e2x) => FALSE"
      using h0 h2 by auto
...
    from hf
    have hh0: "?gxx" ...(is "_ | ?g1")
      by (rule zenon_disjE1 [OF _ hg3x])
    then have hh1: "?g1" (is "_ | ?g0")
      by (rule zenon_disjE1 [OF _ hg2x])
    then have hh0: "?g0"@@@[n-1]
      by (rule zenon_disjE1 [OF _ hg1x])
    have hi: "cas \\in UNION {CaseArm (<<>>[i], <<>>[i])
                                 : i \\in DOMAIN <<>>}"
      using hh0 by (simp only: zenon_seqify_empty)
    show FALSE
      by (rule zenon_case_empty_union [OF hi])
  qed
qed
"#;

const RECORD_TEMPLATE_HEAD: &str = r#"
  "!! r @@@l1x s1x l2x s2x... .
    isAFcn (r) ==>
    DOMAIN r = {@@@l1x, l2x...} ==>
@@@
    r[l1x] \\in s1x ==>
    r[l2x] \\in s2x ==>
...
    r \\in [@@@l1x : s1x, l2x : s2x...]"
proof -
  fix r @@@l1x s1x l2x s2x...
  assume hfcn: "isAFcn (r)"
  assume hdom: "DOMAIN r = {@@@l1x, l2x...}"
@@@
  assume h1: "r[l1x] \\in s1x"
  assume h2: "r[l2x] \\in s2x"
...
  let ?doms = "<<@@@l1x, l2x...>>"
  let ?domset = "{@@@l1x, l2x...}"
  let ?domsetrev = "{...l2x, l1x@@@}"
  let ?rngs = "<<@@@s1x, s2x...>>"
  let ?n0n = "0"
@@@
  let ?n1n = "Succ[?n0n]"
  let ?n2n = "Succ[?n1n]"
...
  let ?indices = "{...?n2n, ?n1n@@@}"
  have hdomx : "?domsetrev = DOMAIN r"
  by (rule zenon_set_rev_1, (rule zenon_set_rev_2)+, rule zenon_set_rev_3,
      rule hdom)
  show "r \\in EnumFuncSet (?doms, ?rngs)"
  proof (rule EnumFuncSetI [of r, OF hfcn])
    have hx1: "isASeq (?doms) & ?domsetrev = Range (?doms)"
    by ((rule zenon_range_2)+, rule zenon_range_1)
    have hx2: "?domsetrev = Range (?doms)"
    by (rule conjD2 [OF hx1])
    show "DOMAIN r = Range (?doms)"
    by (rule subst [where P = "%x. x = Range (?doms)", OF hdomx hx2])
  next
    show "DOMAIN ?rngs = DOMAIN ?doms"
    by (rule zenon_tuple_dom_3, (rule zenon_tuple_dom_2)+,
        rule zenon_tuple_dom_1)
  next
    have hdomseq: "isASeq (?doms)" by auto
    have hindx: "isASeq (?doms) & ?n"#;

const RECORD_TEMPLATE_TAIL: &str = r#"n = Len (?doms)
                  & ?indices = DOMAIN ?doms"
    by (simp only: DomainSeqLen [OF hdomseq], (rule zenon_dom_app_2)+,
        rule zenon_dom_app_1)
    have hind: "?indices = DOMAIN ?doms" by (rule conjE [OF hindx], elim conjE)
    show "ALL i in DOMAIN ?doms : r[?doms[i]] \\in ?rngs[i]"
    proof (rule subst [OF hind], (rule zenon_all_rec_2)+, rule zenon_all_rec_1)
@@@
      have hn: "l1x = ?doms[?n1n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s1x = ?rngs[?n1n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n1n]] \\in ?rngs[?n1n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h1)
    next
      have hn: "l2x = ?doms[?n2n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      have hs: "s2x = ?rngs[?n2n]"
      by (((rule zenon_tuple_acc_2, safe, simp only: zenon_ss_1 zenon_ss_2,
            rule zenon_zero_lt,
            simp only: zenon_ss_1 zenon_ss_2 zenon_sa_1 zenon_sa_2,
            ((rule zenon_ss_le_sa_2)+)?, rule zenon_ss_le_sa_1
           )+)?,
          rule zenon_tuple_acc_1, auto)
      show "r[?doms[?n2n]] \\in ?rngs[?n2n]"
      by (rule subst[OF hs], rule subst[OF hn], rule h2)
...
    qed
  qed
qed
"#;

#[cfg(test)]
mod tests {
    use super::{print_case_lemma, print_record_lemma};

    /// `getTextDigest`: the length and FNV-1a hash of a text's UTF-16 code units.
    fn get_text_digest(text: &str) -> String {
        let units: Vec<u16> = text.encode_utf16().collect();
        let hash = units.iter().fold(0x811c_9dc5_u32, |state, unit| {
            (state ^ u32::from(*unit)).wrapping_mul(0x0100_0193)
        });
        format!("{}:{hash:08x}", units.len())
    }

    #[test]
    fn expands_the_templates_as_the_typescript_does() {
        // The digests of printCaseLemma(arity, false), printCaseLemma(arity, true) and
        // printRecordLemma(arity), from the TypeScript.
        let expected = [
            ["2427:9490e2ad", "3938:a41c31b1", "1433:9b118bd2"],
            ["2736:fee0ea0f", "4247:970560ff", "2321:205b8cf4"],
            ["3173:d60f0c7b", "4684:838478ad", "3238:346a3d6a"],
            ["3611:3c367fba", "5122:650e6690", "4155:8bcfdb3b"],
            ["4049:946536d0", "5560:6083885c", "5072:5840ec81"],
            ["4487:9cf2293d", "5998:f9455349", "5989:91512058"],
            ["4925:b2a8b9bf", "6436:bd4fefcd", "6906:4e9a5f72"],
            ["5363:5a0c847a", "6874:d001c2a4", "7823:720318bf"],
            ["5801:93e2744c", "7312:d6b1d9cc", "8740:f0ebe1b9"],
            ["6239:949dd42d", "7750:7b42a72d", "9657:a35ffa8c"],
        ];
        for (arity, digests) in (0..).zip(expected) {
            let printed = [
                print_case_lemma(arity, false).unwrap(),
                print_case_lemma(arity, true).unwrap(),
                print_record_lemma(arity).unwrap(),
            ];
            assert_eq!(
                printed.map(|text| get_text_digest(&text)),
                digests,
                "arity {arity}"
            );
        }
    }

    #[test]
    fn repeats_the_arms_of_a_case() {
        let printed = print_case_lemma(2, false).unwrap();
        assert!(printed.starts_with(
            "have zenon_case2 :\n  \"!! P c1x e1x c2x e2x .\n    P (CASE c1x -> e1x [] c2x -> e2x) ==>\n"
        ));
        assert!(printed.contains("    (~c2x & ~c1x & TRUE ==> FALSE) ==>\n"));
    }
}
