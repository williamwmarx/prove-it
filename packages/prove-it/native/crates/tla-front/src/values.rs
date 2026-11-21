//! TLC's order of values, as `compareValues` in `src/values.ts` gives it for the values the front
//! end knows: strings and model values by when TLC first interned their texts.

use std::cmp::Ordering;
use std::rc::Rc;

use crate::config::ConfigValue;
use crate::errors::FrontError;
use crate::hash::FastMap;
use crate::resolve::Result;

/// A model value named like `a_b` has the type `a`, which TLC won't compare with another type.
pub fn get_model_value_type(name: &str) -> Option<char> {
    let mut characters = name.chars();
    let first = characters.next()?;
    (name.encode_utf16().count() > 2 && characters.next() == Some('_')).then_some(first)
}

/// TLC's order of values, by the ranks of their texts in TLC's string order.
pub struct ValueOrder<'a> {
    pub ranks: &'a FastMap<Rc<str>, u32>,
}

impl ValueOrder<'_> {
    /// The rank of a string or model value in TLC's string order, which the configuration's
    /// values are all in.
    pub fn get_rank(&self, text: &str) -> Result<u32> {
        self.ranks
            .get(text)
            .copied()
            .ok_or_else(|| FrontError::NotYet("a configuration value TLC doesn't rank".to_owned()))
    }

    /// `compareValues` on the configuration's values. Values of kinds TLC can't compare stop the
    /// front end, whose messages the startup phase will word.
    pub fn compare(&self, left: &ConfigValue, right: &ConfigValue) -> Result<Ordering> {
        Ok(match (left, right) {
            (ConfigValue::Number(left), ConfigValue::Number(right)) => left.total_cmp(right),
            (ConfigValue::String(left), ConfigValue::String(right)) => {
                self.compare_strings(left, right)?
            }
            (ConfigValue::Boolean(left), ConfigValue::Boolean(right)) => {
                if left == right {
                    Ordering::Equal
                } else if left < right {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            }
            (ConfigValue::ModelValue(left), ConfigValue::ModelValue(right)) => {
                if get_model_value_type(left).is_some()
                    && get_model_value_type(right).is_some()
                    && get_model_value_type(left) != get_model_value_type(right)
                {
                    return Err(FrontError::NotYet(
                        "differently-typed model values".to_owned(),
                    ));
                }
                self.get_rank(left)?.cmp(&self.get_rank(right)?)
            }
            (ConfigValue::ModelValue(name), _) | (_, ConfigValue::ModelValue(name))
                if get_model_value_type(name).is_some() =>
            {
                return Err(FrontError::NotYet(
                    "a typed model value compared".to_owned(),
                ));
            }
            (ConfigValue::ModelValue(_), _) => Ordering::Less,
            (_, ConfigValue::ModelValue(_)) => Ordering::Greater,
            (ConfigValue::Set(left), ConfigValue::Set(right)) => {
                if left.len() != right.len() {
                    left.len().cmp(&right.len())
                } else {
                    for (left, right) in left.iter().zip(right) {
                        let comparison = self.compare(left, right)?;
                        if comparison != Ordering::Equal {
                            return Ok(comparison);
                        }
                    }
                    Ordering::Equal
                }
            }
            // `compareFunctions` on two records: their sizes, then their names, then their values.
            (ConfigValue::Record(left), ConfigValue::Record(right)) => {
                if left.len() != right.len() {
                    return Ok(left.len().cmp(&right.len()));
                }
                for ((left, _), (right, _)) in left.iter().zip(right) {
                    let comparison = self.compare_strings(left, right)?;
                    if comparison != Ordering::Equal {
                        return Ok(comparison);
                    }
                }
                for ((_, left), (_, right)) in left.iter().zip(right) {
                    let comparison = self.compare(left, right)?;
                    if comparison != Ordering::Equal {
                        return Ok(comparison);
                    }
                }
                Ordering::Equal
            }
            _ => {
                return Err(FrontError::NotYet(
                    "configuration values TLC can't compare".to_owned(),
                ));
            }
        })
    }

    /// `compareStrings`: by the texts' ranks.
    pub fn compare_strings(&self, left: &str, right: &str) -> Result<Ordering> {
        if left == right {
            return Ok(Ordering::Equal);
        }
        Ok(self.get_rank(left)?.cmp(&self.get_rank(right)?))
    }

    /// `toValue`: a set of the configuration is sorted and its duplicates dropped, as `createSet`
    /// does.
    pub fn normalize(&self, value: &ConfigValue) -> Result<ConfigValue> {
        let ConfigValue::Set(elements) = value else {
            return Ok(value.clone());
        };
        let elements = elements
            .iter()
            .map(|element| self.normalize(element))
            .collect::<Result<Vec<_>>>()?;
        let mut is_sorted = true;
        for pair in elements.windows(2) {
            if self.compare(&pair[0], &pair[1])? != Ordering::Less {
                is_sorted = false;
                break;
            }
        }
        if elements.len() < 2 || is_sorted {
            return Ok(ConfigValue::Set(elements));
        }
        // Sorting compares the elements pairwise; a comparison that fails stops the front end.
        let mut sorted = elements.clone();
        try_sort_by(&mut sorted, &mut |left, right| self.compare(left, right))?;
        let mut unique: Vec<ConfigValue> = Vec::with_capacity(sorted.len());
        for element in sorted {
            if let Some(last) = unique.last()
                && self.compare(last, &element)? == Ordering::Equal
            {
                continue;
            }
            unique.push(element);
        }
        Ok(ConfigValue::Set(unique))
    }
}

/// Sorts `items` stably by `compare`, stopping at the first comparison that fails. The sort of
/// the standard library may panic where a comparison that fails is taken for equality, which
/// leaves the order it sees inconsistent. Up to 20 items it compares them in the order of the
/// standard library's insertion sort (`insertion_sort_shift_left`), and merges sorted halves
/// above that.
pub(crate) fn try_sort_by<T: Clone>(
    items: &mut [T],
    compare: &mut dyn FnMut(&T, &T) -> Result<Ordering>,
) -> Result<()> {
    if items.len() <= 20 {
        for index in 1..items.len() {
            let mut position = index;
            while position > 0 && compare(&items[position], &items[position - 1])? == Ordering::Less
            {
                items.swap(position, position - 1);
                position -= 1;
            }
        }
        return Ok(());
    }
    let middle = items.len() / 2;
    try_sort_by(&mut items[..middle], compare)?;
    try_sort_by(&mut items[middle..], compare)?;
    let mut merged = Vec::with_capacity(items.len());
    let (mut left, mut right) = (0, middle);
    while left < middle && right < items.len() {
        if compare(&items[right], &items[left])? == Ordering::Less {
            merged.push(items[right].clone());
            right += 1;
        } else {
            merged.push(items[left].clone());
            left += 1;
        }
    }
    merged.extend_from_slice(&items[left..middle]);
    merged.extend_from_slice(&items[right..]);
    items.clone_from_slice(&merged);
    Ok(())
}

/// How comparing two of the configuration's values in TLC's classes ends: their order, or the
/// message TLC fails with.
enum Compared {
    Order(Ordering),
    Failed(String),
}

impl ValueOrder<'_> {
    /// `IValue.initialize` of a value the configuration assigns a declared constant, which
    /// `SpecProcessor.processConstantDefns` calls: `deepNormalize` sorts each set, its elements'
    /// sets first, by `ValueVec.sort`, and the message of the first comparison that fails, or
    /// none. NotYet where it can't follow TLC: a record, a value it can't rank, or a message
    /// long enough for `Values.ppr` to break.
    pub fn get_initialize_failure(&self, value: &ConfigValue) -> Result<Option<String>> {
        match self.deep_normalize(value)? {
            Ok(_) => Ok(None),
            Err(message) => Ok(Some(message)),
        }
    }

    fn deep_normalize(
        &self,
        value: &ConfigValue,
    ) -> Result<std::result::Result<ConfigValue, String>> {
        match value {
            ConfigValue::Record(_) => Err(not_followed()),
            ConfigValue::Set(elements) => {
                let mut normalized = Vec::with_capacity(elements.len());
                for element in elements {
                    match self.deep_normalize(element)? {
                        Ok(element) => normalized.push(element),
                        Err(message) => return Ok(Err(message)),
                    }
                }
                // `ValueVec.sort(true)`: each element is searched for by halving among those
                // kept, as the receiver of `compareTo`, and dropped where it equals one.
                let mut kept: Vec<ConfigValue> = Vec::with_capacity(normalized.len());
                for element in normalized {
                    let (mut low, mut high) = (0, kept.len());
                    let mut order = Ordering::Greater;
                    let mut index = 0;
                    while low < high {
                        index = low + ((high - low) >> 1);
                        order = match self.compare_classes(&element, &kept[index])? {
                            Compared::Order(order) => order,
                            Compared::Failed(message) => return Ok(Err(message)),
                        };
                        match order {
                            Ordering::Equal => break,
                            Ordering::Less => high = index,
                            Ordering::Greater => low = index + 1,
                        }
                    }
                    if kept.is_empty() {
                        kept.push(element);
                    } else if order != Ordering::Equal {
                        let at = if order == Ordering::Less {
                            index
                        } else {
                            index + 1
                        };
                        kept.insert(at, element);
                    }
                }
                Ok(Ok(ConfigValue::Set(kept)))
            }
            value => Ok(Ok(value.clone())),
        }
    }

    /// `compareTo` of TLC's class of `left` with `right`, both normalized: IntValue, StringValue,
    /// BoolValue, ModelValue (`modelValueCompareTo` where the model value is the argument) and
    /// SetEnumValue.
    fn compare_classes(&self, left: &ConfigValue, right: &ConfigValue) -> Result<Compared> {
        let failed = |message: String| -> Result<Compared> { Ok(Compared::Failed(message)) };
        // A receiver of another class asks a model value argument (`modelValueCompareTo`).
        if let (false, ConfigValue::ModelValue(name)) =
            (matches!(left, ConfigValue::ModelValue(_)), right)
        {
            return match get_model_value_type(name) {
                Some(_) => failed(format!(
                    "Attempted to compare the typed model value {name} and the non-model value\n{}",
                    format_value(left)?
                )),
                None => Ok(Compared::Order(Ordering::Greater)),
            };
        }
        Ok(match (left, right) {
            (ConfigValue::Record(_), _) | (_, ConfigValue::Record(_)) => {
                return Err(not_followed());
            }
            (ConfigValue::ModelValue(name), other) => match (get_model_value_type(name), other) {
                (None, ConfigValue::ModelValue(other)) => {
                    Compared::Order(self.compare_strings(name, other)?)
                }
                (None, _) => Compared::Order(Ordering::Less),
                (Some(kind), ConfigValue::ModelValue(other)) => {
                    let other_kind = get_model_value_type(other);
                    if other_kind.is_none() || other_kind == Some(kind) {
                        Compared::Order(self.compare_strings(name, other)?)
                    } else {
                        return failed(format!(
                            "Attempted to compare the differently-typed model values {name} and {other}"
                        ));
                    }
                }
                (Some(_), other) => {
                    return failed(format!(
                        "Attempted to compare the typed model value {name} and non-model value\n{}",
                        format_value(other)?
                    ));
                }
            },
            (ConfigValue::Number(left), ConfigValue::Number(right)) => {
                Compared::Order(left.total_cmp(right))
            }
            (ConfigValue::Number(_), other) => {
                return failed(format!(
                    "Attempted to compare integer {} with non-integer:\n{}",
                    format_value(left)?,
                    format_value(other)?
                ));
            }
            (ConfigValue::String(left_text), ConfigValue::String(right_text)) => {
                Compared::Order(self.compare_strings(left_text, right_text)?)
            }
            (ConfigValue::String(_), other) => {
                return failed(format!(
                    "Attempted to compare string {} with non-string:\n{}",
                    format_value(left)?,
                    format_value(other)?
                ));
            }
            (ConfigValue::Boolean(left_value), ConfigValue::Boolean(right_value)) => {
                Compared::Order(left_value.cmp(right_value))
            }
            (ConfigValue::Boolean(_), other) => {
                return failed(format!(
                    "Attempted to compare boolean {} with non-boolean:\n{}",
                    format_value(left)?,
                    format_value(other)?
                ));
            }
            (ConfigValue::Set(left_elements), ConfigValue::Set(right_elements)) => {
                if left_elements.len() != right_elements.len() {
                    Compared::Order(left_elements.len().cmp(&right_elements.len()))
                } else {
                    for (left, right) in left_elements.iter().zip(right_elements) {
                        match self.compare_classes(left, right)? {
                            Compared::Order(Ordering::Equal) => {}
                            compared => return Ok(compared),
                        }
                    }
                    Compared::Order(Ordering::Equal)
                }
            }
            (ConfigValue::Set(_), other) => {
                return failed(format!(
                    "Attempted to compare the set {} with the value:\n{}",
                    format_value(left)?,
                    format_value(other)?
                ));
            }
        })
    }
}

fn not_followed() -> FrontError {
    FrontError::NotYet("a configured constant TLC may fail to normalize".to_owned())
}

/// `Values.ppr` of a normalized configuration value, which is its `toString` where that is short
/// enough not to be broken.
fn format_value(value: &ConfigValue) -> Result<String> {
    let text = format_plain(value)?;
    if text.chars().count() > 60 {
        return Err(not_followed());
    }
    Ok(text)
}

fn format_plain(value: &ConfigValue) -> Result<String> {
    Ok(match value {
        ConfigValue::Boolean(value) => if *value { "TRUE" } else { "FALSE" }.to_owned(),
        ConfigValue::Number(number) => format!("{number}"),
        ConfigValue::String(text) => {
            if text
                .chars()
                .any(|character| character == '"' || character == '\\' || character.is_control())
            {
                return Err(not_followed());
            }
            format!("\"{text}\"")
        }
        ConfigValue::ModelValue(name) => name.clone(),
        ConfigValue::Set(elements) => format!(
            "{{{}}}",
            elements
                .iter()
                .map(format_plain)
                .collect::<Result<Vec<_>>>()?
                .join(", ")
        ),
        ConfigValue::Record(_) => return Err(not_followed()),
    })
}
