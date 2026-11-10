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
        let mut failure = None;
        let mut sorted = elements.clone();
        sorted.sort_by(|left, right| {
            self.compare(left, right).unwrap_or_else(|error| {
                failure.get_or_insert(error);
                Ordering::Equal
            })
        });
        if let Some(error) = failure {
            return Err(error);
        }
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
