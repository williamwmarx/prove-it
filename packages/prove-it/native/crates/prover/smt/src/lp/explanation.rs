// Ported from Z3 (src/math/lp/explanation.h), MIT license, see z3-license.txt. The constraints
// behind a conflict or a propagation: weighted pairs, or a set of constraint indices whose
// iteration order is the slot order of Z3's hashtable.
use crate::lp::dependency::{Dependency, linearize};
use crate::util::hashtable::ObjMap;
use prove_num::Rational;

#[derive(Clone)]
pub struct Explanation {
    pairs: Vec<(usize, Rational)>,
    indices: ObjMap<()>,
}

impl Default for Explanation {
    fn default() -> Explanation {
        Explanation::new()
    }
}

impl Explanation {
    pub fn new() -> Explanation {
        Explanation {
            pairs: Vec::new(),
            indices: ObjMap::new(),
        }
    }

    pub fn clear(&mut self) {
        self.pairs.clear();
        self.indices.clear();
    }

    pub fn add_pair(&mut self, constraint: usize, coeff: Rational) {
        self.pairs.push((constraint, coeff));
    }

    pub fn push(&mut self, constraint: usize) {
        self.indices
            .insert(constraint as u32, constraint as u32, ());
    }

    // push_explanation: the constraints behind a dependency.
    pub fn push_dependency(&mut self, dep: &Dependency) {
        for constraint in linearize(std::slice::from_ref(dep)) {
            self.push(constraint as usize);
        }
    }

    pub fn is_empty(&self) -> bool {
        self.pairs.is_empty() && self.indices.is_empty()
    }

    // add_expl: the pairs of the other explanation, or its indices when it has no pairs.
    pub fn add_explanation(&mut self, other: &Explanation) {
        if other.pairs.is_empty() {
            for constraint in other.indices.keys() {
                self.push(constraint as usize);
            }
        } else {
            for pair in &other.pairs {
                self.add_pair(pair.0, pair.1.clone());
            }
        }
    }

    // The constraints, from the pairs when there are any and from the indices otherwise.
    pub fn iter(&self) -> Box<dyn Iterator<Item = usize> + '_> {
        if self.pairs.is_empty() {
            Box::new(self.indices.keys().map(|key| key as usize))
        } else {
            Box::new(self.pairs.iter().map(|pair| pair.0))
        }
    }

    pub fn pairs(&self) -> &[(usize, Rational)] {
        &self.pairs
    }
}
