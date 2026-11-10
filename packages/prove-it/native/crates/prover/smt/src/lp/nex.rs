// Ported from Z3 (src/math/lp/nex.h), MIT license, see z3-license.txt. The nonlinear expressions
// that horner splits into cross-nested forms: scalars, variables, products of powers with a
// coefficient, and sums. Products and sums are mutable, since nex_creator simplifies them in place
// and cross_nested rewrites their children.
//
// The TypeScript shares subtrees between expressions, compares expressions by identity (`===` in
// nex_creator's gt), and mutates shared products and sums in place (the coefficient that
// sort_join_sum merges into a summand, the children that cross_nested's slots rewrite). So an
// expression here is a `NexId`, an index into the arena `NexCreator::nexes` that owns every node:
// two ids are the same expression exactly when the TypeScript objects are the same object, and a
// mutation through an id is seen by every expression that shares the node, as in the TypeScript.
// The functions of this file read the arena they are given.
use prove_num::Rational;

/// An index into `NexCreator::nexes`.
pub type NexId = usize;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct NexPow {
    pub expr: NexId,
    pub power: u32,
}

#[derive(Clone, Debug)]
pub struct NexMul {
    pub coeff: Rational,
    pub children: Vec<NexPow>,
}

#[derive(Clone, Debug)]
pub struct NexSum {
    pub children: Vec<NexId>,
}

#[derive(Clone, Debug)]
pub enum Nex {
    Scalar(Rational),
    Var(usize),
    Mul(NexMul),
    Sum(NexSum),
}

pub fn is_elementary(nexes: &[Nex], expr: NexId) -> bool {
    matches!(nexes[expr], Nex::Scalar(_) | Nex::Var(_))
}

pub fn is_zero_scalar(nexes: &[Nex], expr: NexId) -> bool {
    matches!(&nexes[expr], Nex::Scalar(value) if value.is_zero())
}

pub fn contains_var(nexes: &[Nex], expr: NexId, variable: usize) -> bool {
    match &nexes[expr] {
        Nex::Var(expr_variable) => *expr_variable == variable,
        Nex::Mul(mul) => mul
            .children
            .iter()
            .any(|child| contains_var(nexes, child.expr, variable)),
        _ => false,
    }
}

pub fn get_degree(nexes: &[Nex], expr: NexId) -> u32 {
    match &nexes[expr] {
        Nex::Scalar(_) => 0,
        Nex::Var(_) => 1,
        Nex::Mul(mul) => mul.children.iter().fold(0, |degree, child| {
            degree + get_degree(nexes, child.expr) * child.power
        }),
        Nex::Sum(sum) => sum
            .children
            .iter()
            .fold(0, |degree, child| degree.max(get_degree(nexes, *child))),
    }
}

pub fn is_linear(nexes: &[Nex], expr: NexId) -> bool {
    match &nexes[expr] {
        Nex::Mul(_) => get_degree(nexes, expr) < 2,
        Nex::Sum(sum) => sum.children.iter().all(|child| is_linear(nexes, *child)),
        _ => true,
    }
}

// is_a_linear_term: a linear combination of at least two variables.
pub fn is_a_linear_term(nexes: &[Nex], sum: &NexSum) -> bool {
    let mut number_of_non_scalars = 0;
    for child in &sum.children {
        let degree = get_degree(nexes, *child);
        if degree == 0 {
            continue;
        }
        if degree > 1 {
            return false;
        }
        number_of_non_scalars += 1;
    }
    number_of_non_scalars > 1
}

// get_powers_from_mul: refills powers with the power of each variable child. powers is the
// TypeScript's insertion-ordered Map from a variable to its power.
pub fn get_powers_from_mul(nexes: &[Nex], mul: &NexMul, powers: &mut Vec<(usize, u32)>) {
    powers.clear();
    for child in &mul.children {
        let Nex::Var(variable) = nexes[child.expr] else {
            continue;
        };
        match powers.iter_mut().find(|entry| entry.0 == variable) {
            Some(entry) => entry.1 = child.power,
            None => powers.push((variable, child.power)),
        }
    }
}

pub fn get_nex_val(
    nexes: &[Nex],
    expr: NexId,
    get_var_val: &dyn Fn(usize) -> Rational,
) -> Rational {
    match &nexes[expr] {
        Nex::Scalar(value) => value.clone(),
        Nex::Var(variable) => get_var_val(*variable),
        Nex::Sum(sum) => sum.children.iter().fold(Rational::zero(), |value, child| {
            value.add(&get_nex_val(nexes, *child, get_var_val))
        }),
        Nex::Mul(mul) => mul.children.iter().fold(mul.coeff.clone(), |value, child| {
            value.mul(&get_nex_val(nexes, child.expr, get_var_val).pow(child.power))
        }),
    }
}

// The variables in the order of their first occurrence, each once, as the TypeScript's Set.
pub fn get_vars_of_expr(nexes: &[Nex], expr: NexId) -> Vec<usize> {
    let children: Vec<NexId> = match &nexes[expr] {
        Nex::Scalar(_) => return Vec::new(),
        Nex::Var(variable) => return vec![*variable],
        Nex::Sum(sum) => sum.children.clone(),
        Nex::Mul(mul) => mul.children.iter().map(|child| child.expr).collect(),
    };
    let mut vars = Vec::new();
    for child in children {
        for variable in get_vars_of_expr(nexes, child) {
            if !vars.contains(&variable) {
                vars.push(variable);
            }
        }
    }
    vars
}

fn print_nex_pow(nexes: &[Nex], child: &NexPow) -> String {
    let printed = print_nex(nexes, child.expr);
    let is_child_elementary = is_elementary(nexes, child.expr);
    if child.power == 1 {
        return if is_child_elementary {
            printed
        } else {
            format!("({printed})")
        };
    }
    if is_child_elementary {
        format!("({printed}^{})", child.power)
    } else {
        format!("(({printed})^{})", child.power)
    }
}

pub fn print_nex(nexes: &[Nex], expr: NexId) -> String {
    match &nexes[expr] {
        Nex::Scalar(value) => value.to_string(),
        Nex::Var(variable) => format!("j{variable}"),
        // Like Z3, a coefficient other than one is followed by a space and a star before each
        // factor.
        Nex::Mul(mul) => {
            if mul.coeff == Rational::one() {
                return mul
                    .children
                    .iter()
                    .map(|child| print_nex_pow(nexes, child))
                    .collect::<Vec<_>>()
                    .join("*");
            }
            let factors: String = mul
                .children
                .iter()
                .map(|child| format!("*{}", print_nex_pow(nexes, child)))
                .collect();
            format!("{} {factors}", mul.coeff)
        }
        Nex::Sum(sum) => sum
            .children
            .iter()
            .enumerate()
            .map(|(index, child)| {
                let printed = print_nex(nexes, *child);
                if !is_elementary(nexes, *child) {
                    return if index == 0 {
                        format!("({printed})")
                    } else {
                        format!("+({printed})")
                    };
                }
                if index == 0 || printed.starts_with('-') {
                    printed
                } else {
                    format!("+{printed}")
                }
            })
            .collect(),
    }
}
