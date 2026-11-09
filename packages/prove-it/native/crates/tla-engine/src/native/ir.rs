//! The native IR (native/design/native-backend.md 3): what the backend emits code from, lowered from
//! the decisions the closure compiler already made. For now it lowers fused predicates, the guards
//! and invariants of N1, into blocks of a few instructions whose branches are the predicates' short
//! circuits. A leaf the IR doesn't read itself is a call of the closure the compiler built for it.

use std::fmt;

use tla_values::Id;

use crate::compile::predicate::{Leaf, Predicate};
use crate::machine::Eval;

/// A register holds an id, or a boolean as FALSE or TRUE.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Register(pub(crate) u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct BlockId(pub(crate) u32);

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Instruction {
    Constant {
        into: Register,
        id: Id,
    },
    Slot {
        into: Register,
        slot: u32,
    },
    /// An unprimed variable, which bails while unassigned.
    Current {
        into: Register,
        variable: u32,
    },
    /// `f[k]`, as `predicate::apply` applies it.
    Apply {
        into: Register,
        function: Register,
        key: Register,
    },
    /// TLC's equality, as `predicate::equals` decides it.
    Equal {
        into: Register,
        left: Register,
        right: Register,
    },
    /// `e \in S`, failing on a non-set.
    Member {
        into: Register,
        element: Register,
        set: Register,
    },
    /// A call of a closure the compiler built, by its index in [`Function::evals`].
    Eval {
        into: Register,
        eval: u32,
    },
    /// Bails unless the register holds a boolean.
    CheckBoolean {
        value: Register,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum End {
    /// To `then` if the register holds TRUE, else to `otherwise`.
    Branch {
        value: Register,
        then: BlockId,
        otherwise: BlockId,
    },
    Jump(BlockId),
    Return(bool),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Block {
    pub(crate) instructions: Vec<Instruction>,
    pub(crate) end: End,
}

/// A predicate as blocks, the first of which it starts at.
pub(crate) struct Function {
    pub(crate) blocks: Vec<Block>,
    pub(crate) registers: u32,
    pub(crate) evals: Vec<Eval>,
}

/// Lowers a fused predicate, evaluating what its closures evaluate, in the same order, with the
/// same short circuits and the same failures.
pub(crate) fn lower(predicate: &Predicate) -> Function {
    let mut lowering = Lowering {
        blocks: vec![Block {
            instructions: Vec::new(),
            end: End::Return(false),
        }],
        registers: 0,
        evals: Vec::new(),
    };
    let holds = lowering.block(End::Return(true));
    let fails = lowering.block(End::Return(false));
    lowering.predicate(BlockId(0), predicate, holds, fails);
    Function {
        blocks: lowering.blocks,
        registers: lowering.registers,
        evals: lowering.evals,
    }
}

struct Lowering {
    blocks: Vec<Block>,
    registers: u32,
    evals: Vec<Eval>,
}

impl Lowering {
    fn block(&mut self, end: End) -> BlockId {
        self.blocks.push(Block {
            instructions: Vec::new(),
            end,
        });
        BlockId(self.blocks.len() as u32 - 1)
    }

    fn register(&mut self) -> Register {
        self.registers += 1;
        Register(self.registers - 1)
    }

    fn push(&mut self, block: BlockId, instruction: Instruction) {
        self.blocks[block.0 as usize].instructions.push(instruction);
    }

    fn read(&mut self, block: BlockId, leaf: &Leaf) -> Register {
        let into = self.register();
        let instruction = match leaf {
            Leaf::Slot(slot) | Leaf::IntSlot(slot) => Instruction::Slot { into, slot: *slot },
            Leaf::Constant(id) => Instruction::Constant { into, id: *id },
            Leaf::Current(variable) => Instruction::Current {
                into,
                variable: *variable,
            },
            Leaf::ApplyVar { variable, slot, .. } => {
                let function = self.read(block, &Leaf::Current(*variable));
                let key = self.read(block, &Leaf::Slot(*slot));
                Instruction::Apply {
                    into,
                    function,
                    key,
                }
            }
            Leaf::ApplyVar2 {
                variable,
                slot,
                second,
            } => {
                let function = self.read(
                    block,
                    &Leaf::ApplyVar {
                        variable: *variable,
                        slot: *slot,
                        is_int: false,
                    },
                );
                let key = self.read(block, &Leaf::Slot(*second));
                Instruction::Apply {
                    into,
                    function,
                    key,
                }
            }
            Leaf::Eval(eval) => Instruction::Eval {
                into,
                eval: self.eval(eval),
            },
        };
        self.push(block, instruction);
        into
    }

    fn eval(&mut self, eval: &Eval) -> u32 {
        self.evals.push(eval.clone());
        self.evals.len() as u32 - 1
    }

    fn branch(&mut self, block: BlockId, value: Register, then: BlockId, otherwise: BlockId) {
        self.blocks[block.0 as usize].end = End::Branch {
            value,
            then,
            otherwise,
        };
    }

    // Lowers the predicate into `block`, going to `holds` if it holds and to `fails` if not.
    fn predicate(&mut self, block: BlockId, predicate: &Predicate, holds: BlockId, fails: BlockId) {
        match predicate {
            Predicate::Equal {
                left,
                right,
                is_equal,
            } => {
                let left = self.read(block, left);
                let right = self.read(block, right);
                let into = self.register();
                self.push(block, Instruction::Equal { into, left, right });
                let (then, otherwise) = if *is_equal {
                    (holds, fails)
                } else {
                    (fails, holds)
                };
                self.branch(block, into, then, otherwise);
            }
            Predicate::Member {
                element,
                set,
                is_in,
            } => {
                let element = self.read(block, element);
                let set = self.read(block, set);
                let into = self.register();
                self.push(block, Instruction::Member { into, element, set });
                let (then, otherwise) = if *is_in {
                    (holds, fails)
                } else {
                    (fails, holds)
                };
                self.branch(block, into, then, otherwise);
            }
            Predicate::Not(operand) => self.predicate(block, operand, fails, holds),
            Predicate::And(operands) => self.junction(block, operands, holds, fails, true),
            Predicate::Or(operands) => self.junction(block, operands, holds, fails, false),
            Predicate::Implies(antecedent, consequent) => {
                let next = self.block(End::Return(false));
                self.predicate(block, antecedent, next, holds);
                self.predicate(next, consequent, holds, fails);
            }
            Predicate::Eval { eval, is_checked } => {
                let into = self.register();
                let eval = self.eval(eval);
                self.push(block, Instruction::Eval { into, eval });
                if *is_checked {
                    self.push(block, Instruction::CheckBoolean { value: into });
                }
                self.branch(block, into, holds, fails);
            }
        }
    }

    // `/\` goes on while its operands hold and `\/` while they fail, each to a block of its own.
    fn junction(
        &mut self,
        block: BlockId,
        operands: &[Predicate],
        holds: BlockId,
        fails: BlockId,
        is_and: bool,
    ) {
        let Some((last, rest)) = operands.split_last() else {
            self.blocks[block.0 as usize].end = End::Jump(if is_and { holds } else { fails });
            return;
        };
        let mut current = block;
        for operand in rest {
            let next = self.block(End::Return(false));
            let (then, otherwise) = if is_and { (next, fails) } else { (holds, next) };
            self.predicate(current, operand, then, otherwise);
            current = next;
        }
        self.predicate(current, last, holds, fails);
    }
}

impl fmt::Display for Function {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (index, block) in self.blocks.iter().enumerate() {
            writeln!(formatter, "b{index}:")?;
            for instruction in &block.instructions {
                writeln!(formatter, "  {instruction}")?;
            }
            match block.end {
                End::Branch {
                    value,
                    then,
                    otherwise,
                } => writeln!(
                    formatter,
                    "  branch r{} b{} b{}",
                    value.0, then.0, otherwise.0
                )?,
                End::Jump(target) => writeln!(formatter, "  jump b{}", target.0)?,
                End::Return(value) => writeln!(formatter, "  return {value}")?,
            }
        }
        Ok(())
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Instruction::Constant { into, id } => write!(formatter, "r{} = id {id}", into.0),
            Instruction::Slot { into, slot } => write!(formatter, "r{} = slot {slot}", into.0),
            Instruction::Current { into, variable } => {
                write!(formatter, "r{} = current {variable}", into.0)
            }
            Instruction::Apply {
                into,
                function,
                key,
            } => write!(formatter, "r{} = apply r{} r{}", into.0, function.0, key.0),
            Instruction::Equal { into, left, right } => {
                write!(formatter, "r{} = equal r{} r{}", into.0, left.0, right.0)
            }
            Instruction::Member { into, element, set } => {
                write!(formatter, "r{} = member r{} r{}", into.0, element.0, set.0)
            }
            Instruction::Eval { into, eval } => write!(formatter, "r{} = eval {eval}", into.0),
            Instruction::CheckBoolean { value } => write!(formatter, "check boolean r{}", value.0),
        }
    }
}

#[cfg(test)]
mod tests {
    use tla_values::Bail;
    use tla_values::store::{FALSE, KIND_SET, Outcome, TRUE};

    use super::{End, Function, Instruction, lower};
    use crate::compile::predicate::{self, Leaf, Predicate};
    use crate::machine::Machine;
    use crate::native::generated;

    // Runs a function's blocks as the closures run the predicate: the reference the emitted code
    // will be held to.
    fn interpret(function: &Function, machine: &mut Machine<'_>) -> Outcome<bool> {
        let mut registers = vec![0; function.registers as usize];
        let mut block = 0;
        loop {
            for instruction in &function.blocks[block].instructions {
                match *instruction {
                    Instruction::Constant { into, id } => registers[into.0 as usize] = id,
                    Instruction::Slot { into, slot } => {
                        registers[into.0 as usize] = machine.locals[slot as usize];
                    }
                    Instruction::Current { into, variable } => {
                        registers[into.0 as usize] = machine.read_current(variable)?;
                    }
                    Instruction::Apply {
                        into,
                        function,
                        key,
                    } => {
                        let (function, key) =
                            (registers[function.0 as usize], registers[key.0 as usize]);
                        registers[into.0 as usize] = predicate::apply(machine, function, key)?;
                    }
                    Instruction::Equal { into, left, right } => {
                        let (left, right) =
                            (registers[left.0 as usize], registers[right.0 as usize]);
                        let is_equal = predicate::equals(machine, left, right)?;
                        registers[into.0 as usize] = machine.store.bool(is_equal);
                    }
                    Instruction::Member { into, element, set } => {
                        let (element, set) =
                            (registers[element.0 as usize], registers[set.0 as usize]);
                        if machine.store.kind_of(set) != KIND_SET {
                            return Err(Bail("membership in a non-set"));
                        }
                        let is_member = machine.store.is_member(element, set)?;
                        registers[into.0 as usize] = machine.store.bool(is_member);
                    }
                    Instruction::Eval { into, eval } => {
                        registers[into.0 as usize] = function.evals[eval as usize](machine)?;
                    }
                    Instruction::CheckBoolean { value } => {
                        if !matches!(registers[value.0 as usize], TRUE | FALSE) {
                            return Err(Bail("expected a boolean"));
                        }
                    }
                }
            }
            match function.blocks[block].end {
                End::Branch {
                    value,
                    then,
                    otherwise,
                } => {
                    block = if registers[value.0 as usize] == TRUE {
                        then.0
                    } else {
                        otherwise.0
                    } as usize;
                }
                End::Jump(target) => block = target.0 as usize,
                End::Return(value) => return Ok(value),
            }
        }
    }

    #[test]
    fn lowers_predicates_to_blocks_that_evaluate_as_their_closures() {
        let program = generated::program();
        let outcomes = generated::compare(&program, |predicate| {
            let function = lower(predicate);
            Box::new(move |machine| interpret(&function, machine))
        });
        // Each outcome is common enough that the comparison means something.
        assert!(outcomes.iter().all(|&count| count > 1_000), "{outcomes:?}");
    }

    #[test]
    fn prints_short_circuits_as_branches() {
        let predicate = Predicate::And(vec![
            Predicate::Equal {
                left: Leaf::Current(0),
                right: Leaf::Constant(7),
                is_equal: true,
            },
            Predicate::Not(Box::new(Predicate::Member {
                element: Leaf::Slot(1),
                set: Leaf::Current(2),
                is_in: true,
            })),
        ]);
        assert_eq!(
            lower(&predicate).to_string(),
            "b0:\n  r0 = current 0\n  r1 = id 7\n  r2 = equal r0 r1\n  branch r2 b3 b2\n\
             b1:\n  return true\n\
             b2:\n  return false\n\
             b3:\n  r3 = slot 1\n  r4 = current 2\n  r5 = member r3 r4\n  branch r5 b2 b1\n"
        );
    }
}
