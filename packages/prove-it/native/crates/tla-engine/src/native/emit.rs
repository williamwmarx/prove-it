//! Emits a function of the IR as x86-64 (native/design/native-backend.md 4), as `call.rs` calls it:
//! `extern "sysv64" fn(*mut Context) -> u32`. The context stays in rbx and each register has a
//! stack slot of its own. Reads of a bound name or a variable are inline, as is equality of equal
//! ids; the rest calls a helper, after which every base is read again from the context.

use tla_values::store::TRUE;

use super::call::{BAILED, CURRENT, FAILS, HOLDS, LOCALS};
use super::helpers::{self, NOT_BOOLEAN, UNASSIGNED};
use super::ir::{End, Function, Instruction, Register};
use super::x86_64::{Assembler, Condition, Gpr, Label, Memory, Width};

enum Argument {
    Register(Register),
    Immediate(u32),
}

pub(crate) fn function(function: &Function) -> Vec<u8> {
    let mut assembler = Assembler::new();
    let blocks: Vec<Label> = function.blocks.iter().map(|_| assembler.label()).collect();
    let mut emitter = Emitter {
        exit: assembler.label(),
        bailed: assembler.label(),
        unassigned: assembler.label(),
        not_boolean: assembler.label(),
        assembler,
    };
    // A slot of 8 bytes per register, in a frame that keeps rsp 16-byte aligned at each call:
    // the return address and rbx take 16.
    let frame = (function.registers as i32 * 8 + 15) & !15;
    let assembler = &mut emitter.assembler;
    assembler.push(Gpr::Rbx);
    assembler.mov(Width::W64, Gpr::Rbx, Gpr::Rdi);
    assembler.sub_immediate(Width::W64, Gpr::Rsp, frame);
    for (index, block) in function.blocks.iter().enumerate() {
        emitter.assembler.bind(blocks[index]);
        for instruction in &block.instructions {
            emitter.instruction(instruction);
        }
        let next = blocks.get(index + 1).copied();
        match block.end {
            End::Branch {
                value,
                then,
                otherwise,
            } => {
                emitter.read(Gpr::Rax, value);
                let assembler = &mut emitter.assembler;
                assembler.cmp_immediate(Width::W32, Gpr::Rax, TRUE as i32);
                assembler.jump_if(Condition::Equal, blocks[then.0 as usize]);
                emitter.jump(blocks[otherwise.0 as usize], next);
            }
            End::Jump(target) => emitter.jump(blocks[target.0 as usize], next),
            End::Return(value) => {
                emitter.result(if value { HOLDS } else { FAILS });
            }
        }
    }
    emitter.bails(emitter.unassigned, UNASSIGNED);
    emitter.bails(emitter.not_boolean, NOT_BOOLEAN);
    let assembler = &mut emitter.assembler;
    assembler.bind(emitter.bailed);
    assembler.mov_immediate(Gpr::Rax, u64::from(BAILED));
    assembler.bind(emitter.exit);
    assembler.add_immediate(Width::W64, Gpr::Rsp, frame);
    assembler.pop(Gpr::Rbx);
    assembler.ret();
    emitter.assembler.finish()
}

struct Emitter {
    assembler: Assembler,
    exit: Label,
    // Where a helper has bailed, its reason already in the context.
    bailed: Label,
    unassigned: Label,
    not_boolean: Label,
}

fn slot(register: Register) -> Memory {
    Memory::at(Gpr::Rsp, register.0 as i32 * 8)
}

// The offset of an id in a vector of ids.
fn offset(index: u32) -> i32 {
    i32::try_from(u64::from(index) * 4).expect("an index within 2 GiB")
}

impl Emitter {
    fn instruction(&mut self, instruction: &Instruction) {
        match *instruction {
            Instruction::Constant { into, id } => {
                self.assembler.mov_immediate(Gpr::Rax, u64::from(id));
                self.write(into);
            }
            Instruction::Slot { into, slot } => {
                self.load_id(LOCALS, slot);
                self.write(into);
            }
            Instruction::Current { into, variable } => {
                self.load_id(CURRENT, variable);
                // UNASSIGNED is u32::MAX.
                self.assembler.cmp_immediate(Width::W32, Gpr::Rax, -1);
                self.assembler.jump_if(Condition::Equal, self.unassigned);
                self.write(into);
            }
            Instruction::Apply {
                into,
                function,
                key,
            } => {
                self.call(
                    helpers::apply as *const () as usize,
                    &[Argument::Register(function), Argument::Register(key)],
                );
                self.write(into);
            }
            Instruction::Equal { into, left, right } => {
                let (slow, done) = (self.assembler.label(), self.assembler.label());
                self.read(Gpr::Rax, left);
                self.assembler.cmp_memory(Width::W32, Gpr::Rax, slot(right));
                self.assembler.jump_if(Condition::NotEqual, slow);
                self.assembler.mov_immediate(Gpr::Rax, u64::from(TRUE));
                self.assembler.jump(done);
                self.assembler.bind(slow);
                self.call(
                    helpers::equals as *const () as usize,
                    &[Argument::Register(left), Argument::Register(right)],
                );
                self.assembler.bind(done);
                self.write(into);
            }
            Instruction::Member { into, element, set } => {
                self.call(
                    helpers::member as *const () as usize,
                    &[Argument::Register(element), Argument::Register(set)],
                );
                self.write(into);
            }
            Instruction::Eval { into, eval } => {
                self.call(
                    helpers::eval as *const () as usize,
                    &[Argument::Immediate(eval)],
                );
                self.write(into);
            }
            Instruction::CheckBoolean { value } => {
                // FALSE and TRUE are 0 and 1.
                self.read(Gpr::Rax, value);
                self.assembler.cmp_immediate(Width::W32, Gpr::Rax, 2);
                self.assembler
                    .jump_if(Condition::AboveOrEqual, self.not_boolean);
            }
        }
    }

    // eax = the id at `index` of the vector whose base is at `base` in the context.
    fn load_id(&mut self, base: i32, index: u32) {
        self.assembler
            .load(Width::W64, Gpr::Rax, Memory::at(Gpr::Rbx, base));
        self.assembler
            .load(Width::W32, Gpr::Rax, Memory::at(Gpr::Rax, offset(index)));
    }

    fn read(&mut self, to: Gpr, register: Register) {
        self.assembler.load(Width::W32, to, slot(register));
    }

    fn write(&mut self, register: Register) {
        self.assembler.store(Width::W32, slot(register), Gpr::Rax);
    }

    // Calls a helper with the context and the arguments, going to `bailed` if it bails.
    fn call(&mut self, helper: usize, arguments: &[Argument]) {
        self.assembler.mov(Width::W64, Gpr::Rdi, Gpr::Rbx);
        for (argument, to) in arguments.iter().zip([Gpr::Rsi, Gpr::Rdx]) {
            match *argument {
                Argument::Register(register) => self.read(to, register),
                Argument::Immediate(value) => self.assembler.mov_immediate(to, u64::from(value)),
            }
        }
        self.assembler.mov_immediate(Gpr::Rax, helper as u64);
        self.assembler.call(Gpr::Rax);
        // helpers::BAILED is u64::MAX.
        const _: () = assert!(helpers::BAILED == u64::MAX);
        self.assembler.cmp_immediate(Width::W64, Gpr::Rax, -1);
        self.assembler.jump_if(Condition::Equal, self.bailed);
    }

    fn jump(&mut self, target: Label, next: Option<Label>) {
        if next != Some(target) {
            self.assembler.jump(target);
        }
    }

    fn result(&mut self, value: u32) {
        self.assembler.mov_immediate(Gpr::Rax, u64::from(value));
        self.assembler.jump(self.exit);
    }

    // A bail for one of the helpers' reasons, which emitted code takes itself.
    fn bails(&mut self, label: Label, reason: u32) {
        self.assembler.bind(label);
        self.call(
            helpers::bail as *const () as usize,
            &[Argument::Immediate(reason)],
        );
    }
}

#[cfg(all(test, target_os = "linux"))]
mod tests {
    use std::sync::Arc;

    use tla_values::store::{FALSE, Store, TRUE};

    use super::function;
    use crate::compile::predicate::{Leaf, Predicate};
    use crate::machine::{Eval, Machine};
    use crate::native::call::Native;
    use crate::native::{generated, ir};

    fn emit(predicate: &Predicate) -> Native {
        let lowered = ir::lower(predicate);
        Native::new(&function(&lowered), lowered.evals, true).expect("executable memory")
    }

    #[test]
    fn emits_predicates_that_evaluate_as_their_closures() {
        let program = generated::program();
        let outcomes = generated::compare(&program, |predicate| {
            let native = emit(predicate);
            Box::new(move |machine| native.run(machine))
        });
        // Each outcome is common enough that the comparison means something.
        assert!(outcomes.iter().all(|&count| count > 1_000), "{outcomes:?}");
    }

    // A helper may move the vectors the code reads in place, so the code reads their bases again.
    #[test]
    fn reads_vectors_a_helper_moved() {
        let program = generated::program();
        let mut store = Store::new();
        store.reset(std::iter::empty::<&[u16]>());
        let mut machine = Machine::new(&program, store);
        machine.cur.fill(TRUE);
        machine.locals.fill(TRUE);
        let moves: Eval = Arc::new(|machine: &mut Machine<'_>| {
            machine.cur = vec![FALSE; machine.cur.len()];
            machine.locals = vec![FALSE; machine.locals.len()];
            Ok(TRUE)
        });
        let holds: Eval = Arc::new(|_: &mut Machine<'_>| Ok(TRUE));
        let predicate = Predicate::And(vec![
            Predicate::Eval {
                eval: moves,
                is_checked: true,
            },
            Predicate::Equal {
                left: Leaf::Current(0),
                right: Leaf::Constant(FALSE),
                is_equal: true,
            },
            Predicate::Equal {
                left: Leaf::Slot(2),
                right: Leaf::Constant(FALSE),
                is_equal: true,
            },
            // A call after the reads, whose helper checks the bases it's handed are current.
            Predicate::Eval {
                eval: holds,
                is_checked: true,
            },
        ]);
        assert_eq!(emit(&predicate).run(&mut machine), Ok(true));
    }

    // A panic can't unwind through emitted code, so it reaches the caller past it, as a panic.
    #[test]
    fn resumes_a_panic_past_the_code() {
        let program = generated::program();
        let mut store = Store::new();
        store.reset(std::iter::empty::<&[u16]>());
        let mut machine = Machine::new(&program, store);
        let panics: Eval = Arc::new(|_: &mut Machine<'_>| panic!("an eval's panic"));
        let native = emit(&Predicate::Eval {
            eval: panics,
            is_checked: true,
        });
        let payload =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| native.run(&mut machine)))
                .expect_err("the panic");
        assert_eq!(payload.downcast_ref::<&str>(), Some(&"an eval's panic"));
    }
}
