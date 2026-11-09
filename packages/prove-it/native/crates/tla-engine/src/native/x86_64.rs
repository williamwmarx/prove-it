//! An encoder for the x86-64 instructions the backend emits (native/design/native-backend.md 4):
//! the forms the code of a predicate needs, and labels whose jumps are patched once the code is
//! whole. It only writes bytes; [`super::memory`] makes them executable.

/// A general-purpose register, by its number in the encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(
    not(test),
    expect(dead_code, reason = "the whole register file, which N2 allocates")
)]
pub(crate) enum Gpr {
    Rax,
    Rcx,
    Rdx,
    Rbx,
    Rsp,
    Rbp,
    Rsi,
    Rdi,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
}

impl Gpr {
    fn low(self) -> u8 {
        self as u8 & 7
    }

    fn is_extended(self) -> bool {
        self as u8 >= 8
    }
}

/// A memory operand: `[base + index * scale + displacement]`, the index being optional.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Memory {
    pub(crate) base: Gpr,
    pub(crate) index: Option<(Gpr, Scale)>,
    pub(crate) displacement: i32,
}

impl Memory {
    pub(crate) fn at(base: Gpr, displacement: i32) -> Memory {
        Memory {
            base,
            index: None,
            displacement,
        }
    }

    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "N2's segments, bounds checks and memo probes use it"
        )
    )]
    pub(crate) fn indexed(base: Gpr, index: Gpr, scale: Scale, displacement: i32) -> Memory {
        assert_ne!(index, Gpr::Rsp, "rsp can't be an index");
        Memory {
            base,
            index: Some((index, scale)),
            displacement,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "N2's segments, bounds checks and memo probes use it"
    )
)]
pub(crate) enum Scale {
    One = 0,
    Four = 2,
    Eight = 3,
}

/// A condition of `jcc` and `cmovcc`, by its number in the encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "N2's segments, bounds checks and memo probes use it"
    )
)]
pub(crate) enum Condition {
    Below = 0x2,
    AboveOrEqual = 0x3,
    Equal = 0x4,
    NotEqual = 0x5,
    Less = 0xc,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Label(u32);

/// Whether an instruction works on 32 or 64 bits. A 32-bit write zeroes the upper half.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Width {
    W32,
    W64,
}

pub(crate) struct Assembler {
    bytes: Vec<u8>,
    labels: Vec<Option<usize>>,
    // The offset of each rel32 to patch, and the label it jumps to.
    fixups: Vec<(usize, Label)>,
}

impl Assembler {
    pub(crate) fn new() -> Assembler {
        Assembler {
            bytes: Vec::new(),
            labels: Vec::new(),
            fixups: Vec::new(),
        }
    }

    pub(crate) fn label(&mut self) -> Label {
        self.labels.push(None);
        Label(self.labels.len() as u32 - 1)
    }

    /// Places a label at the next instruction.
    pub(crate) fn bind(&mut self, label: Label) {
        let place = &mut self.labels[label.0 as usize];
        assert!(place.is_none(), "a label bound twice");
        *place = Some(self.bytes.len());
    }

    /// The code, with every jump patched; a jump to a label never bound panics.
    pub(crate) fn finish(mut self) -> Vec<u8> {
        for (at, label) in self.fixups {
            let target = self.labels[label.0 as usize].expect("a jump to a label never bound");
            let relative = target as i64 - (at as i64 + 4);
            let relative = i32::try_from(relative).expect("a jump beyond 2 GiB");
            self.bytes[at..at + 4].copy_from_slice(&relative.to_le_bytes());
        }
        self.bytes
    }

    // --- moves ---

    /// `mov to, from`.
    pub(crate) fn mov(&mut self, width: Width, to: Gpr, from: Gpr) {
        self.rex_registers(width, from, to);
        self.bytes.push(0x89);
        self.mod_rm_registers(from, to);
    }

    /// `mov to, immediate`, in the fewest bytes: a 32-bit move zero-extends.
    pub(crate) fn mov_immediate(&mut self, to: Gpr, immediate: u64) {
        let is_wide = u32::try_from(immediate).is_err();
        self.rex(is_wide, false, false, to.is_extended());
        self.bytes.push(0xb8 + to.low());
        let bytes = immediate.to_le_bytes();
        self.bytes
            .extend_from_slice(if is_wide { &bytes } else { &bytes[..4] });
    }

    /// `mov to, [memory]`.
    pub(crate) fn load(&mut self, width: Width, to: Gpr, memory: Memory) {
        self.rex_memory(width, to, memory);
        self.bytes.push(0x8b);
        self.memory_operand(to, memory);
    }

    /// `mov [memory], from`.
    pub(crate) fn store(&mut self, width: Width, memory: Memory, from: Gpr) {
        self.rex_memory(width, from, memory);
        self.bytes.push(0x89);
        self.memory_operand(from, memory);
    }

    /// `lea to, [memory]`.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "N2's segments, bounds checks and memo probes use it"
        )
    )]
    pub(crate) fn lea(&mut self, to: Gpr, memory: Memory) {
        self.rex_memory(Width::W64, to, memory);
        self.bytes.push(0x8d);
        self.memory_operand(to, memory);
    }

    /// `cmovcc to, from`: moves only if the condition holds.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "N2's segments, bounds checks and memo probes use it"
        )
    )]
    pub(crate) fn cmov(&mut self, width: Width, condition: Condition, to: Gpr, from: Gpr) {
        self.rex_registers(width, to, from);
        self.bytes
            .extend_from_slice(&[0x0f, 0x40 + condition as u8]);
        self.mod_rm_registers(to, from);
    }

    // --- arithmetic and comparisons ---

    /// `add to, immediate`.
    pub(crate) fn add_immediate(&mut self, width: Width, to: Gpr, immediate: i32) {
        self.group1(width, 0, to, immediate);
    }

    /// `sub to, immediate`.
    pub(crate) fn sub_immediate(&mut self, width: Width, to: Gpr, immediate: i32) {
        self.group1(width, 5, to, immediate);
    }

    /// `cmp left, immediate`.
    pub(crate) fn cmp_immediate(&mut self, width: Width, left: Gpr, immediate: i32) {
        self.group1(width, 7, left, immediate);
    }

    /// `cmp left, right`.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "N2's segments, bounds checks and memo probes use it"
        )
    )]
    pub(crate) fn cmp(&mut self, width: Width, left: Gpr, right: Gpr) {
        self.rex_registers(width, right, left);
        self.bytes.push(0x39);
        self.mod_rm_registers(right, left);
    }

    /// `cmp left, [memory]`.
    pub(crate) fn cmp_memory(&mut self, width: Width, left: Gpr, memory: Memory) {
        self.rex_memory(width, left, memory);
        self.bytes.push(0x3b);
        self.memory_operand(left, memory);
    }

    /// `test left, right`.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "N2's segments, bounds checks and memo probes use it"
        )
    )]
    pub(crate) fn test(&mut self, width: Width, left: Gpr, right: Gpr) {
        self.rex_registers(width, right, left);
        self.bytes.push(0x85);
        self.mod_rm_registers(right, left);
    }

    // --- control ---

    /// `jcc label`, always with a 32-bit displacement.
    pub(crate) fn jump_if(&mut self, condition: Condition, label: Label) {
        self.bytes
            .extend_from_slice(&[0x0f, 0x80 + condition as u8]);
        self.fixup(label);
    }

    /// `jmp label`, always with a 32-bit displacement.
    pub(crate) fn jump(&mut self, label: Label) {
        self.bytes.push(0xe9);
        self.fixup(label);
    }

    /// `call target`, an absolute address held in a register.
    pub(crate) fn call(&mut self, target: Gpr) {
        self.rex(false, false, false, target.is_extended());
        self.bytes.push(0xff);
        self.bytes.push(0xc0 | 2 << 3 | target.low());
    }

    pub(crate) fn push(&mut self, register: Gpr) {
        self.rex(false, false, false, register.is_extended());
        self.bytes.push(0x50 + register.low());
    }

    pub(crate) fn pop(&mut self, register: Gpr) {
        self.rex(false, false, false, register.is_extended());
        self.bytes.push(0x58 + register.low());
    }

    pub(crate) fn ret(&mut self) {
        self.bytes.push(0xc3);
    }

    // --- encoding ---

    fn fixup(&mut self, label: Label) {
        self.fixups.push((self.bytes.len(), label));
        self.bytes.extend_from_slice(&[0; 4]);
    }

    // `op r/m, imm` of group 1 (add, sub, cmp, ...), whose ModRM reg field picks the operation.
    fn group1(&mut self, width: Width, operation: u8, to: Gpr, immediate: i32) {
        self.rex(width == Width::W64, false, false, to.is_extended());
        match i8::try_from(immediate) {
            Ok(immediate) => {
                self.bytes.push(0x83);
                self.bytes.push(0xc0 | operation << 3 | to.low());
                self.bytes.push(immediate as u8);
            }
            Err(_) => {
                self.bytes.push(0x81);
                self.bytes.push(0xc0 | operation << 3 | to.low());
                self.bytes.extend_from_slice(&immediate.to_le_bytes());
            }
        }
    }

    // A REX prefix, left out when it would be 0x40.
    fn rex(&mut self, is_wide: bool, r: bool, x: bool, b: bool) {
        let rex = 0x40 | u8::from(is_wide) << 3 | u8::from(r) << 2 | u8::from(x) << 1 | u8::from(b);
        if rex != 0x40 {
            self.bytes.push(rex);
        }
    }

    fn rex_registers(&mut self, width: Width, reg: Gpr, rm: Gpr) {
        self.rex(
            width == Width::W64,
            reg.is_extended(),
            false,
            rm.is_extended(),
        );
    }

    fn rex_memory(&mut self, width: Width, reg: Gpr, memory: Memory) {
        let index = memory.index.is_some_and(|(index, _)| index.is_extended());
        self.rex(
            width == Width::W64,
            reg.is_extended(),
            index,
            memory.base.is_extended(),
        );
    }

    fn mod_rm_registers(&mut self, reg: Gpr, rm: Gpr) {
        self.bytes.push(0xc0 | reg.low() << 3 | rm.low());
    }

    // ModRM, SIB and displacement for `[memory]`, with `reg` in the ModRM reg field.
    fn memory_operand(&mut self, reg: Gpr, memory: Memory) {
        // rbp and r13 as a base with mod 00 mean "no base", so they always take a displacement.
        let mode = match (memory.displacement, memory.base.low()) {
            (0, low) if low != 5 => 0b00,
            (displacement, _) if i8::try_from(displacement).is_ok() => 0b01,
            _ => 0b10,
        };
        match memory.index {
            Some((index, scale)) => {
                self.bytes.push(mode << 6 | reg.low() << 3 | 0b100);
                self.bytes
                    .push((scale as u8) << 6 | index.low() << 3 | memory.base.low());
            }
            // rsp and r12 as a base need a SIB byte, with no index.
            None if memory.base.low() == 4 => {
                self.bytes.push(mode << 6 | reg.low() << 3 | 0b100);
                self.bytes.push(0b100 << 3 | 0b100);
            }
            None => self
                .bytes
                .push(mode << 6 | reg.low() << 3 | memory.base.low()),
        }
        match mode {
            0b01 => self.bytes.push(memory.displacement as u8),
            0b10 => self
                .bytes
                .extend_from_slice(&memory.displacement.to_le_bytes()),
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Assembler, Condition, Gpr, Memory, Scale, Width};

    type Form = (fn(&mut Assembler), &'static [u8], &'static str);

    // Each form alone: its bytes from the Intel manual's encoding tables, and the instruction in
    // Intel syntax, as GNU objdump printed it for those bytes when they were checked. The cases
    // cover the REX bits, the 8- and 32-bit immediates, and the bases that need a SIB byte (rsp,
    // r12) or a displacement (rbp, r13).
    const FORMS: &[Form] = &[
        (
            |a| a.mov(Width::W64, Gpr::Rax, Gpr::Rdi),
            &[0x48, 0x89, 0xf8],
            "mov rax,rdi",
        ),
        (
            |a| a.mov(Width::W32, Gpr::R9, Gpr::Rcx),
            &[0x41, 0x89, 0xc9],
            "mov r9d,ecx",
        ),
        (
            |a| a.mov(Width::W64, Gpr::Rbx, Gpr::R12),
            &[0x4c, 0x89, 0xe3],
            "mov rbx,r12",
        ),
        (
            |a| a.mov_immediate(Gpr::Rax, 7),
            &[0xb8, 7, 0, 0, 0],
            "mov eax,0x7",
        ),
        (
            |a| a.mov_immediate(Gpr::R11, 0x1234_5678_9abc),
            &[0x49, 0xbb, 0xbc, 0x9a, 0x78, 0x56, 0x34, 0x12, 0, 0],
            "movabs r11,0x123456789abc",
        ),
        (
            |a| a.load(Width::W64, Gpr::Rax, Memory::at(Gpr::Rdi, 0)),
            &[0x48, 0x8b, 0x07],
            "mov rax,QWORD PTR [rdi]",
        ),
        (
            |a| a.load(Width::W64, Gpr::Rax, Memory::at(Gpr::Rbp, 0)),
            &[0x48, 0x8b, 0x45, 0x00],
            "mov rax,QWORD PTR [rbp+0x0]",
        ),
        (
            |a| a.load(Width::W64, Gpr::R13, Memory::at(Gpr::R13, 0)),
            &[0x4d, 0x8b, 0x6d, 0x00],
            "mov r13,QWORD PTR [r13+0x0]",
        ),
        (
            |a| a.load(Width::W64, Gpr::Rcx, Memory::at(Gpr::Rsp, 8)),
            &[0x48, 0x8b, 0x4c, 0x24, 0x08],
            "mov rcx,QWORD PTR [rsp+0x8]",
        ),
        (
            |a| a.load(Width::W64, Gpr::Rcx, Memory::at(Gpr::R12, -8)),
            &[0x49, 0x8b, 0x4c, 0x24, 0xf8],
            "mov rcx,QWORD PTR [r12-0x8]",
        ),
        (
            |a| a.load(Width::W32, Gpr::Rdx, Memory::at(Gpr::Rsi, 0x200)),
            &[0x8b, 0x96, 0x00, 0x02, 0x00, 0x00],
            "mov edx,DWORD PTR [rsi+0x200]",
        ),
        (
            |a| {
                a.load(
                    Width::W32,
                    Gpr::Rax,
                    Memory::indexed(Gpr::Rbx, Gpr::Rcx, Scale::Four, 0),
                )
            },
            &[0x8b, 0x04, 0x8b],
            "mov eax,DWORD PTR [rbx+rcx*4]",
        ),
        (
            |a| {
                a.load(
                    Width::W32,
                    Gpr::R8,
                    Memory::indexed(Gpr::R13, Gpr::R9, Scale::Eight, 16),
                )
            },
            &[0x47, 0x8b, 0x44, 0xcd, 0x10],
            "mov r8d,DWORD PTR [r13+r9*8+0x10]",
        ),
        (
            |a| {
                a.load(
                    Width::W64,
                    Gpr::Rax,
                    Memory::indexed(Gpr::Rsp, Gpr::Rbp, Scale::One, 0),
                )
            },
            &[0x48, 0x8b, 0x04, 0x2c],
            "mov rax,QWORD PTR [rsp+rbp*1]",
        ),
        (
            |a| a.store(Width::W64, Memory::at(Gpr::Rsp, 16), Gpr::Rax),
            &[0x48, 0x89, 0x44, 0x24, 0x10],
            "mov QWORD PTR [rsp+0x10],rax",
        ),
        (
            |a| a.store(Width::W32, Memory::at(Gpr::R14, -4), Gpr::R15),
            &[0x45, 0x89, 0x7e, 0xfc],
            "mov DWORD PTR [r14-0x4],r15d",
        ),
        (
            |a| a.lea(Gpr::Rax, Memory::at(Gpr::Rdi, 1)),
            &[0x48, 0x8d, 0x47, 0x01],
            "lea rax,[rdi+0x1]",
        ),
        (
            |a| a.cmov(Width::W32, Condition::Equal, Gpr::Rax, Gpr::Rcx),
            &[0x0f, 0x44, 0xc1],
            "cmove eax,ecx",
        ),
        (
            |a| a.cmov(Width::W32, Condition::Below, Gpr::Rdx, Gpr::R9),
            &[0x41, 0x0f, 0x42, 0xd1],
            "cmovb edx,r9d",
        ),
        (
            |a| a.cmov(Width::W64, Condition::Less, Gpr::R10, Gpr::Rbx),
            &[0x4c, 0x0f, 0x4c, 0xd3],
            "cmovl r10,rbx",
        ),
        (
            |a| a.add_immediate(Width::W64, Gpr::Rsp, 8),
            &[0x48, 0x83, 0xc4, 0x08],
            "add rsp,0x8",
        ),
        (
            |a| a.sub_immediate(Width::W64, Gpr::Rsp, 0x1000),
            &[0x48, 0x81, 0xec, 0x00, 0x10, 0x00, 0x00],
            "sub rsp,0x1000",
        ),
        (
            |a| a.cmp_immediate(Width::W32, Gpr::Rax, 1),
            &[0x83, 0xf8, 0x01],
            "cmp eax,0x1",
        ),
        (
            |a| a.cmp_immediate(Width::W32, Gpr::R8, -200),
            &[0x41, 0x81, 0xf8, 0x38, 0xff, 0xff, 0xff],
            "cmp r8d,0xffffff38",
        ),
        (
            |a| a.cmp(Width::W32, Gpr::Rax, Gpr::Rcx),
            &[0x39, 0xc8],
            "cmp eax,ecx",
        ),
        (
            |a| a.cmp(Width::W64, Gpr::R8, Gpr::Rdx),
            &[0x49, 0x39, 0xd0],
            "cmp r8,rdx",
        ),
        (
            |a| a.cmp_memory(Width::W32, Gpr::Rax, Memory::at(Gpr::Rdi, 4)),
            &[0x3b, 0x47, 0x04],
            "cmp eax,DWORD PTR [rdi+0x4]",
        ),
        (
            |a| a.test(Width::W32, Gpr::Rax, Gpr::Rax),
            &[0x85, 0xc0],
            "test eax,eax",
        ),
        (|a| a.call(Gpr::Rax), &[0xff, 0xd0], "call rax"),
        (|a| a.call(Gpr::R11), &[0x41, 0xff, 0xd3], "call r11"),
        (|a| a.push(Gpr::Rbx), &[0x53], "push rbx"),
        (|a| a.push(Gpr::R15), &[0x41, 0x57], "push r15"),
        (|a| a.pop(Gpr::Rbp), &[0x5d], "pop rbp"),
        (|a| a.pop(Gpr::R12), &[0x41, 0x5c], "pop r12"),
        (|a| a.ret(), &[0xc3], "ret"),
    ];

    fn encode(form: fn(&mut Assembler)) -> Vec<u8> {
        let mut assembler = Assembler::new();
        form(&mut assembler);
        assembler.finish()
    }

    #[test]
    fn encodes_each_form() {
        for (form, bytes, text) in FORMS {
            assert_eq!(&encode(*form), bytes, "{text}");
        }
    }

    #[test]
    fn patches_jumps_forward_and_back() {
        let mut assembler = Assembler::new();
        let start = assembler.label();
        let end = assembler.label();
        assembler.bind(start);
        assembler.jump_if(Condition::Equal, end);
        assembler.jump(start);
        assembler.bind(end);
        assembler.ret();
        assert_eq!(
            assembler.finish(),
            [
                // je +5, past the jmp
                0x0f, 0x84, 0x05, 0x00, 0x00, 0x00, // jmp -11, to the je
                0xe9, 0xf5, 0xff, 0xff, 0xff, 0xc3,
            ]
        );
    }

    #[test]
    #[should_panic(expected = "a jump to a label never bound")]
    fn refuses_a_jump_to_a_label_never_bound() {
        let mut assembler = Assembler::new();
        let nowhere = assembler.label();
        assembler.jump(nowhere);
        assembler.finish();
    }
}
