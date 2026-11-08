// Three ways to run a compiled invariant on interned ids, timed on the same states:
//   MutualExclusion == \A i, j \in 1..N : i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")
// a tree of boxed closures (compile.ts's design, in Rust), a register-free stack bytecode loop, and
// the native code a code generator such as Cranelift would aim at.
use std::time::Instant;

type Id = i32;
const TRUE: Id = 1;
const FALSE: Id = 0;
const N: i32 = 12;
const CS: Id = 77;

pub struct Ctx<'a> { pub cur: &'a [Id], pub locals: [Id; 8] }

#[derive(Debug)]
pub struct Bail;

type Eval = Box<dyn Fn(&mut Ctx) -> Result<Id, Bail>>;

fn int_id(i: i32) -> Id { 1000 + i }
fn int_of(id: Id) -> i32 { id - 1000 }

fn closure_tree() -> Eval {
    let constant = |id: Id| -> Eval { Box::new(move |_| Ok(id)) };
    let slot = |s: usize| -> Eval { Box::new(move |c| Ok(c.locals[s])) };
    let apply_pc = |arg: Eval| -> Eval { Box::new(move |c| { let i = int_of(arg(c)?); if i < 1 || i > N { return Err(Bail); } Ok(c.cur[(i - 1) as usize]) }) };
    let eq = |a: Eval, b: Eval| -> Eval { Box::new(move |c| Ok(if a(c)? == b(c)? { TRUE } else { FALSE })) };
    let neq = |a: Eval, b: Eval| -> Eval { Box::new(move |c| Ok(if a(c)? != b(c)? { TRUE } else { FALSE })) };
    let and = |a: Eval, b: Eval| -> Eval { Box::new(move |c| { let x = a(c)?; if x == FALSE { return Ok(FALSE); } if x != TRUE { return Err(Bail); } let y = b(c)?; if y != TRUE && y != FALSE { return Err(Bail); } Ok(y) }) };
    let not = |a: Eval| -> Eval { Box::new(move |c| { let x = a(c)?; if x == TRUE { Ok(FALSE) } else if x == FALSE { Ok(TRUE) } else { Err(Bail) } }) };
    let implies = |a: Eval, b: Eval| -> Eval { Box::new(move |c| { let x = a(c)?; if x == FALSE { return Ok(TRUE); } if x != TRUE { return Err(Bail); } b(c) }) };
    let forall = |s: usize, body: Eval| -> Eval { Box::new(move |c| { for i in 1..=N { c.locals[s] = int_id(i); let v = body(c)?; if v == FALSE { return Ok(FALSE); } if v != TRUE { return Err(Bail); } } Ok(TRUE) }) };
    let body = implies(
        neq(slot(0), slot(1)),
        not(and(eq(apply_pc(slot(0)), constant(CS)), eq(apply_pc(slot(1)), constant(CS)))),
    );
    forall(0, forall(1, body))
}

#[derive(Clone, Copy)]
enum Op { Slot(u8), Const(Id), ApplyCur, Eq, Neq, Not, AndJump(u16), Check, ImpliesJump(u16), ForallStart(u8, i32), ForallNext(u8, u16, i32), Return }

// A stack machine for the hand-assembled program below.
fn run_bytecode(code: &[Op], c: &mut Ctx) -> Result<Id, Bail> {
    let mut stack = [0 as Id; 16];
    let mut top = 0usize;
    let mut pc = 0usize;
    loop {
        match code[pc] {
            Op::Slot(s) => { stack[top] = c.locals[s as usize]; top += 1; }
            Op::Const(id) => { stack[top] = id; top += 1; }
            Op::ApplyCur => { let i = int_of(stack[top - 1]); if i < 1 || i > N { return Err(Bail); } stack[top - 1] = c.cur[(i - 1) as usize]; }
            Op::Eq => { top -= 1; stack[top - 1] = (stack[top - 1] == stack[top]) as Id; }
            Op::Neq => { top -= 1; stack[top - 1] = (stack[top - 1] != stack[top]) as Id; }
            Op::Not => { let x = stack[top - 1]; if x != TRUE && x != FALSE { return Err(Bail); } stack[top - 1] = 1 - x; }
            Op::Check => { let x = stack[top - 1]; if x != TRUE && x != FALSE { return Err(Bail); } }
            Op::AndJump(target) => { let x = stack[top - 1]; if x == FALSE { pc = target as usize; continue; } if x != TRUE { return Err(Bail); } top -= 1; }
            Op::ImpliesJump(target) => { let x = stack[top - 1]; if x == FALSE { stack[top - 1] = TRUE; pc = target as usize; continue; } if x != TRUE { return Err(Bail); } top -= 1; }
            Op::ForallStart(s, low) => { c.locals[s as usize] = int_id(low); }
            Op::ForallNext(s, body, high) => {
                let x = stack[top - 1]; top -= 1;
                if x == FALSE { stack[top] = FALSE; top += 1; pc = pc + 1; continue; }
                if x != TRUE { return Err(Bail); }
                let i = int_of(c.locals[s as usize]) + 1;
                if i <= high { c.locals[s as usize] = int_id(i); pc = body as usize; continue; }
                stack[top] = TRUE; top += 1;
            }
            Op::Return => return Ok(stack[top - 1]),
        }
        pc += 1;
    }
}

fn program() -> Vec<Op> {
    use Op::*;
    // 0 ForallStart i; 1 ForallStart j; 2..: body leaves a boolean; ForallNext j loops to 2, then
    // the inner result feeds ForallNext i, which restarts j at 1.
    vec![
        ForallStart(0, 1),            // 0
        ForallStart(1, 1),            // 1
        Slot(0), Slot(1), Neq,        // 2 3 4
        ImpliesJump(16),              // 5
        Slot(0), ApplyCur, Const(CS), Eq, // 6 7 8 9
        AndJump(15),                  // 10
        Slot(1), ApplyCur, Const(CS), Eq, // 11 12 13 14
        Not,                          // 15
        ForallNext(1, 2, N),          // 16
        ForallNext(0, 1, N),          // 17 (restarts j through ForallStart at 1)
        Return,                       // 18
    ]
}

// The same tree with the fused nodes a compiler picks by pattern: pc[i] = "cs" as one node that
// reads the variable's element and compares it with a constant, i # j over two slots, and a \A
// over an interval that tests its body's boolean itself.
fn fused_tree() -> Eval {
    let eq_apply_const = |s: usize, k: Id| -> Eval { Box::new(move |c| { let i = int_of(c.locals[s]); if i < 1 || i > N { return Err(Bail); } Ok((c.cur[(i - 1) as usize] == k) as Id) }) };
    let not_and = |a: Eval, b: Eval| -> Eval { Box::new(move |c| { let x = a(c)?; if x == FALSE { return Ok(TRUE); } let y = b(c)?; Ok(1 - y) }) };
    let implies_neq_slots = |s: usize, t: usize, b: Eval| -> Eval { Box::new(move |c| if c.locals[s] == c.locals[t] { Ok(TRUE) } else { b(c) }) };
    let forall_interval = |s: usize, low: i32, high: i32, body: Eval| -> Eval { Box::new(move |c| { for i in low..=high { c.locals[s] = int_id(i); match body(c)? { TRUE => {}, FALSE => return Ok(FALSE), _ => return Err(Bail) } } Ok(TRUE) }) };
    forall_interval(0, 1, N, forall_interval(1, 1, N, implies_neq_slots(0, 1, not_and(eq_apply_const(0, CS), eq_apply_const(1, CS)))))
}

fn native(c: &mut Ctx) -> Result<Id, Bail> {
    for i in 1..=N {
        for j in 1..=N {
            if i != j && c.cur[(i - 1) as usize] == CS && c.cur[(j - 1) as usize] == CS { return Ok(FALSE); }
        }
    }
    Ok(TRUE)
}

pub fn bench() {
    // States in which at most one process is in its critical section, so the invariant holds and
    // every evaluation runs all N * N cases.
    let states: Vec<Vec<Id>> = (0..4096).map(|s| (0..N).map(|p| if (s % (N + 3)) == p { CS } else { 50 + ((s * 7 + p) % 5) }).collect()).collect();
    let tree = closure_tree();
    let code = program();
    let fused = fused_tree();
    let rounds = 200;
    let time = |label: &str, f: &mut dyn FnMut(&mut Ctx) -> Result<Id, Bail>| {
        let started = Instant::now();
        let mut holds = 0u64;
        for _ in 0..rounds {
            for state in &states {
                let mut c = Ctx { cur: state, locals: [0; 8] };
                if f(&mut c).unwrap() == TRUE { holds += 1; }
            }
        }
        let ns = started.elapsed().as_secs_f64() * 1e9 / (rounds * states.len()) as f64;
        println!("{label:<34} {ns:>8.1} ns/evaluation ({holds} held)");
    };
    time("closure tree (Box<dyn Fn>)", &mut |c| tree(c));
    time("fused closure tree", &mut |c| fused(c));
    time("bytecode loop", &mut |c| run_bytecode(&code, c));
    time("native (codegen ceiling)", &mut |c| native(c));
}
