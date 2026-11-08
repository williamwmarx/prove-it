// The invariant of src/eval.rs as compile.ts builds it: closures of no arguments over registers.
const TRUE = 1;
const FALSE = 0;
const N = 12;
const CS = 77;
let CUR = new Int32Array(N);
const LOC = new Int32Array(8);
const bail = () => {
  throw new Error("bail");
};
type Evaluate = () => number;
const constant =
  (id: number): Evaluate =>
  () =>
    id;
const slot =
  (index: number): Evaluate =>
  () =>
    LOC[index];
const applyPc =
  (argument: Evaluate): Evaluate =>
  () => {
    const position = argument() - 1000;
    return position >= 1 && position <= N ? CUR[position - 1] : bail();
  };
const eq =
  (left: Evaluate, right: Evaluate): Evaluate =>
  () =>
    left() === right() ? TRUE : FALSE;
const neq =
  (left: Evaluate, right: Evaluate): Evaluate =>
  () =>
    left() !== right() ? TRUE : FALSE;
const and =
  (left: Evaluate, right: Evaluate): Evaluate =>
  () => {
    const value = left();
    if (value === FALSE) return FALSE;
    if (value !== TRUE) bail();
    const other = right();
    return other === TRUE || other === FALSE ? other : bail();
  };
const not =
  (operand: Evaluate): Evaluate =>
  () => {
    const value = operand();
    return value === TRUE ? FALSE : value === FALSE ? TRUE : bail();
  };
const implies =
  (left: Evaluate, right: Evaluate): Evaluate =>
  () => {
    const value = left();
    if (value === FALSE) return TRUE;
    if (value !== TRUE) bail();
    return right();
  };
const forall =
  (index: number, body: Evaluate): Evaluate =>
  () => {
    for (let element = 1; element <= N; element++) {
      LOC[index] = 1000 + element;
      const value = body();
      if (value === FALSE) return FALSE;
      if (value !== TRUE) bail();
    }
    return TRUE;
  };
const invariant = forall(
  0,
  forall(
    1,
    implies(
      neq(slot(0), slot(1)),
      not(and(eq(applyPc(slot(0)), constant(CS)), eq(applyPc(slot(1)), constant(CS)))),
    ),
  ),
);
const states = Array.from({ length: 4096 }, (_, state) =>
  Int32Array.from({ length: N }, (_, process) =>
    state % (N + 3) === process ? CS : 50 + ((state * 7 + process) % 5),
  ),
);
for (let round = 0; round < 3; round++) {
  const startedAt = performance.now();
  let held = 0;
  for (let repeat = 0; repeat < 200; repeat++) {
    for (const state of states) {
      CUR = state;
      if (invariant() === TRUE) held++;
    }
  }
  console.log(
    `ts closure tree ${(((performance.now() - startedAt) * 1e6) / (200 * states.length)).toFixed(1)} ns/evaluation (${held} held)`,
  );
}
