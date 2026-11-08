// The TypeScript FP64 of the sample state in src/fp.rs, which must print the same fingerprint.
import { getTlcFingerprint } from "/home/user/prove-it/packages/prove-it/src/tlc/fingerprint";
import {
  createRecord,
  createSet,
  createTuple,
} from "/home/user/prove-it/packages/prove-it/src/values";

const sample = [
  7,
  -2147483648,
  "hello",
  true,
  createSet([1, 2, 3]),
  createRecord([
    ["a", 1],
    ["b", "x"],
  ]),
  createTuple(["p", "q"]),
];
console.log(`sample fingerprint ${BigInt.asIntN(64, getTlcFingerprint(sample))}`);
const startedAt = performance.now();
let sink = 0n;
for (let state = 0; state < 1_000_000; state++) {
  const values = [0, 1, 2, 3, 4].map((variable) => Math.imul(state, variable + 1) & 1023);
  sink ^= getTlcFingerprint(values);
}
console.log(
  `ts fp64: 1M states of 5 ints in ${(performance.now() - startedAt).toFixed(1)} ms, sink ${BigInt.asIntN(64, sink)}`,
);
