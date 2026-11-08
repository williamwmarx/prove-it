// Times calls across N-API (both runtimes) and bun:ffi (Bun only).
import { createRequire } from "node:module";
const require = createRequire(import.meta.url);
const t0 = performance.now();
const native = require("./napi_cost.node");
const loadMs = performance.now() - t0;
const isBun = typeof Bun !== "undefined";
const time = (label, n, body) => {
  for (let i = 0; i < Math.min(n, 100000); i++) body(i); // warm up
  const start = performance.now();
  let sink = 0;
  for (let i = 0; i < n; i++) sink = (sink + body(i)) | 0;
  const ns = ((performance.now() - start) * 1e6) / n;
  console.log(`${label.padEnd(44)} ${ns.toFixed(1).padStart(8)} ns/call  (sink ${sink & 1})`);
};
console.log(
  `${isBun ? "bun " + Bun.version : "node " + process.version}: load ${loadMs.toFixed(2)} ms`,
);
const jsAdd = (a, b) => (a + b) | 0;
time("JS function add", 10_000_000, (i) => jsAdd(i, 1));
time("N-API noop()", 5_000_000, () => {
  native.noop();
  return 0;
});
time("N-API add(i, 1)", 5_000_000, (i) => native.add(i, 1));
for (const size of [16, 1024, 65536]) {
  const array = new Int32Array(size).fill(1);
  time(`N-API sum(Int32Array(${size})) zero-copy`, size > 1024 ? 20_000 : 2_000_000, () =>
    native.sum(array),
  );
}
{
  const n = 1_000_000;
  const start = performance.now();
  native.callBack((x) => x & 1, n);
  console.log(
    `${"N-API Rust -> JS callback".padEnd(44)} ${(((performance.now() - start) * 1e6) / n).toFixed(1).padStart(8)} ns/call`,
  );
}
if (isBun) {
  const { dlopen, FFIType, ptr } = await import("bun:ffi");
  const lib = dlopen(new URL("./napi_cost.node", import.meta.url).pathname, {
    ffi_add: { args: [FFIType.i32, FFIType.i32], returns: FFIType.i32 },
    ffi_sum: { args: [FFIType.ptr, FFIType.u64], returns: FFIType.i32 },
  });
  time("bun:ffi add(i, 1)", 10_000_000, (i) => lib.symbols.ffi_add(i, 1));
  const array = new Int32Array(1024).fill(1);
  time("bun:ffi sum(ptr(Int32Array(1024)))", 2_000_000, () =>
    lib.symbols.ffi_sum(ptr(array), 1024),
  );
}
