const t0 = performance.now();
const { dlopen, FFIType } = await import("bun:ffi");
const lib = dlopen(new URL("./napi_cost.node", import.meta.url).pathname, {
  ffi_add: { args: [FFIType.i32, FFIType.i32], returns: FFIType.i32 },
});
const t1 = performance.now();
lib.symbols.ffi_add(1, 2);
console.log(
  `bun:ffi dlopen ${(t1 - t0).toFixed(2)} ms, first call ${(performance.now() - t1).toFixed(3)} ms`,
);
