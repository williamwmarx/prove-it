const t0 = performance.now();
const m = { exports: {} };
process.dlopen(m, new URL("./napi_cost.node", import.meta.url).pathname);
const t1 = performance.now();
m.exports.add(1, 2);
const t2 = performance.now();
console.log(`dlopen ${(t1 - t0).toFixed(2)} ms, first call ${(t2 - t1).toFixed(3)} ms`);
