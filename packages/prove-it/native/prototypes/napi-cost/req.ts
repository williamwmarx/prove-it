const t0 = performance.now();
const { createRequire } = await import("node:module");
const t1 = performance.now();
createRequire(import.meta.url)("./napi_cost.node");
const t2 = performance.now();
console.log(
  `import node:module ${(t1 - t0).toFixed(2)} ms, require .node ${(t2 - t1).toFixed(2)} ms`,
);
