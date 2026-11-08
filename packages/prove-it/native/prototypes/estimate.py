# Projects each stage's time per model from today's Depot numbers (dash/r3/suite.json) under the
# assumptions stated in design.md section 8. Prints per-model seconds and geometric means.
import json, math, sys
suite = json.load(open(sys.argv[1]))
LIVE_ENGINE = {"ReadersWriters MC": 0.049, "TokenRing": 0.097}
def fixed(r): return min(0.040, 0.8 * r["proveit_s"])
def threads(s, cores=4):
    # Level-synchronous search on 4 cores: no gain below 0.1 s of search, 2.5x from 0.5 s.
    if s <= 0.1: return 1.0
    if s >= 0.5: return 2.5
    return 1.0 + 1.5 * (s - 0.1) / 0.4
def project(r, k1):
    total, f = r["proveit_s"], fixed(r)
    name = r["model"]
    if name in LIVE_ENGINE:
        e = LIVE_ENGINE[name]; live = total - f - e
        s1 = f + 0.002 + e / k1 + live
        s2 = f + 0.002 + e / k1 / threads(e / k1) + live
        s3 = f + 0.002 + 2 * e / k1 / threads(e / k1)   # liveness on the graph costs about the search
        s4 = 0.006 + 2 * e / k1 / threads(e / k1)
    else:
        s = total - f
        s1 = f + 0.002 + s / k1
        s2 = f + 0.002 + s / k1 / threads(s / k1)
        s3 = s2
        s4 = 0.006 + s / k1 / threads(s / k1)
    return [total, s1, s2, s3, s4]
for k1 in (1.3, 1.6, 2.0):
    rows = [(r, project(r, k1)) for r in suite]
    g = lambda i: math.exp(sum(math.log(p[i]) for _, p in rows) / len(rows))
    gt = math.exp(sum(math.log(r["tlc_s"]) for r in suite) / len(suite))
    gts = math.exp(sum(math.log(r["tlats_s"]) for r in suite) / len(suite))
    print(f"single-thread engine speedup k1={k1}")
    if k1 == 1.6:
        for r, p in rows: print(f"  {r['model']:<18} " + "  ".join(f"{x:6.3f}" for x in p))
    print("  geomean s: " + "  ".join(f"{g(i):.4f}" for i in range(5)))
    print("  vs TLC 1 worker: " + "  ".join(f"{gt / g(i):.1f}x" for i in range(5)))
    print("  vs tla-ts:       " + "  ".join(f"{gts / g(i):.1f}x" for i in range(5)))
