These startup fixtures were recorded from TLC commit
`d8fb231de4e4b5d02c1b2ed1ac759c086f694021`, with JDK 21.0.13+9.
`any.rs` compares the complete output at one and four workers for fourteen models:
membership, printing, finiteness, function sets and domains, duplicate-set normalization,
container equality, initial-state fingerprints, isEmpty, nonenumerable quantification,
permutations and random draws. The recorded exceptional output remains the Jar's output.

For each fixture, copy its `.tla` and `.cfg` to `M.tla` and `M.cfg` in a temporary
directory. Run, for workers 1 and 4:

```
java -XX:+UseParallelGC -cp "$TLA2TOOLS_JAR" tlc2.TLC -workers "$workers" -nowarning -fp 0 -seed 4 -lncheck final -noGenerateSpecTE -config M.cfg M.tla
```

Record the exit code in `.exit`. Concatenate stdout and stderr, remove only lines
with the prefixes in `any.rs`'s `VARYING`, trim trailing whitespace at the end, and
write one final newline to `.tlc-1.txt` or `.tlc-4.txt`. Do not replace the Jar's
exceptional output with a native decline.
