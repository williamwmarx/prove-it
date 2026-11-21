These full-output fixtures use TLC commit `d8fb231de4e4b5d02c1b2ed1ac759c086f694021`
and JDK 21.0.13+9. The Java sources beside the real class files document the probes;
the Rust tests do not execute javac or the JVM.

`scoped-packaged` and `indexed-scoped` retain declines while the configuration/Java
replacement phase of AnySet!ANY is unproved. `opaque-print` retains the static-initializer
decline. `opaque-plain-print` forces the complete-context origin check to revoke the new
alias graph before startup: its TLA ANY body must never print SHOULD_NOT_RUN.
`unused-literal` retains a prior matching result under the same unrelated Foo.class.

For workers 1 and 4, run in a fresh copy of each fixture directory:

```
java -XX:+UseParallelGC -cp "$TLA2TOOLS_JAR" tlc2.TLC -workers "$workers" -nowarning -fp 0 -seed 4 -lncheck final -noGenerateSpecTE -config M.cfg M.tla
```

Concatenate stdout and stderr, remove only `any_origin.rs`'s VARYING prefixes, trim the
end, and add one newline to tlc-1.txt or tlc-4.txt. The exit code is in exit. Full Jar
outputs remain recorded even where the native checker declines.
