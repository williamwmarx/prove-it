Real-class precedence fixtures, recorded from TLC
`d8fb231de4e4b5d02c1b2ed1ac759c086f694021` with JDK 21.0.13+9.

Each directory contains the Java source, its real class file, the TLA+ model and
configuration, and the Jar's complete output after the varying startup lines in
`any_class.rs` are removed. Directory paths become `{directory}`.

`with-any` replaces packaged TLC with a class whose Any method returns integer 7.
`without-any` replaces it with an empty class, leaving TLA Any's unbounded CHOOSE.
Both must remain native declines. `unused` uses that empty class without reading
Any and must preserve its complete successful Jar output.

To rebuild each class: `javac --release 8 -cp "$TLA2TOOLS_JAR" TLC.java`.
To record each model at workers 1 and 4, run in its own temporary directory:

```
java -XX:+UseParallelGC -cp "$TLA2TOOLS_JAR" tlc2.TLC -workers "$workers" -nowarning -fp 0 -seed 4 -lncheck final -noGenerateSpecTE -config M.cfg M.tla
```

Save the exit code, concatenate stdout and stderr, remove only the varying-line
prefixes, replace the temporary directory with `{directory}`, and append one final
newline. Retain the Jar's exceptional output rather than substituting a native decline.
