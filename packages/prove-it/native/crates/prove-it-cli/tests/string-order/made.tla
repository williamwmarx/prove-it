---- MODULE Stop ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Lit == "lit"
Init == x = 0
Next == x' = x
ASSUME PrintT({"q" \o "0fresh", "=" \o "===", "N" \o "at", "-" \o "-unknown--", "L" \o "AMBDA", "$" \o "$InAssume", "U" \o "nnamedAction", "e" \o "xit", "al" \o "l", "al" \o "l:named", "m" \o "ode", "c" \o "onstraints", "l" \o "evel", "s" \o "tats", "l" \o "evelvariance", "b" \o "eginLine", "b" \o "eginColumn", "e" \o "ndLine", "e" \o "ndColumn", "m" \o "odule", "n" \o "ame", "l" \o "ocation", "c" \o "ontext", "p" \o "arameters", "_" \o "action", "" \o "a", "B" \o "OOLEAN", "N" \o "_ActDecl", "I" \o "nit", "A" \o "ppend", "l" \o "it", "d" \o "uration", "c" \o "ounterexample", "v" \o "ars", "S" \o "tate", "z" \o "q"})
====
