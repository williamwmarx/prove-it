---- MODULE Stop ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Lit == "lit"
Init == x = 0
Next == x' = x
ASSUME PrintT({"z" \o "q", "S" \o "tate", "v" \o "ars", "c" \o "ounterexample", "d" \o "uration", "l" \o "it", "A" \o "ppend", "I" \o "nit", "N" \o "_ActDecl", "B" \o "OOLEAN", "" \o "a", "_" \o "action", "p" \o "arameters", "c" \o "ontext", "l" \o "ocation", "n" \o "ame", "m" \o "odule", "e" \o "ndColumn", "e" \o "ndLine", "b" \o "eginColumn", "b" \o "eginLine", "l" \o "evelvariance", "s" \o "tats", "l" \o "evel", "c" \o "onstraints", "m" \o "ode", "al" \o "l:named", "al" \o "l", "e" \o "xit", "U" \o "nnamedAction", "$" \o "$InAssume", "L" \o "AMBDA", "-" \o "-unknown--", "N" \o "at", "=" \o "===", "q" \o "0fresh"})
====
