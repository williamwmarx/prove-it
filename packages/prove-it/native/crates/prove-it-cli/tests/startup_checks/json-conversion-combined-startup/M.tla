---- MODULE M ----
EXTENDS Integers,TLC,Json
VARIABLE x
ASSUME ToJson(<<3,2,1>>) = "[3,2,1]"
ASSUME ToJson({3,2,1}) = "[1,2,3]"
ASSUME ToJsonObject([a |-> TRUE,b |-> FALSE]) = "{\"a\":true,\"b\":false}"
ASSUME ToJson(3 :> "c" @@ 2 :> "b" @@ 1 :> "a") = "[\"a\",\"b\",\"c\"]"
ASSUME ToJson([n \in {3,2,1} |-> 2*n+1]) = "[3,5,7]"
ASSUME ToJsonArray({}) = "[]"
Init == x = 0
Next == x' = x
====
