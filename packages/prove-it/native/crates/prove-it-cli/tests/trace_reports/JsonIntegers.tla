---- MODULE JsonIntegers ----
EXTENDS Integers, Json
VARIABLE x
ASSUME JsonDeserialize("JsonIntegers.json") = <<1, -2, 0, 0, 2147483647, -2147483647 - 1>>
Init == x = 0
Next == x' = x
====
