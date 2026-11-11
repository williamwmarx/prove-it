---- MODULE JsonFraction ----
EXTENDS Naturals, Json
VARIABLE x
ASSUME JsonDeserialize("JsonFraction.json") = <<1, 1>>
Init == x = 0
Next == x' = x
====
