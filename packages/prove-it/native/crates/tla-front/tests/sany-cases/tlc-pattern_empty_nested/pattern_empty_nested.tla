---- MODULE pattern_empty_nested ----
Test == \A <<>> \in {<<1>>} : \A <<>> \in {<<2>>} : TRUE
ASSUME Test
====
