---- MODULE M ----
EXTENDS Integers, TLC

ASSUME Print(11, TRUE) + Print(22, <<1>>)
====
