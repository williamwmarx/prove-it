---- MODULE M ----
EXTENDS Integers, TLC

Test == TRUE + <<1>>
ASSUME Test
====
