---- MODULE M ----
EXTENDS Integers, TLC, FiniteSets
VARIABLE x
Test == PrintT([a : {1}] \cap {30, 2, 28, 18, 17, 31, 29, 4, 12, 1, 6, 25, 9, 24, 20, 13, "s", 3, 10, 22, 19, 15, 16, 5, 27, 8, 7, 26, 21, 23, 11, 14})
ASSUME Test
Init == x = 0
Next == UNCHANGED x
====
