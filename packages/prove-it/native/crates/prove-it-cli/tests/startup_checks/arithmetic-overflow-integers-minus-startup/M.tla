---- MODULE M ----
EXTENDS Integers, TLC, TLCExt, FiniteSets

Test == ((0-2147483647-1)-1)=0
ASSUME Test
====
