---- MODULE CaseSplit ----
EXTENDS TLAPS
THEOREM TRUE
<1>. DEFINE P(T) == T # {}
<1>1. ASSUME NEW T, P(T) PROVE T = T
  <2>1. CASE T = {}  OMITTED
  <2>2. CASE ~(T = {})  OMITTED
  <2>. QED  BY <2>1, <2>2, PTL
<1>. QED  OBVIOUS
====
