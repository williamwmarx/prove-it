---------------------------- MODULE FiniteSets -----------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
IsFiniteSet(S) ==
  \E seq \in Seq(S) : \A s \in S : \E n \in 1..Len(seq) : seq[n] = s
Cardinality(S) ==
  LET CS[T \in SUBSET S] == IF T = {} THEN 0
                                      ELSE 1 + CS[T \ {CHOOSE x : x \in T}]
  IN  CS[S]
=============================================================================
