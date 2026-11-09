----------------------------- MODULE Bags --------------------------------
LOCAL INSTANCE Naturals
IsABag(B) ==
  B \in [DOMAIN B -> {n \in Nat : n > 0}]
BagToSet(B) == DOMAIN B
SetToBag(S) == [e \in S |-> 1]
BagIn(e,B) == e \in BagToSet(B)
EmptyBag == SetToBag({})
B1 (+) B2  ==
  [e \in (DOMAIN B1) \cup (DOMAIN B2) |->
      (IF e \in DOMAIN B1 THEN B1[e] ELSE 0)
    + (IF e \in DOMAIN B2 THEN B2[e] ELSE 0) ]
B1 (-) B2  ==
  LET B == [e \in DOMAIN B1 |-> IF e \in DOMAIN B2 THEN B1[e] - B2[e]
                                                   ELSE B1[e]]
  IN  [e \in {d \in DOMAIN B : B[d] > 0} |-> B[e]]
LOCAL Sum(f) ==
        LET DSum[S \in SUBSET DOMAIN f] ==
               LET elt == CHOOSE e \in S : TRUE
               IN  IF S = {} THEN 0
                             ELSE f[elt] + DSum[S \ {elt}]
        IN  DSum[DOMAIN f]
BagUnion(S) ==
  [e \in UNION {BagToSet(B) : B \in S} |->
    Sum( [B \in S |-> IF BagIn(e, B) THEN B[e] ELSE 0] ) ]
B1 \sqsubseteq B2  ==
  /\ (DOMAIN B1) \subseteq (DOMAIN B2)
  /\ \A e \in DOMAIN B1 : B1[e] \leq B2[e]
SubBag(B) ==
  LET RemoveFromDom(x, f) == [y \in (DOMAIN f) \ {x} |-> f[y]]
      Combine(x, BagSet) ==
         BagSet \cup
          {[y \in (DOMAIN f) \cup {x} |-> IF y = x THEN i ELSE f[y]] :
                f \in BagSet, i \in 1..B[x]}
      Biggest == LET Range == {B[x] : x \in DOMAIN B}
                 IN  IF Range = {} THEN 0
                                   ELSE CHOOSE r \in Range :
                                           \A s \in Range : r \geq s
      RSB[BB \in UNION {[S -> 1..Biggest] : S \in SUBSET DOMAIN B}] ==
        IF BB = << >> THEN {<< >>}
                      ELSE LET x == CHOOSE x \in DOMAIN BB : TRUE
                           IN  Combine(x, RSB[RemoveFromDom(x, BB)])
  IN RSB[B]
BagOfAll(F(_), B) ==
  [e \in {F(d) : d \in BagToSet(B)} |->
     Sum( [d \in BagToSet(B) |-> IF F(d) = e THEN B[d] ELSE 0] ) ]
BagCardinality(B) ==
  Sum(B)
CopiesIn(e, B) ==
  IF BagIn(e, B) THEN B[e] ELSE 0
=============================================================================
 6 Apr 99 : Modified version for standard module set
 7 Dec 98 : Corrected error found by Stephan Merz.
 6 Dec 98 : Modified comments based on suggestions by Lyle Ramshaw.
 5 Dec 98 : Initial version.
