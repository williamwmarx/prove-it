---- MODULE IsabelleMethods ----
EXTENDS TLAPS
THEOREM ASSUME NEW P, NEW Q, P /\ Q PROVE Q /\ P
  BY IsaM("simp")
THEOREM ASSUME NEW P, NEW Q, P /\ Q PROVE Q /\ P
  BY IsaM("(simp)")
THEOREM ASSUME NEW P, NEW Q, P /\ Q PROVE Q /\ P
  BY IsaM("(simp, auto)")
THEOREM ASSUME NEW P(_), NEW a, P(a) PROVE \E x : P(x) /\ TRUE
  BY IsaM("(simp, auto)")
THEOREM ASSUME NEW P(_), NEW a, P(a) /\ TRUE PROVE \E x : P(x)
  BY IsaM("(simp, auto)")
THEOREM ASSUME NEW S, NEW T, \A x : x \in S <=> x \in T PROVE S = T
  BY IsaWithSetExtensionality
THEOREM ASSUME NEW S, NEW T, \A x : x \in S <=> x \in T PROVE S = T
  BY AllIsa
====
