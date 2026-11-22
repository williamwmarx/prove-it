---- MODULE IsabelleMethods ----
EXTENDS TLAPS
THEOREM ASSUME NEW P, NEW Q, P /\ Q PROVE Q /\ P
  BY IsaM("simp")
THEOREM ASSUME NEW S, NEW T, \A x : x \in S <=> x \in T PROVE S = T
  BY IsaWithSetExtensionality
THEOREM ASSUME NEW S, NEW T, \A x : x \in S <=> x \in T PROVE S = T
  BY AllIsa
====
