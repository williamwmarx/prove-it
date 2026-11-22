---- MODULE IsaRules ----
EXTENDS TLAPS
THEOREM Fast == ASSUME NEW P(_), \A x : P(x) PROVE P(1)
  BY IsaM("fast")
THEOREM Rule == ASSUME NEW P(_), NEW x, P(x) PROVE P(CHOOSE a : P(a))
  BY IsaM("(rule chooseI)")
THEOREM SimpAdd == ASSUME NEW S PROVE (S = {}) <=> (\A x : x \notin S)
  BY IsaM("(simp add: emptysetIffEmpty)")
THEOREM AutoSimp == ASSUME NEW S PROVE (S = {}) <=> (\A x : x \notin S)
  BY IsaM("(auto simp: emptysetIffEmpty)")
THEOREM Plain == ASSUME NEW S PROVE (S = {}) <=> (\A x : x \notin S)
  BY IsaM("simp")
====
