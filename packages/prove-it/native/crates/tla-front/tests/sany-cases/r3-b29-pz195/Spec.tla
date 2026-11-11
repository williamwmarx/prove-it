---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == \A n \in {1} : n = n
<1> DEFINE dd == op
<1>2. x = 1
  <2>1. ASSUME NEW STATE s PROVE thm!1
    <3> USE <2>a
    <3>2. thm!:
      BY lem
    <3> WITNESS dd
    <3> QED BY <3>2
  <2> DEFINE dd == [](x = 1)
  <2>3. 1 = 1
    BY <2>3!1 DEF op
  <2> DEFINE dd == op(1)
  <2> QED
<1>3. ASSUME NEW TEMPORAL t PROVE lab :: x = 1
  <2> M0 == INSTANCE Inner WITH w <- x'
  <2> QED BY <1>a
<1> QED BY <1>3
====
