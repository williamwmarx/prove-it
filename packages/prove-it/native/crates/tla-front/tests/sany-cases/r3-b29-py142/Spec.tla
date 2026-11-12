---- MODULE Spec ----
VARIABLE x
op == x
LEMMA lem == TRUE
THEOREM thm == [](x = 1)
<1> DEFINE dd == x \in {1}
<1>2. ASSUME NEW ACTION a PROVE lab :: x = 1
  BY <1>1 DEF op
<1>3. SUFFICES ASSUME NEW q, TRUE PROVE TRUE
  <2> TAKE p \in {1}
  <2>2. thm!2
    <3>1. lab :: x = 1
      BY <3>1 DEF op
    <3>2. TRUE
    <3>3. [](x = 1)
      BY <3>1
    <3> QED BY <3>3
  <2> USE <2>2 DEF thm
  <2> QED BY <2>2!1
<1>4. op(1)
  BY <1>7
<1> QED
====
