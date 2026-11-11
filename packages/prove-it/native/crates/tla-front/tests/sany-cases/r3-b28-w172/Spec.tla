---- MODULE Spec ----
CONSTANT c, S, F(_)
VARIABLE x, y
f[i \in {1}] == i
op1(a) == a
G(H(_)) == H(x)
M == INSTANCE Inner WITH w <- y'
D0 == ((SF_<<x, y>>(M!E) => (M!E ~> TRUE)) ~> [][[q \in {} |-> {}]]_<<x,y>>)
THEOREM T1 == (y => op1(x))
<1>1. \E q : (TRUE -+-> x)
<1>2. [][({} -+-> op1(x))]_([][f[1]]_<<x,y>>)
  BY <1>1
<1> QED BY <1>2
D2 == [][<>({1, f[1]})]_x
====
