---- MODULE PcalGuard ----
EXTENDS Naturals
CONSTANT N
(* --algorithm PcalGuard
variable lock = 0;
fair process P \in 1..N
begin
  a: while TRUE do
       await lock = 0;
       lock := self;
  b:   lock := 0;
     end while;
end process
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES pc, lock

vars == << pc, lock >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ lock = 0
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ lock = 0
           /\ lock' = self
           /\ pc' = [pc EXCEPT ![self] = "b"]

b(self) == /\ pc[self] = "b"
           /\ lock' = 0
           /\ pc' = [pc EXCEPT ![self] = "a"]

P(self) == a(self) \/ b(self)

Next == (\E self \in 1..N: P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(P(self))

\* END TRANSLATION
Always == TRUE
Live == \A p \in 1..N : []<>(pc[p] = "b")
Some == []<>(\E p \in 1..N : pc[p] = "b")
====
