---- MODULE M ----
EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLE x
D0(a) == a = a
D1(a) == D0(a) /\ D0(a)
D2(a) == D1(a) /\ D1(a)
D3(a) == D2(a) /\ D2(a)
D4(a) == D3(a) /\ D3(a)
D5(a) == D4(a) /\ D4(a)
D6(a) == D5(a) /\ D5(a)
D7(a) == D6(a) /\ D6(a)
D8(a) == D7(a) /\ D7(a)
D9(a) == D8(a) /\ D8(a)
D10(a) == D9(a) /\ D9(a)
D11(a) == D10(a) /\ D10(a)
D12(a) == D11(a) /\ D11(a)
D13(a) == D12(a) /\ D12(a)
D14(a) == D13(a) /\ D13(a)
D15(a) == D14(a) /\ D14(a)
D16(a) == D15(a) /\ D15(a)
S == D16(1) /\ TLCSet(1, 2)
Inv == TLCGet(1) = 2
Init == x = 0
Next == x' = x
====
