---- MODULE Spec ----
EXTENDS TLAPS

---- MODULE Inner ----
VARIABLE x

A == ENABLED (x')

======================

VARIABLE x

MZz == INSTANCE Inner

THEOREM M!A
BY ExpandENABLED DEF M!A

=================================================
