---- MODULE AnySet ----
EXTENDS TLC
ANY == Print("SHOULD_NOT_RUN", CHOOSE x: TRUE)
====
