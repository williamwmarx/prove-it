---- MODULE Spec ----
VARIABLE x
Init == x = 0
Next == x' = x
LOCAL INSTANCE _TLCTrace
====
