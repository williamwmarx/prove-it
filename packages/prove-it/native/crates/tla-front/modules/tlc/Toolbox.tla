----------------------------- MODULE Toolbox --------------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE TLC
-----------------------------------------------------------------------------
_TETrace ==
    CHOOSE f \in [ (Nat \ {0}) -> STRING ] : TRUE
LOCAL _TETraceLength == Cardinality(DOMAIN _TETrace)
_TEPosition ==
    IF TLCGet("level") >= _TETraceLength
       THEN _TETraceLength
       ELSE IF TLCGet("level") = 0 THEN 1 ELSE TLCGet("level")
=============================================================================
