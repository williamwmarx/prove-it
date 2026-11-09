------------------------------- MODULE TLCExt -------------------------------
LOCAL INSTANCE TLC
LOCAL INSTANCE Integers
-----------------------------------------------------------------------------
AssertEq(a, b) ==
    IF a # b THEN
        /\ PrintT("Assertion failed")
        /\ PrintT(a)
        /\ PrintT(b)
        /\ a = b
    ELSE a = b
AssertError(err, exp) ==
    LET FailsEval(e) == CHOOSE b \in BOOLEAN : TRUE
        TLCError     == CHOOSE s \in STRING  : TRUE
    IN IF FailsEval(exp) THEN Assert(err = TLCError, TLCError) ELSE TRUE
-----------------------------------------------------------------------------
TLCGetOrDefault(key, defaultVal) ==
  CHOOSE n : TRUE
TLCGetAndSet(key, Op(_,_), val, defaultVal) ==
  LET oldVal == TLCGetOrDefault(key, defaultVal)
  IN CHOOSE v \in {oldVal} : TLCSet(key, Op(oldVal, val))
-----------------------------------------------------------------------------
Trace ==
  TRUE
-----------------------------------------------------------------------------
CounterExample ==
    TRUE
ToTrace(CE) ==
	TRUE
-----------------------------------------------------------------------------
TLCModelValue(str) ==
  CHOOSE v: ToString(v) = str
TLCDefer(expression) ==
  TRUE
-----------------------------------------------------------------------------
TLCNoOp(val) ==
  val
PickSuccessor(exp) ==
  IF (exp)
  THEN TRUE
  ELSE CHOOSE bool \in BOOLEAN : TRUE
-----------------------------------------------------------------------------
TLCCache(expression, closure) ==
  expression
TLCFP(var) ==
  CHOOSE i \in Int: TRUE
-----------------------------------------------------------------------------
TLCEvalDefinition(definitionName) ==
  TRUE
============================================================================
