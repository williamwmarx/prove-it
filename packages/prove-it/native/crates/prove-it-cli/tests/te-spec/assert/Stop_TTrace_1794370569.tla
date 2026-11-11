---- MODULE Stop_TTrace_1794370569 ----
EXTENDS Sequences, TLCExt, Stop, Toolbox, Naturals, TLC

_expression ==
    LET Stop_TEExpression == INSTANCE Stop_TEExpression
    IN Stop_TEExpression!expression
----

_trace ==
    LET Stop_TETrace == INSTANCE Stop_TETrace
    IN Stop_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        x = (1)
    )
----

_init ==
    /\ x = _TETrace[1].x
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ x  = _TETrace[i].x
        /\ x' = _TETrace[j].x

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("Stop_TTrace_1794370569.json", _TETrace)

=============================================================================

 Note that you can extract this module `Stop_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `Stop_TEExpression.tla` file takes precedence 
  over the module `Stop_TEExpression` below).

---- MODULE Stop_TEExpression ----
EXTENDS Sequences, TLCExt, Stop, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `Stop` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        x |-> x
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_xUnchanged |-> x = x'
        
        \* Format the `x` variable as Json value.
        \* ,_xJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(x)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_xModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].x # _TETrace[s-1].x
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE Stop_TETrace ----
\*EXTENDS IOUtils, Stop, TLC
\*
\*trace == IODeserialize("Stop_TTrace_1794370569.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE Stop_TETrace ----
EXTENDS Stop, TLC

trace == 
    <<
    ([x |-> 0]),
    ([x |-> 1])
    >>
----


=============================================================================

---- CONFIG Stop_TTrace_1794370569 ----

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Wed Nov 11 04:16:10 UTC 2026