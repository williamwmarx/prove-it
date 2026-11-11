---- MODULE Stut_TTrace_1794372783 ----
EXTENDS Sequences, TLCExt, Toolbox, Stut, Naturals, TLC

_expression ==
    LET Stut_TEExpression == INSTANCE Stut_TEExpression
    IN Stut_TEExpression!expression
----

_trace ==
    LET Stut_TETrace == INSTANCE Stut_TETrace
    IN Stut_TETrace!trace
----

_prop ==
    ~<>[](
        x = (2)
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
    \*         IN J!JsonSerialize("Stut_TTrace_1794372783.json", _TETrace)

=============================================================================

 Note that you can extract this module `Stut_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `Stut_TEExpression.tla` file takes precedence 
  over the module `Stut_TEExpression` below).

---- MODULE Stut_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Stut, Naturals, TLC

expression == 
    [
        \* To hide variables of the `Stut` spec from the error trace,
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
\*---- MODULE Stut_TETrace ----
\*EXTENDS IOUtils, Stut, TLC
\*
\*trace == IODeserialize("Stut_TTrace_1794372783.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE Stut_TETrace ----
EXTENDS Stut, TLC

trace == 
    <<
    ([x |-> 0]),
    ([x |-> 1]),
    ([x |-> 2])
    >>
----


=============================================================================

---- CONFIG Stut_TTrace_1794372783 ----

PROPERTY
    _prop

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
\* Generated on Wed Nov 11 04:53:04 UTC 2026