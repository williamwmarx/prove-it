---- MODULE Dead_TTrace_1794370569 ----
EXTENDS Sequences, TLCExt, Dead, Toolbox, Naturals, TLC

_expression ==
    LET Dead_TEExpression == INSTANCE Dead_TEExpression
    IN Dead_TEExpression!expression
----

_trace ==
    LET Dead_TETrace == INSTANCE Dead_TETrace
    IN Dead_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        x = (2)
        /\
        y = ("a")
    )
----

_init ==
    /\ x = _TETrace[1].x
    /\ y = _TETrace[1].y
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ x  = _TETrace[i].x
        /\ x' = _TETrace[j].x
        /\ y  = _TETrace[i].y
        /\ y' = _TETrace[j].y

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("Dead_TTrace_1794370569.json", _TETrace)

=============================================================================

 Note that you can extract this module `Dead_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `Dead_TEExpression.tla` file takes precedence 
  over the module `Dead_TEExpression` below).

---- MODULE Dead_TEExpression ----
EXTENDS Sequences, TLCExt, Dead, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `Dead` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        x |-> x
        ,y |-> y
        
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
\*---- MODULE Dead_TETrace ----
\*EXTENDS IOUtils, Dead, TLC
\*
\*trace == IODeserialize("Dead_TTrace_1794370569.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE Dead_TETrace ----
EXTENDS Dead, TLC

trace == 
    <<
    ([x |-> 0,y |-> "a"]),
    ([x |-> 1,y |-> "a"]),
    ([x |-> 2,y |-> "a"])
    >>
----


=============================================================================

---- CONFIG Dead_TTrace_1794370569 ----

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
\* Generated on Wed Nov 11 04:16:09 UTC 2026