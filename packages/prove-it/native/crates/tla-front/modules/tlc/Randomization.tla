-------------------------- MODULE Randomization------------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE FiniteSets
RandomSubset(k, S) == CHOOSE T \in SUBSET S : Cardinality(T) = k
RandomSetOfSubsets(k, n, S) == CHOOSE T \in SUBSET SUBSET S :
                                              Cardinality(T) \leq k
TestRandomSetOfSubsets(k, n, S) ==
              [i \in 1..5 |-> Cardinality(RandomSetOfSubsets(k, n, S))]
=============================================================================
