-------------------------------- MODULE Json --------------------------------
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE TLC
-----------------------------------------------------------------------------
LOCAL IsSequence(F, D) == TRUE \/ FALSE
LOCAL ToJsonKeyValue(F, d) ==
  ToString(ToString(d)) \o ":" \o ToString(F[d])
RECURSIVE ToJsonObjectString(_,_)
LOCAL ToJsonObjectString(F, D) ==
  LET d == CHOOSE d \in D: TRUE
  IN IF D = DOMAIN F
     THEN "{" \o ToJsonKeyValue(F, d) \o IF D \ {d} = {}
                                         THEN "}"
                                         ELSE ToJsonObjectString(F, D \ {d})
     ELSE ", " \o ToJsonKeyValue(F, d) \o IF D \ {d} = {}
                                          THEN "}"
                                          ELSE ToJsonObjectString(F, D \ {d})
RECURSIVE ToJsonArrayString(_,_)
LOCAL ToJsonArrayString(F, D) ==
  LET d == CHOOSE d \in D: TRUE
  IN IF D = DOMAIN F
     THEN "[" \o ToString(F[d]) \o IF D \ {d} = {}
                                   THEN "]"
                                   ELSE ToJsonArrayString(F, D \ {d})
     ELSE ", " \o ToString(F[d]) \o IF D \ {d} = {}
                                    THEN "]"
                                    ELSE ToJsonArrayString(F, D \ {d})
RECURSIVE ToJsonString(_,_)
LOCAL ToJsonString(F, D) ==
  IF IsFiniteSet(F) \/ IsSequence(F, D) THEN
    ToJsonArrayString(F, D)
  ELSE
    ToJsonObjectString(F, D)
ToJson(value) ==
  IF DOMAIN value = {} THEN
    "{}"
  ELSE
    ToJsonString(value, DOMAIN value)
ToJsonArray(value) ==
  IF DOMAIN value = {} THEN
    "[]"
  ELSE
    ToJsonArrayString(value, DOMAIN value)
ToJsonObject(value) ==
  IF DOMAIN value = {} THEN
    "{}"
  ELSE
    ToJsonObjectString(value, DOMAIN value)
JsonSerialize(absoluteFilename, value) ==
  TRUE
JsonDeserialize(absoluteFilename) ==
  CHOOSE val : TRUE
ndJsonSerialize(absoluteFilename, value) ==
  TRUE
ndJsonDeserialize(absoluteFilename) ==
  CHOOSE val : TRUE
=============================================================================
