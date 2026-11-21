---- MODULE M ----
EXTENDS TLC, Json
ASSUME PrintT(JsonDeserialize("lone.json"))
====
