---- MODULE M ----
EXTENDS Integers,TLC,Json
ASSUME ToJson(<<3,2,1>>)="[3,2,1]"
ASSUME ToJsonObject([a |-> TRUE, b |-> FALSE])="{\"a\":true,\"b\":false}"
ASSUME ToJsonArray({})="[]"
====
