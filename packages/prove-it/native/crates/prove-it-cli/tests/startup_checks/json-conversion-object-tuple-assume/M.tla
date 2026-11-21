---- MODULE M ----
EXTENDS Integers,TLC,Json
ASSUME ToJsonObject(<<3,2,1>>) = "{\"0\":3,\"1\":2,\"2\":1}"
====
