---- MODULE M ----
EXTENDS Json, IOUtils, TLC, Naturals
ASSUME /\ Serialize(<<123456, 7>>, "out.ndjson", [format |-> "NDJSON", charset |-> "UTF-8", openOptions |-> <<>>])
       /\ Serialize(<<1>>, "out.ndjson", [format |-> "NDJSON", charset |-> "UTF-8", openOptions |-> <<"WRITE">>])
       /\ ndJsonDeserialize("out.ndjson") = <<1, 3456, 7>>
       /\ Serialize(<<"a", [k |-> 2]>>, "out.ndjson", [format |-> "NDJSON", charset |-> "utf8", openOptions |-> <<"APPEND">>])
       /\ ndJsonDeserialize("out.ndjson") = <<1, 3456, 7, "a", [k |-> 2]>>
       /\ Serialize(<<2>>, "new.ndjson", [format |-> "NDJSON", charset |-> "UTF-8", openOptions |-> <<"CREATE_NEW", "WRITE">>])
       /\ ndJsonDeserialize("new.ndjson") = <<2>>
====
