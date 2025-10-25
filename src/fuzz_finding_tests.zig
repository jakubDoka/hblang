const utils = @import("utils");

test "id:000000,sig:11,src:000272,time:52581,execs:4247030,op:havoc,rep:12" {
    try utils.runFuzzFindingTest(
        "id:000000,sig:11,src:000272,time:52581,execs:4247030,op:havoc,rep:12",
        "main :=  loop {\x14    1 \x04 n := 0\x0a        n += 1\x0a    }\x0a",
    );
}

