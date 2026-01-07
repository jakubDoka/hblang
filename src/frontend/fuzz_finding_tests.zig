const utils = @import("utils");

//test "id:000000,sig:11,src:000153,time:64035,execs:5586114,op:havoc,rep:2" {
//    try utils.runFuzzFindingTest(
//        "id:000000,sig:11,src:000153,time:64035,execs:5586114,op:havoc,rep:2",
//        "foo.{global} := @use(\"global2.hb\")\x0a\x0amain := fn(): uint {\x0a    return global\x0a}\x0a\x0a// in: global2.hb\x0a.{global} := @use(\"global.hc\")\x0a\x0a// in: global.hc\x0a$global := 0",
//    );
//}
//
