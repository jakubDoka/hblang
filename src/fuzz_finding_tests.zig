const utils = @import("utils");

//test "id:000000,sig:06,src:000053,time:377,execs:2973,op:havoc,rep:4" {
//    try utils.runFuzzFindingTest(
//        "id:000000,sig:06,src:000053,time:377,execs:2973,op:havoc,rep:4",
//        "S := ft($A: type): type return st ruct {\x0a    get := fn(): u32 return A.get() + 1\x0a}\x0a\x0aZ := struct {\x0a    get := fn(): u32 return 0\x0a@syscall}\x0a\x7f\x00ain := fn(): uint {\x0a    return S(S(S(S(S(S(S(S(Z)))))))).get() != 8\x0a}",
//    );
//}
//
//test "id:000000,sig:11,src:000114,time:2211,execs:70008,op:havoc,rep:2" {
//    try utils.runFuzzFindingTest(
//        "id:000000,sig:11,src:000114,time:2211,execs:70008,op:havoc,rep:2",
//        "main := fn(): uint {\x0a    for i := 0..10 {\x0a       $if i == 0 continue\x0a  \x1f }\x0a    return 0\x0a}",
//    );
//}
//
//test "id:000000,sig:06,src:000264,time:352,execs:3488,op:havoc,rep:14" {
//    try utils.runFuzzFindingTest(
//        "id:000000,sig:06,src:000264,time:352,execs:3488,op:havoc,rep:14",
//        "maoo := un(x: ?u+8ct{.l: u16; .r: u16}, @bi): bool {\x0a    bwa := fn(x: [7]?bool): u32 r     .a => rein := fn(): Vi\x91t \x0a    \xe0\xb6\x9e := 1\x0a    b := 2\x0a   {\x0a    \x7f\xb6\x9e :=!1\x0a \x05  b := 2\x0b    \xe0\xb6\x9e += 1\x0a    return \xe0\xb6\x9e - b\x0a}",
//    );
//}
//
