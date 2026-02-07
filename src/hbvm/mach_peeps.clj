(CInt ?c (:value 0)) : (Zero (:data_type .i64) c)

(UnOp _ (:op .cast) oper) : oper

(MemCpy c m d s (CInt (:value size))) :
  (BlockCpy c m d s (:size {@intCast(size)}))

(Store ?c m bs @ (Local _ LocalAlloc:l) offset = {bs.knownOffset()} v) :
  (StackSt (:offset) c m l v)

(Store ?c m bs @ base offset = {bs.knownOffset()} v) :
  (St (:offset) c m base v)

(Load ?c m bs @ (Local _ LocalAlloc:l) offset = {bs.knownOffset()}) :
  (StackLd (:offset) c m l)

(Load ?c m bs @ base offset = {bs.knownOffset()}) :
  (Ld (:offset) c m base)

(BinOp ?c
  (:op op @ pop = {switch (op) {
    .iadd => hb.hbvm.isa.Op.addi8,
    .imul => .muli8,
    .isub => .addi8,
    .bor => .ori,
    .bxor => .xori,
    .band => .andi,
    else => break :rule,
  }}) lhs (CInt (:value imm))) :
  (ImmBinOp (:op pop) (:imm {if (op == .isub) -imm else imm}) c lhs)

(If:i c (BinOp _ (:op op @ instr swap = {switch (op) {
  .ule => .{ hb.hbvm.isa.Op.jgtu, false },
  .uge => .{ .jltu, false },
  .ult => .{ .jltu, true },
  .ugt => .{ .jgtu, true },

  .sle => .{ .jgts, false },
  .sge => .{ .jlts, false },
  .slt => .{ .jlts, true },
  .sgt => .{ .jgts, true },

  .eq => .{ .jne, false },
  .ne => .{ .jeq, false },
  else => break :rule,
}}) lhs rhs)) :
  (IfOp c (:base {i.extra(.If).*}) (:op instr) (:swapped swap) lhs rhs)

