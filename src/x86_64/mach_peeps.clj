(_ _ && {node.isStore()}
  (Phi:mem (Loop:l lctrl && {l.outputs().len == 4}
    (Then (If:loop_if &l (ImmOp _ (:imm 0) (:op .ugt)
      (Phi:iphi &l in_count (ImmOp _ (:op .isub) (:imm 1) &iphi))
    )))) in_mem (&node))
  (Phi:ph &l ptr (ImmOp _ (:op .iadd) (:imm 1) &ph))
  value
) : (RepStosb lctrl in_mem ptr value in_count) && {
  Backend.postporcessRepStosb(func, res, mem, loop_if, node, worklist);
}

(Store ?c m bs @ LocalAlloc:l dis = {bs.knownOffset()}
  (BinOp _ (:op op & .iadd | .isub | .bor | .band | .bxor)
    (Load _ (&m) (&bs)) (CInt (:data_type) (:value value & {Backend.clampI32(value)})))) :
  (ConstOpStackStore (:ty data_type) (:dis {@intCast(dis)}) (:op) (:imm {@intCast(value)}) c m l)

(Store ?c m bs @ base dis = {bs.knownOffset()}
  (BinOp _ (:op op & .iadd | .isub | .bor | .band | .bxor)
    (Load _ (&m) (&bs)) (CInt (:data_type) (:value value & {Backend.clampI32(value)})))) :
  (ConstOpStore (:ty data_type) (:dis {@intCast(dis)}) (:op) (:imm {@intCast(value)}) c m base)

(Store ?c m bs @ (Local _ LocalAlloc:l) dis = {bs.knownOffset()}
  (BinOp _ (:op op & .iadd | .isub | .bor | .band | .bxor)
    (Load _ (&m) (&bs)) r)) : (OpStackStore (:dis {@intCast(dis)}) (:op) c m l r)

(Store ?c m bs @ base dis = {bs.knownOffset()}
  (BinOp _ (:op op & .iadd | .isub | .bor | .band | .bxor)
    (Load _ (&m) (&bs)) r)) : (OpStore (:dis {@intCast(dis)}) (:op) c m base r)

(Store ?c m bs @ (Local _ LocalAlloc:l)
  dis = {bs.knownOffset()}
  (CInt (:data_type dt && {dt.isInt()}) (:value value & {Backend.clampI32(value)}))) :
  (ConstStackStore (:dis {@intCast(dis)}) (:imm {@intCast(value)}) (:ty dt) c m l)

(Store ?c  m bs @ LocalAlloc:l
  dis = {bs.knownOffset()}
  (CInt (:data_type dt && {dt.isInt()}) (:value value & {Backend.clampI32(value)}))) :
  (ConstStackStore (:dis {@intCast(dis)}) (:imm {@intCast(value)}) (:ty dt) c m l)

(Store ?c m bs @ (GlobalAddr (:id) _ s)
  dis = {bs.knownOffset()}
  (CInt (:data_type dt && {dt.isInt()}) (:value value & {Backend.clampI32(value)}))) :
  (ConstGlobalStore (:dis {@intCast(dis)}) (:imm {@intCast(value)})
    (:id) (:ty dt) c m {null} s)
&& {res.input_ordered_len -= 1;}

(Store ?c m bs @ base dis = {bs.knownOffset()}
  (CInt (:data_type dt && {dt.isInt()}) (:value value & {Backend.clampI32(value)}))) :
  (ConstStore (:ty dt) (:dis {@intCast(dis)}) (:imm {@intCast(value)}) c m base)

(Store ?c m bs @ (GlobalAddr (:id) _ s) dis = {bs.knownOffset()} v) :
  (GlobalStore (:dis {@intCast(dis)}) (:id) c m {null} v s)
&& {res.input_ordered_len -= 1;}

(Store ?c m bs @ (Local _ LocalAlloc:l) dis = {bs.knownOffset()} v) :
  (StackStore (:dis {@intCast(dis)}) c m l v)

(Store ?c m bs @ LocalAlloc:l dis = {bs.knownOffset()} v) :
  (StackStore (:dis {@intCast(dis)}) c m l v)

(Store ?c m bs @ base dis = {bs.knownOffset()} v) :
  (OffsetStore (:dis {@intCast(dis)}) c m base v)

(Load ?c m bs @ (GlobalAddr (:id) _ s) dis = {bs.knownOffset()}) :
  (GlobalLoad (:dis {@intCast(dis)}) (:id) c m {null} s)
&& {res.input_ordered_len -= 1;}

(Load ?c m bs @ (Local _ LocalAlloc:l) dis = {bs.knownOffset()}) :
  (StackLoad (:dis {@intCast(dis)}) c m l)

(Load ?c m bs @ (LocalAlloc:l) dis = {bs.knownOffset()}) :
  (StackLoad (:dis {@intCast(dis)}) c m l)

(Load ?c m bs @ base dis = {bs.knownOffset()}) :
  (OffsetLoad (:dis {@intCast(dis)}) c m base)


(If:f c (BinOp _ (:op op & .ne | .eq | .uge | .ule | .ugt
  | .ult | .sge | .sle | .sgt | .slt) a b)) :
  (CondJump (:op) (:base {f.extra(.If).*}) c a b)

(If:f c (ImmOp _ (:op op & .ne | .eq | .uge | .ule | .ugt
  | .ult | .sge | .sle | .sgt | .slt) a :imm)) :
  (ImmCondJump (:op) (:base {f.extra(.If).*}) :imm c a)

(CondJump:f c (:op) a (CInt (:value value & {Backend.clampI32(value)}))) :
  (ImmCondJump (:op) (:base {f.extra(.CondJump).base}) (:imm {@intCast(value)}) c a)

(If:f c (ImmOp _ (:op op & .ugt | .ne) v (:imm 0))) :
  (If (:id {f.extra(.If).id}) c v)

(BinOp ?c :data_type (:op op & .iadd | .isub | .bor | .band | .bxor)
  l (StackLoad _ (:data_type (&data_type)) :dis m p)) :
  (OpStackLoad (:op) (:dis) c m p l)

(BinOp _ :data_type (:op op & .iadd | .isub | .bor | .band | .bxor)
  l (OffsetLoad ?c && {c == null} (:data_type (&data_type)) :dis m p)) :
  (OpLoad (:op) (:dis) c m p l)

(BinOp ?c (:op .iadd) bs @ base dis = {bs.knownOffset()}
  (ImmOp _ (:op .ishl) (:imm scale & 0 .. 3) index)) :
  (IndexLea (:dis {@intCast(dis)}) (:scale {@intCast(scale)}) c base index)

(BinOp ?c (:op .iadd) (Local _ LocalAlloc:l)
  (CInt (:value value & {Backend.clampI32(value)}))) :
  (StackLea (:dis {@intCast(value)}) c l)

(BinOp ?c 
  (:op op & .band | .bor | .bxor)
  lhs (CInt (:value value & {Backend.clampI32(value)})
    (:data_type d && {d.size() > 1}))) :
  (ImmOp (:op) (:imm {@intCast(value)}) c lhs)

(BinOp ?c 
  (:op op & .iadd | .isub | .ishl | .ushr | .sshr)
  lhs (CInt (:value value & {Backend.clampI32(value)}))) :
  (ImmOp (:op) (:imm {@intCast(value)}) c lhs)

(BinOp ?c
  (:op op & .eq | .ne | .uge | .ule | .ugt | .ult | .sge | .sle | .sgt | .slt)
  lhs (CInt (:value value & {Backend.clampI32(value)})
    (:data_type d && {d.size() > 2 and d.isInt()}))) :
  (ImmOp (:op) (:imm {@intCast(value)}) c lhs)

(BinOp ?ct (:op .fadd) (BinOp _ (:op .fmul) b c) a) : (FusedMulAdd ct a b c)
(BinOp ?ct (:op .fadd) a (BinOp _ (:op .fmul) b c)) : (FusedMulAdd ct a b c)

(BinOp ?c (:op .iadd) (Local _ LocalAlloc:l)
  (CInt (:value dis & {Backend.clampI32(dis)}))
) : (StackLea (:dis {@intCast(dis)}) c l)

(Splat _ (:data_type {hb.backend.graph.DataType.vec(.f32, .v128)})
       (F32:n _ (:imm {0.0}))) : n
(Splat _ (:data_type {hb.backend.graph.DataType.vec(.f64, .v128)})
       (F64:n _ (:imm {0.0}))) : n
(Splat ?c (:data_type {hb.backend.graph.DataType.vec(.i8, .v128)}) v) :
  (SplatSmall c v (F64 c (:imm {0.0})))

(UnOp ?c (:op .fneg) (:data_type .f32) a) :
  (BinOp c (:op .fsub) (F32 c (:imm {0.0})) a)
(UnOp ?c (:op .fneg) (:data_type .f64) a) :
  (BinOp c (:op .fsub) (F64 c (:imm {0.0})) a)
(UnOp ?c (:op .fneg) (:data_type {hb.backend.graph.DataType.vec(.f32, .v128)}) a) :
  (BinOp c (:op .fsub) (F32 c (:imm {0.0})) a)
(UnOp ?c (:op .fneg) (:data_type {hb.backend.graph.DataType.vec(.f64, .v128)}) a) :
  (BinOp c (:op .fsub) (F64 c (:imm {0.0})) a)
(UnOp ?c (:op .ctz) (_:nd (:data_type .i8))) :
  (UnOp c (:op .ctz) (BinOp c (:data_type .i16) (:op .bor)
                            (UnOp c (:data_type .i16) (:op .uext) nd)
                            (CInt c (:data_type .i16) (:value {1 << 8}))))

(CInt ?c (:data_type .f64) (:value value)) : (F64 (:imm {@bitCast(value)}) c)
(CInt ?c (:data_type .f32) (:value value)) :
  (F32 (:imm {@bitCast(@as(u32, @intCast(value)))}) c)
