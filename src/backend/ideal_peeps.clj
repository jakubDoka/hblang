(UnOp ?c (:op op && {op.propagatesPoison()}) :data_type (Poison) _) :
  (Poison c :data_type)

(BinOp ?c (:op op && {op.propagatesPoison() == .yes}) :data_type (Poison) _) :
  (Poison c :data_type)

(BinOp ?c (:op op && {op.propagatesPoison() == .yes}) :data_type _ (Poison)) :
  (Poison c :data_type)

(BinOp _ (:op op && {op.propagatesPoison() == .into_other_value}) (Poison) vl) : vl
(BinOp _ (:op op && {op.propagatesPoison() == .into_other_value}) vl (Poison)) : vl

(BinOp ?c :op :data_type
  (CInt _ (:value lhs))
  (CInt _ (:value rhs))
) : (CInt c (:value {op.eval(data_type, lhs, rhs)}))

(BinOp ?ct (:op op && {op.isDistributing()})
  (BinOp _ (:op other_op &&
    {other_op.isDistributive() and other_op.isComutative()}) a b)
  (BinOp _ (:op (&other_op)) c d @ e f g =
    {hb.utils.undistributeComutative(a, b, c, d) orelse break :rule})
) : (BinOp ct (:op other_op) e (BinOp ct (:op) f g))

(BinOp ?ct (:op op && {op.isDistributing()})
  (BinOp _ (:op other_op &&
    {other_op.isRightDistributive()}) a b)
  (BinOp _ (:op (&other_op)) c d @ e f g =
    {hb.utils.undistribute(a, b, c, d, true) orelse break :rule})
) : (BinOp ct (:op other_op) (BinOp ct (:op) e f) g)

(BinOp ?c (:op op @ cnst = {op.symetricConstant()}) a (&a)) :
  (CInt c (:value {cnst orelse break :rule}))

(BinOp _ :data_type :op lhs
  (CInt (:value rhs & {op.neutralElememnt(data_type)}))) : lhs

(BinOp ?c :op _ (CInt (:value v @ nvl = {op.killConstant(v)}))) :
  (CInt c (:value {nvl orelse break :rule}))

(BinOp ?c :op :data_type CInt:lhs rhs &&
  {op.isComutative() and data_type.isInt()}) :
  (BinOp c :op rhs lhs) && {
  worklist.add(res);
}

(BinOp ?c lhs
  (CInt (:value rhs && {rhs > 0 and std.math.isPowerOfTwo(rhs)}
    @ rhs_pow = {std.math.log2_int(u64, @bitCast(rhs))}))
  (:op op @ rop rhs_val = {switch (op) {
    .udiv => .{ hb.backend.graph.BinOp.ushr, rhs_pow },
    .sdiv => .{ .sshr, rhs_pow },
    .umod, .smod => .{ .band, rhs - 1 },
    .imul => .{ .ishl, rhs_pow },
    else => break :rule,
  }})
) : (BinOp c (:op rop) lhs (CInt c (:value rhs_val)))

(BinOp ?c (:op op && {op.isAsociative()})
  (BinOp _ (:op &op) lhs (CInt _ (:value rl)))
  (CInt _ (:value rv))
) : (BinOp c :op lhs (CInt c (:value {op.eval(lhs.data_type, rl, rv)})))

(Store _ mem _ (Poison)) : mem

(MemCpy _ mem _ _ (CInt _ (:value 0))) : mem

(Phi c && {!c.preservesIdentityPhys()} l (&l)) : l

(Phi:p _ l (&p)) : l

(Phi reg
  (Store:l _ (:data_type dt) lmem base lv)
  (Store:r _ (:data_type &dt) rmem (&base) rv)
) : (Store reg (:data_type dt)
  (Phi (:data_type .top) reg lmem rmem)
  base (Phi (:data_type dt) reg lv rv)) && {
  worklist.add(l);
  worklist.add(r);
}

(UnOp ?c :op (:data_type dst) (CInt (:data_type src) (:value oper))) :
  (CInt c (:value {op.eval(src, dst, oper)}))

(UnOp _ (:op .uext | .sext) (:data_type dst)
  (_:oper (:data_type src & {dst.meet(src)}))) : oper

