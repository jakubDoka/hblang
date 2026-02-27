(UnOp ?c (:op op && {op.propagatesPoison()}) :data_type (Poison) _) :
  (Poison c :data_type)

(BinOp ?c (:op op && {op.propagatesPoison() == .yes}) :data_type (Poison) _) :
  (Poison c :data_type)

(BinOp ?c (:op op && {op.propagatesPoison() == .yes}) :data_type _ (Poison)) :
  (Poison c :data_type)

(BinOp _ (:op op && {op.propagatesPoison() == .into_other_value}) (Poison) vl) : vl
(BinOp _ (:op op && {op.propagatesPoison() == .into_other_value}) vl (Poison)) : vl

(BinOp _ (:op .ne) (_:vl (:data_type .i8)) (CInt (:value 0))) : vl

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

;(Phi (Region:r) (CInt:i (:value 0))
;     (BinOp:do ?c (:op .disjoint_or) _ @ a b = {do.normalizedDisjointValues(func)})) :
;  (BinOp (:op .disjoint_or) c 
;         (Phi (:data_type {a.data_type}) r i a)
;         (Phi (:data_type {a.data_type}) r i b))
;
;(Phi (Region:r)
;     (BinOp:do ?c (:op .disjoint_or) _ @ a b = {do.normalizedDisjointValues(func)})
;     (CInt:i (:value 0))) :
;  (BinOp (:op .disjoint_or) c
;         (Phi (:data_type {a.data_type}) r a i)
;         (Phi (:data_type {a.data_type}) r b i))

;(BinOp (:op .ushr) _ (BinOp (:op .disjoint_or) _ v) (CInt (:value 8))) : v

(Store _ mem _ (Poison)) : mem

(MemCpy _ mem _ _ (CInt _ (:value 0))) : mem

(UnOp ?c :op (:data_type dst) (CInt (:data_type src) (:value oper))) :
  (CInt c (:value {op.eval(src, dst, oper)}))

(UnOp _ (:op .uext | .sext) (:data_type dst)
  (_:oper (:data_type src & {dst.meet(src)}))) : oper

