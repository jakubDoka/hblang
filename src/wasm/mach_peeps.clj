(BinOp ?c (:op .eq) (_:lhs (:data_type .i64 | .i32 | .i16 | .i8)) (CInt (:value 0))) :
  (Eqz c lhs)

(Store ?c m bs @ (Local _ LocalAlloc:l) offset = {bs.knownOffset()} v) :
  (StackStore# (:offset) c m l v)

(Store ?c m bs @ base offset = {bs.knownOffset()} v) :
  (WStore# (:offset) c m base v)

(UnOp _ (:op .sext) (:data_type)
  (StackLoad ?c (:base) (:data_type src_ty) (:offset) m bs)) :
  (SignedStackLoad (:base) (:src_ty) (:data_type) (:offset) c m bs)

(UnOp _ (:op .sext) (:data_type)
  (WLoad ?c (:base) (:data_type src_ty) (:offset) m bs)) :
  (SignedLoad (:base) (:src_ty) (:data_type) (:offset) c m bs)

(Load ?c m bs @ (Local _ LocalAlloc:l) offset = {bs.knownOffset()}) :
  (StackLoad# (:offset) c m l)

(Load ?c m bs @ base offset = {bs.knownOffset()}) :
  (WLoad# (:offset) c m base)

(UnOp _ (:op .uext) (:data_type .i64)
  (WLoad ?c (:base) (:data_type src_ty) (:offset) m bs)) :
  (UnsignedLoad (:base) (:offset) (:src_ty) c m bs)

(UnOp _ (:op .uext) (:data_type .i64)
  (StackLoad ?c (:base) (:data_type src_ty) (:offset) m bs)) :
  (UnsignedStackLoad (:base) (:offset) (:src_ty) c m bs)

(UnOp ?c (:data_type .i8) (:op .ctz) (_:v (:data_type .i64))) :
  (UnOp c (:op .ired) (:data_type .i8) (UnOp c (:data_type .i64) (:op .ctz) v))

(UnOp _ (:op .uext) (:data_type .i32 | .i16) (WLoad:l)) : l

(UnOp _ (:op .uext) (:data_type .i32 | .i16) (StackLoad:l)) : l
