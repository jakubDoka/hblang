(BinOp ?c (:op .eq) (_:lhs (:data_type .i64 | .i32 | .i16 | .i8)) (CInt (:value 0))) :
  (Eqz c lhs)

(Store ?c m bs @ (Local _ LocalAlloc:l) offset = {bs.knownOffset()} v) :
  (StackStore (:offset) c m l v)

(Store ?c m bs @ base offset = {bs.knownOffset()} v) :
  (WStore (:offset) c m base v)

(Load ?c m bs @ (Local _ LocalAlloc:l) offset = {bs.knownOffset()}) :
  (StackLoad (:offset) c m l)

(Load ?c m bs @ base offset = {bs.knownOffset()}) :
  (WLoad (:offset) c m base)

(UnOp _ (:op .uext) (:data_type .i32 | .i16) (WLoad:l)) : l
