
;(Store ?c m bs @ (Local _ LocalAlloc:l) offset = {bs.knownOffset()} v) :
;  (StackSt (:offset) c m l v)

(Store ?c m bs @ base offset = {bs.knownOffset()} v) :
  (WStore (:offset) c m base v)

;(Load ?c m bs @ (Local _ LocalAlloc:l) offset = {bs.knownOffset()}) :
;  (StackLd (:offset) c m l)

(Load ?c m bs @ base offset = {bs.knownOffset()}) :
  (WLoad (:offset) c m base)
