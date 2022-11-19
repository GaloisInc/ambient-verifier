(defun @memcmp ((a Pointer) (b Pointer) (n SizeT)) Int
  (registers
    ($i SizeT)
    ($aval Byte)
    ($bval Byte))

  (start start:
    (let one (bv-typed-literal SizeT 1))
    (let zlit (bv-typed-literal SizeT 0))
    (let zint (bv-typed-literal Int 0))
    (let ret (fresh Int))
    (set-register! $i zlit)
    (jump loop:))

  (defblock loop:
    (let ptra (pointer-add a $i))
    (let vala (pointer-read Byte le ptra))
    (set-register! $aval vala)
    (let ptrb (pointer-add b $i))
    (let valb (pointer-read Byte le ptrb))
    (set-register! $bval valb)
    (set-register! $i (+ $i one))
    (branch (< $aval $bval) exita: loopb:))

  (defblock loopb:
    (branch (< $bval $aval) exitb: loopc:))

  (defblock loopc:
    (branch (equal? $i (- n one)) exitc: loop:))


  (defblock exita:
    (assume! (< ret zint) "less than case")
    (return ret))
  (defblock exitb:
    (assume! (< zint ret) "greater than case")
    (return ret))
  (defblock exitc:
    (return zint))
)
