(defun @strlen ( (str Pointer) ) SizeT
  (registers
    ($s Pointer)
    ($ret SizeT)
  )

  (start start:
    (let zlit (bv-typed-literal SizeT 0))
    (set-register! $ret zlit)
    (set-register! $s str)
    (jump first:))

  (defblock first:
    (let zlitbt (bv-typed-literal Byte 0))
    (let pr (pointer-read Byte le $s))
    (branch
       (equal? pr zlitbt)
       exit:
       next:))

  (defblock next:
     (let onesz (bv-typed-literal SizeT 1))
     (let incd (pointer-add $s onesz))
     (set-register! $s incd)
     (jump first:))

  (defblock exit:
     (let diff (pointer-diff $s str))
     (set-register! $ret diff)
     (return $ret))
)
