(defun @strncmp ((s1 Pointer) (s2 Pointer) (n SizeT)) Int
  (registers
    ($s1 Pointer)
    ($s2 Pointer)
    ($n SizeT)
    ($i SizeT))
  (start init_params:
    (set-register! $s1 s1)
    (set-register! $s2 s2)
    (set-register! $n n)
    (jump start:))
  (defblock start:
    (let zero (bv-typed-literal SizeT 0))
    (let rv zero)
    (set-register! $i rv)
    (jump loop_start:))
  (defblock loop_start:
    (let rv0 (pointer-read Byte le $s1))
    (let zero1 (bv-typed-literal Byte 0))
    (let rv2 (pointer-read Byte le $s2))
    (let one (bv-typed-literal SizeT 1))
    (let rv3 (pointer-read Byte le $s1))
    (let rv4 (pointer-read Byte le $s2))
    (branch (and (and (and (not (equal? rv0 zero1)) (not (equal? rv2 zero1))) (equal? rv3 rv4)) (< $i $n)) loop_next: loop_done:))
  (defblock loop_next:
    (let ptrOpR one)
    (let pv (pointer-add $s1 ptrOpR))
    (set-register! $s1 pv)
    (let pv5 (pointer-add $s2 ptrOpR))
    (set-register! $s2 pv5)
    (let rv6 (+ $i one))
    (set-register! $i rv6)
    (jump loop_start:))
  (defblock loop_done:
    (branch (equal? $i $n) then: done:))
  (defblock then:
    (return zero))
  (defblock done:
    (let rv7 (pointer-read Byte le $s1))
    (let rv8 (pointer-read Byte le $s2))
    (let r (- (zero-extend 32 rv7) (zero-extend 32 rv8)))
    (return r)))
