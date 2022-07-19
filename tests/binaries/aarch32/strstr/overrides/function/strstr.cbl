(defun @strstr ((haystack Pointer) (needle Pointer)) Pointer
  (registers
    ($i SizeT))

  (start start:
    (let zero-SizeT (bv-typed-literal SizeT 0))
    (let one-SizeT (bv-typed-literal SizeT 1))
    (let zero-Int (bv-typed-literal Int 0))
    (let one-Int (bv-typed-literal Int 1))
    (let zero-Byte (bv-typed-literal Byte 0))
    (set-register! $i zero-SizeT)
    (jump loop:))

  (defblock loop:
    (let haystacki (pointer-add haystack $i))
    (let haystack-front (pointer-read Byte le haystacki))
    (branch (not (equal? haystack-front zero-Byte)) loop-body-1: exit-null:))

  (defblock loop-body-1:
    (let needle-front (pointer-read Byte le needle))
    (branch (equal? haystack-front needle-front) loop-body-2: loop-continue:))

  (defblock loop-body-2:
    (let compare-res (funcall @compare haystacki needle))
    (let compare-nezero (not (equal? compare-res zero-Int)))
    (branch compare-nezero exit-haystack: loop-continue:))

  (defblock loop-continue:
    (set-register! $i (+ $i one-SizeT))
    (jump loop:))

  (defblock exit-haystack:
    (return haystacki))

  (defblock exit-null:
    (let null (make-null))
    (return null))
)

(defun @compare ((x Pointer) (y Pointer)) Int
  (registers
    ($i SizeT))

  (start start:
    (let zero-SizeT (bv-typed-literal SizeT 0))
    (let zero-Byte (bv-typed-literal Byte 0))
    (set-register! $i zero-SizeT)
    (jump loop:))

  (defblock loop:
    (let xi (pointer-add x $i))
    (let yi (pointer-add y $i))
    (let xi-front (pointer-read Byte le xi))
    (let yi-front (pointer-read Byte le yi))
    (let xi-nezero (not (equal? xi-front zero-Byte)))
    (let yi-nezero (not (equal? yi-front zero-Byte)))
    (branch (and xi-nezero yi-nezero) loop-body: exit-y-null:))

  (defblock loop-body:
    (branch (not (equal? xi-front yi-front)) exit-zero: loop-continue:))

  (defblock loop-continue:
    (let one-SizeT (bv-typed-literal SizeT 1))
    (set-register! $i (+ $i one-SizeT))
    (jump loop:))

  (defblock exit-y-null:
    (branch (equal? yi-front (bv 8 0)) exit-one: exit-zero:))

  (defblock exit-zero:
    (let zero (bv-typed-literal Int 0))
    (return zero))

  (defblock exit-one:
    (let one (bv-typed-literal Int 1))
    (return one))
)
