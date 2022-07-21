(declare @get-global-pointer-addr ((bin-name (String Unicode)) (addr SizeT)) Pointer)
(declare @get-global-pointer-named ((bin-name (String Unicode)) (global-name (String Unicode))) Pointer)
(declare @malloc-global ((size SizeT)) Pointer)

(defun @_start () Unit
  (start start:
    (let x-ptr (funcall @get-global-pointer-named "startup-override.exe" "x"))
    (let x-val (bv-typed-literal (Bitvector 32) 42))
    (pointer-write (Bitvector 32) le x-ptr x-val)

    (let y-addr (bv-typed-literal SizeT 0x20120))
    (let y-ptr (funcall @get-global-pointer-addr "startup-override.exe" y-addr))
    (let y-val-size (bv-typed-literal SizeT 4))
    (let y-val (funcall @malloc-global y-val-size))
    (let y-val-points-to (bv-typed-literal (Bitvector 32) 27))
    (pointer-write (Bitvector 32) le y-val y-val-points-to)
    (pointer-write Pointer le y-ptr y-val)

    (return ())))
