; Compute the difference between p1 and p2.  If either is NULL, returns 0.
(defun @checked_ptr_diff ((p1 Pointer) (p2 Pointer)) SizeT
  (start start:
    (let null (make-null))
    (let p1-null (pointer-eq p1 null))
    (let p2-null (pointer-eq p2 null))
    (branch (or p1-null p2-null) has-null: non-null:))

  (defblock has-null:
    (let zero (bv-typed-literal SizeT 0))
    (return zero))

  (defblock non-null:
    (let delta (pointer-diff p1 p2))
    (return delta)))
