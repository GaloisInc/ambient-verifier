; Assert that `assertion` is nonzero
(defun @ambient_assert ((assertion SizeT)) Unit
  (start start:
    (let zero (bv-typed-literal SizeT 0))
    (assert! (not (equal? assertion zero)) "ambient_assert override")
    (return ())))
