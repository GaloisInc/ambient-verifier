; A basic function that computes the sum of two Pointers
(defun @padd ((p1 Pointer) (p2 SizeT)) Pointer
  (start start:
    (let res (pointer-add p1 p2))
    (return res)))

