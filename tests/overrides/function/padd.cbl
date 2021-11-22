; A basic function that computes the sum of two Pointers
(defun @padd ((p1 Pointer) (p2 (Bitvector 64))) Pointer
  (start start:
    (let res (pointer-add p1 p2))
    (return res)))

