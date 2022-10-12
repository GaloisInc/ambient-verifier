; An override for isatty(2) that returns a symbolic value.  Result is either 0
; or 1.

(defun @isatty () Int
  (start start:
    (let res (fresh Int))
    (let zero (bv-typed-literal Int 0))
    (let one (bv-typed-literal Int 1))
    (assume! (or (equal? res zero) (equal? res one)) "0 or 1")
    (return res)))
