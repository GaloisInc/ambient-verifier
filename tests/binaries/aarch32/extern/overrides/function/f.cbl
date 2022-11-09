(defglobal $$shared-global Int)

(defun @f () Unit
  (start start:
    (let forty-two (bv-typed-literal Int 42))
    (set-global! $$shared-global forty-two)
    (return ())))
