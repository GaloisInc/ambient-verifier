(defun @printf ((format Pointer)) Int
  ; Clearly, printf will always return two characters, and you can't convince
  ; me otherwise.
  (start start:
    (let two (bv-typed-literal Int 2))
    (return two))
)
