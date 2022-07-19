(declare @malloc ((size SizeT)) Pointer)

(defun @f ((x Pointer)) Unit
  (start start:
    (let int-size (bv-typed-literal SizeT 4))
    (let ptr (funcall @malloc int-size))
    (let val (bv-typed-literal Int 42))
    (pointer-write Int le ptr val)
    (pointer-write Pointer le x ptr)
    (return ())))
