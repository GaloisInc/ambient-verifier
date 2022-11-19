(declare @get-global-pointer-named ((bin-name (String Unicode)) (global-name (String Unicode))) Pointer)

(extern $$AMBIENT_environ Pointer)

(defun @_start () Unit
  (start start:
    (let environ-ptr (funcall @get-global-pointer-named "environ.exe" "environ"))
    (pointer-write Pointer le environ-ptr $$AMBIENT_environ)
    (return ())))
