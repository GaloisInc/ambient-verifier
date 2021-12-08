; A simplistic model of libgd's gd_error_ex function
; (https://github.com/libgd/libgd/blob/ba14dec6efe9d87fe80fa1d7bd3d5b0583e1320e/src/gd.c#L116)
; that does nothing.
(defun @gd_error_ex ((priority Int) (format Pointer) (va_args Pointer)) Unit
  (start start:
    (return ())))
