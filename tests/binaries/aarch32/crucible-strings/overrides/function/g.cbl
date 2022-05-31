(declare @write-c-string ((dst Pointer) (src (String Unicode))) Unit)

(defun @g ((dst Pointer)) Unit
  (start start:
    (funcall @write-c-string dst "hello")
    (return ()))
)
