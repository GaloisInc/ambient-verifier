; An override for getuid(2) that returns a symbolic value.  The override
; returns the same value for each subsequent call.

(defglobal $$uid (Bitvector 32))

(defun @getuid () (Bitvector 32)
  (start start:
    (return $$uid)))
