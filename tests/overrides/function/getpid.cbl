; An override for getpid(2) that returns a symbolic value.  The override
; returns the same value for each subsequent call.

(defglobal $$pid PidT)

(defun @getpid () PidT
  (start start:
    (return $$pid)))
