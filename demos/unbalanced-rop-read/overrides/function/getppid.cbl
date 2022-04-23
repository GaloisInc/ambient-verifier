; An override for getppid(2) that returns a symbolic value.  The override
; returns a new symbolic value each time to represent the fact that the parent
; PID can change at any time.

(defun @getppid () PidT
  (start start:
    (let pid (fresh PidT))
    (return pid)))
