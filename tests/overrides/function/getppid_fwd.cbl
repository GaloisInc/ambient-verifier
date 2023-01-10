(declare @getppid () Short)

; Wrap forward declared getppid haskell override
(defun @getppid_fwd () Short
  (start start:
    (let res (funcall @getppid))
    (return res)))
