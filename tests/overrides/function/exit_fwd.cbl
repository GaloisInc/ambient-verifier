(declare @exit ((x Short)) Unit)

; Wrap forward declared exit haskell override
(defun @exit_fwd ((x Short)) Unit
  (start start:
    (funcall @exit x)
    (return ())))
