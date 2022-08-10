(declare @g () Int)

(defun @f () Int
  (start start:
    (let res (funcall @g))
    (return res)))
