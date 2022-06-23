(defun @way_too_many_arguments ((a Int) (b Int) (c Int) (d Int) (e Int) (f Int) (g Int) (h Int)) Int
  (start start:
    (return (+ a (+ b (+ c (+ d (+ e (+ f (+ g h))))))))))
