; The identity function for a 16-bit int
(declare @short_id ((x Short)) Short)

; Wrap forward declared short_id crucible syntax override
(defun @short_id_fwd ((x Short)) Short
  (start start:
    (let res (funcall @short_id x))
    (return res)))

(defun @test_short_id_fwd () Unit
  (start start:
    (let input (fresh Short))
    (let input_back (funcall @short_id_fwd input))
    (assert! (equal? input input_back) "short_id_fwd test")
    (return ())))
