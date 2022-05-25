; A test case that ensures forward declarations are resolved in syntax
; override tests.
(declare @byte_id ((x Byte)) Byte)

(defun @byte_id_2 ((x Byte)) Byte
  (start start:
    (let res (funcall @byte_id x))
    (return res)))

(defun @test_byte_id_2 () Unit
  (start start:
    (let input (fresh Byte))
    (let input_back (funcall @byte_id_2 input))
    (assert! (equal? input input_back) "byte_id_2 test")
    (return ())))

