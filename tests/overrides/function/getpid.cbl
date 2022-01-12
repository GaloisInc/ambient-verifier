; An override for getpid(2) that returns a symbolic value.  The override
; returns the same value for each subsequent call.

(defglobal $$pid PidT)

(defun @getpid () PidT
  (start start:
    (return $$pid)))

(defun @test_getpid () Unit
  (start start:
    (let pid_back (funcall @getpid))
    (assert! (equal? pid_back $$pid) "getpid test")
    (return ())))

; A failing version of the getpid test to verify that test-overrides mode can
; detect failing tests
(defun @test_getpid_failing () Unit
  (start start:
    (let pid_back (funcall @getpid))
    (assert! (not (equal? pid_back $$pid)) "failing getpid test")
    (return ())))
