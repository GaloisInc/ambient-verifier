(declare @malloc ((size SizeT)) Pointer)
(declare @read-c-string ((ptr Pointer)) (String Unicode))
(declare @write-bytes ((dest Pointer) (src (Vector (Bitvector 8)))) Unit)

(defun @getenv ((s Pointer)) Pointer
  (start start:
    (let s-str (funcall @read-c-string s))
    (branch (equal? s-str "SYMBOLIC") symbolic: exit-nomatch:))

  (defblock symbolic:
    (let symbolic-sz (bv-typed-literal SizeT 3))
    (let symbolic-rval (funcall @malloc symbolic-sz))

    (let symbolic-bytes (fresh-vec "byte" (Bitvector 8) 2))
    (funcall @write-bytes symbolic-rval symbolic-bytes)
    (return symbolic-rval))

  (defblock exit-nomatch:
    (let np (make-null))
    (return np)))
