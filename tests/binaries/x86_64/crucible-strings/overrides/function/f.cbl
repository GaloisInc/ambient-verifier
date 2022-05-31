(declare @read-c-string ((x Pointer)) (String Unicode))

(defun @f ((x Pointer)) Int
  (start start:
    (let x-str (funcall @read-c-string x))
    (jump cmp-1:))

  (defblock cmp-1:
    (branch (equal? x-str "hello") exit-hello: cmp-2:))

  (defblock cmp-2:
    (branch (equal? x-str "world!") exit-world: exit-fallback:))

  (defblock exit-hello:
    (let r1 (bv-typed-literal Int 1))
    (return r1))

  (defblock exit-world:
    (let r2 (bv-typed-literal Int 2))
    (return r2))

  (defblock exit-fallback:
    (let r3 (bv-typed-literal Int 3))
    (return r3))
)
