; A basic function that copies the data pointed to by one pointer to another
(defun @copy ((src Pointer) (dest Pointer)) Unit
  (start start:
    (let src-data (pointer-read 4 le src))
    (pointer-write 4 le dest src-data)
    (return ())))

