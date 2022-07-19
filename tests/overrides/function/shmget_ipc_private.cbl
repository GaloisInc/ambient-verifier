(declare @shmget ((key SizeT) (size SizeT) (shmflg Int)) Int)
(declare @shmat ((shmid Int) (shmaddr Pointer) (shmflg Int)) Pointer)

; A version of shmget that hardcodes its arguments.
(defun @shmget_ipc_private () Int
  (start start:
    ; Here, we assume that IPC_PRIVATE is equal to 0. This is currently the
    ; case on all OS/architecture configurations that we support, but we may
    ; want to abstract this out in the future. See #75.
    (let ipc-private (bv-typed-literal SizeT 0))
    (let size (bv-typed-literal SizeT 32))
    (let shmflg (bv-typed-literal Int 0))
    (let shmid (funcall @shmget ipc-private size shmflg))
    (return shmid)))

(defun @test_shmget_ipc_private () Unit
  (start start:
    (let shmid (funcall @shmget_ipc_private))
    (let null (make-null))
    (let shmflg (bv-typed-literal Int 0))
    (let p1 (funcall @shmat shmid null shmflg))
    (let p2 (funcall @shmat shmid null shmflg))
    (pointer-write Int le p1 (bv 32 10))
    (let r1 (pointer-read Int le p1))
    (let r2 (pointer-read Int le p2))
    (assert! (equal? r1 r2) "Multiple calls to shmget() with the same ID return the same memory segment")
    (return ())))
