(library (obf)
  (export dump-obf)
  (import
    (rnrs)
    (rnrs r5rs)
    (rnrs arithmetic bitwise)
    (rnrs io ports))


  (define (read-d64le port)
    (bytevector-ieee-double-ref
      (get-bytevector-n port 8) 0 (endianness little)))


  (define (read-i32le port)
    (bytevector-s32-ref
      (get-bytevector-n port 4) 0 (endianness little)))


  (define (xchng cns)
    (cons (cdr cns) (car cns)))

  (define (read-frame evn? port)
    (if evn?
      (cons (read-d64le port) (read-i32le port))
      (xchng (cons (read-i32le port) (read-d64le port)))))


  (define (dump-obf file)
    (let ((port (open-file-input-port file)))
      (let loop ((evn #t)
                 (ins 0))
        (if (port-eof? port)
          '()
          (let ((frame (read-frame evn port)))
            (display ins) (display ": ")
            (display (process-instr (cdr frame))) (display ", ")
            (display (car frame))
            (newline)
            (loop (not evn) (+ ins 1)))))
      (close-port port)))



  (define d-type-instr '((1 . add )
                         (2 . sub )
                         (3 . mult)
                         (4 . div )
                         (5 . out )
                         (6 . phi )))

  (define s-type-instr '((0 . noop)
                         (1 . cmpz)
                         (2 . sqrt)
                         (3 . copy)
                         (4 . inpt)))

  (define imm-op-code  '((0 . <)
                         (1 . <=)
                         (2 . =)
                         (3 . >=)
                         (4 . >)))


  (define (process-instr i)
    (let ((a (bitwise-bit-field i 28 31)))
      (if (= a 0)
        ;; s-type
        (list (cdr (assq (bitwise-bit-field i 24 27) s-type-instr))
              ;; only cmpz uses this
              (cdr (assq (bitwise-bit-field i 21 23) imm-op-code))
              (bitwise-bit-field i 0 13))

        ;; d-type
        (list (cdr (assq a d-type-instr))
              (bitwise-bit-field i 14 27)
              (bitwise-bit-field i 0  13)) )))






  (define-record-type orbit-vm (fields
                                 mem
                                 inp
                                 out
                                 (mutable status)
                                 pc))

  (define make-mem make-eq-hashtable)
  (define (mem-set! mem addr v) (hashtable-set! mem addr v))
  (define (mem-get  mem addr) (hashtable-ref mem addr))

  (define (make-vm)
    (make-orbit-vm
      (make-mem) ; mem
      (make-mem) ; input
      (make-mem) ; output
      #f         ; status
      0          ; program counter
      ))


  (define (alist->instr-set a) a)
  (define (instr-set-get set idx) (cdr (assq set idx)))

  (define (make-instr name code) (cons name code))
  (define (instr-name instr) (car instr))
  (define (instr-code instr) (cdr instr))


  ;; instruction operations
  (define (mem vm addr)    (mem-get (orbit-vm-mem vm) addr))
  (define (mem! vm addr v) (mem-set! (orbit-vm-mem vm) addr v))
  (define (inp vm addr)    (mem-get (orbit-vm-inp vm) addr))
  (define (out! vm addr v) (mem-set! (orbit-vm-out vm) addr v))
  (define (status vm) (orbit-vm-status vm))
  (define (status! vm x) (orbit-vm-status-set! vm x))
  (define (op-instr op) (lambda (vm rd r1 r2)
                          (mem! vm rd (op (mem vm r1)
                                          (mem vm r2)))))

  (define eps 1.0e-20)
  (define (=0.0 x) (< (abs x) eps))
  (define (div-op a b)
    (if (=0.0 b)
      0.0
      (/ a b)))

  (define d-type-instr-set (alist->instr-set 
                             `((1 . ,(make-instr 'add (op-instr +)))
                               (2 . ,(make-instr 'sub (op-instr -)))
                               (3 . ,(make-instr 'mul (op-instr *)))
                               (4 . ,(make-instr 'div (op-instr div-op)))
                               (5 . ,(make-instr 'out (lambda (vm rd r1 r2)
                                                        (out! vm r1 
                                                              (mem vm r2)))))
                               (6 . ,(make-instr 'phi (lambda (vm rd r1 r2) 
                                                        (if (status vm)
                                                          (mem! vm rd
                                                                (mem vm r1))
                                                          (mem! vm rd
                                                                (mem vm r2))))))
                               )))

  (define s-type-instr-set (alist->instr-set
                             `((0 . ,(make-instr 'noop (lambda (vm rd imm r1)
                                                         #f)))
                               (1 . ,(make-instr 'cmpz (lambda (vm rd imm r1)
                                                         (status! 
                                                           vm
                                                           (imm (mem vm r1))))))
                               (2 . ,(make-instr 'sqrt (lambda (vm rd imm r1)
                                                         (mem!
                                                           vm rd
                                                           (sqrt (mem r1))))))
                               (3 . ,(make-instr 'copy (lambda (vm rd imm r1)
                                                         (mem! vm rd
                                                               (mem r1)))))
                               (4 . ,(make-instr 'inpt (lambda (vm rd imm r1)
                                                         (mem! vm rd
                                                               (inp vm r1)))))
                               )))


  (define (op0.0 op) (lambda (x) (op x 0.0)))

  (define cmpz-imm-ops (alist->instr-set
                         `((0 . ,(make-instr '<0.0  (op0.0 <)))
                           (1 . ,(make-instr '<=0.0 (op0.0 <=)))
                           (2 . ,(make-instr '=0.0  =0.0))
                           (3 . ,(make-instr '>=0.0 (op0.0 >=)))
                           (4 . ,(make-instr '>0.0  (op0.0 >))))))

  (define (step vm code)
    '())

  ;(define (load-obj port)
    ;(let loop ((evn #t)
               ;(ins 0))
      ;(if (port-eof? port)
      ;)
    ;)

  )

(import (obf))
(dump-obf "bin1.obf")
(exit)
