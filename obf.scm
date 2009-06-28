(library (obf)
  (export
    test-run)
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

  (define frame-instr cdr)
  (define frame-mem   car)


  (define-record-type orbit-vm (fields
                                 mem
                                 inp
                                 out
                                 (mutable status)
                                 ))

  (define make-mem make-eq-hashtable)
  (define (mem-set! mem addr v) (hashtable-set! mem addr v))
  (define (mem-get  mem addr) (hashtable-ref mem addr 0.0))
  (define (mem-addresses mem) (vector->list (hashtable-keys mem)))

  (define (make-vm)
    (make-orbit-vm
      (make-mem) ; mem
      (make-mem) ; input
      (make-mem) ; output
      #f         ; status
      ))


  (define (alist->instr-set a) a)
  (define (instr-set-get set idx) (cdr (assq idx set)))

  (define (make-instr name code) (cons name code))
  (define instr-name car)
  (define instr-code cdr)


  ;; instruction operations
  (define (mem vm addr)    (mem-get (orbit-vm-mem vm) addr))
  (define (mem! vm addr v) (mem-set! (orbit-vm-mem vm) addr v))
  (define (inp vm addr)    #;(begin (display "Input needed ") (display addr) (newline))  (mem-get (orbit-vm-inp vm) addr))
  (define (inp! vm addr v) (mem-set! (orbit-vm-inp vm) addr v))
  (define (out! vm addr v) #;(begin (display "Outputing ") (display addr) (display ": ") (display v) (newline)) (mem-set! (orbit-vm-out vm) addr v))
  (define (status vm)      (orbit-vm-status vm))
  (define (status! vm x)   (orbit-vm-status-set! vm x))

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
                                                           (sqrt (mem vm r1))))))
                               (3 . ,(make-instr 'copy (lambda (vm rd imm r1)
                                                         (mem! vm rd
                                                               (mem vm r1)))))
                               (4 . ,(make-instr 'inpt (lambda (vm rd imm r1)
                                                         (mem! vm rd
                                                               (inp vm r1)))))
                               )))


  (define (op0.0 op) (lambda (x) (op x 0.0)))

  (define cmpz-imm-ops-set (alist->instr-set
                             `((0 . ,(make-instr '<0.0  (op0.0 <)))
                               (1 . ,(make-instr '<=0.0 (op0.0 <=)))
                               (2 . ,(make-instr '=0.0  =0.0))
                               (3 . ,(make-instr '>=0.0 (op0.0 >=)))
                               (4 . ,(make-instr '>0.0  (op0.0 >))))))

  (define-record-type s-type-code
    (fields instr imm r1 rd))

  (define-record-type d-type-code
    (fields instr r1 r2 rd))

  (define (load-instr i rd)
    (let ((op-code (bitwise-bit-field i 28 32)))
      (if (= op-code 0) ;; s-type
        (let ((s-op-code (bitwise-bit-field i 24 28))
              (imm-code  (bitwise-bit-field i 21 24))
              (r1        (bitwise-bit-field i 0  14)))
          (make-s-type-code
            (instr-set-get s-type-instr-set s-op-code)
            (instr-set-get cmpz-imm-ops-set imm-code)
            r1 rd))
        ;; d-type
        (let ((r1 (bitwise-bit-field i 14 28))
              (r2 (bitwise-bit-field i 0  14)))
          (make-d-type-code
            (instr-set-get d-type-instr-set op-code)
            r1 r2 rd)))))


  (define (load-obj port)
    (let loop ((evn #t)
               (ins 0)
               (code '()))
      (if (port-eof? port)
        (reverse code)
        (let ((frame (read-frame evn port)))
          (loop (not evn)
                (+ ins 1)
                (cons (cons ins frame) code))))))

  (define (load-obj-from-file file)
    (let* ((p (open-file-input-port file))
           (o (load-obj p)))
      (close-port p)
      o))

  (define (obj->memory-alist obj)
    (map (lambda (i) (cons (car i) (frame-mem (cdr i)))) obj))

  (define (obj->instrs-alist obj)
    (map (lambda (i) (cons (car i) (frame-instr (cdr i)))) obj))

  (define (compile-instrs ia)
    (map (lambda (i) (load-instr (cdr i) (car i))) ia))

  (define (init-memory! vm mem)
    (for-each (lambda (x) (mem! vm (car x) (cdr x))) mem))


  (define (interpret-run-instr-code vm instr)
    (cond
      ((s-type-code? instr) ((instr-code (s-type-code-instr instr))
                             vm (s-type-code-rd instr)
                             (instr-code (s-type-code-imm instr))
                             (s-type-code-r1 instr)))
      ((d-type-code? instr) ((instr-code (d-type-code-instr instr))
                             vm (d-type-code-rd instr)
                             (d-type-code-r1 instr)
                             (d-type-code-r2 instr))) ))


  (define (interpret-step-vm vm instrs)
    (for-each (lambda (i) (interpret-run-instr-code vm i)) instrs))



  (define (time-step! vm code input)
    (for-each (lambda (i) (inp! vm (car i) (cdr i))) input)

    (interpret-step-vm vm code)

    (map (lambda (a)
           (cons a (mem-get (orbit-vm-out vm) a)))
         (mem-addresses (orbit-vm-out vm))))


  (define (load-vm-from-file file)
    (let ((vm (make-vm))
          (obj (load-obj-from-file file)))
      (init-memory! vm (obj->memory-alist obj))
      (let ((code (compile-instrs (obj->instrs-alist obj))))
        (values vm code))))


  ;; physics
  (define earth-radius 6.357e6) ; meters
  (define dt 1) ; seconds

  (define (string-join del strings)
    (fold-left (lambda (a b)
                 (if (string=? a "")
                   b
                   (string-append a del b))) "" strings))

  (define (plot . objs)
    (display "plot ")
    (display (string-join "," objs))
    (newline))


  (define (plot-circle x y radius caption)
    (let ((sx (number->string x))
          (sy (number->string y))
          (sr (number->string radius)))
      (string-append
        "sin(t)*" sr "+" sx ","
        "cos(t)*" sr "+" sy " "
        "title \""
        "(" sx ", " sy "), " sr " - " caption "\"")))

  (define (plot-info caption val)
    (string-append
      "0,0 title \"" (number->string val) " - " caption "\""))


  (define (hohmann-gp-vis op)
    ; 0 - score
    ; 1 - fuel remaining
    ; 2 - sx
    ; 3 - sy
    ; 4 - target orbit radius
    (let ((sx (cdr (assq 2 op)))
          (sy (cdr (assq 3 op)))
          (fl (cdr (assq 1 op)))
          (sc (cdr (assq 0 op)))
          (tr (cdr (assq 4 op))) )

      (plot
        (plot-circle 0 0 earth-radius "Earth")
        (plot-circle sx sy (/ earth-radius 30) "Satallite")
        (plot-circle 0 0 tr "Target radius")
        (plot-info "Fuel" fl)
        (plot-info "Score" sc)
        )
      ))


  (define (test-run)
    (let-values (((vm code) (load-vm-from-file "bin1.obf")))
      (display "set parametric")(newline)
      (do ((i 0 (+ i 1))) ((> i 20000) i)
        (let ((results (time-step! vm code '((#x3e80 . 1001)
                                             (3 . 0)
                                             (2 . 0))) ))
          (if (= (mod i 50) 0)
            (begin
              (hohmann-gp-vis results) (newline) ))
          ;(display "pause 0.0001") (newline)
          )
        )))


  )

(import (obf))
(test-run)

