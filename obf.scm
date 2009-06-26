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


  (define (read-i43le port)
    (bytevector-s32-ref
      (get-bytevector-n port 4) 0 (endianness little)))


  (define (xchng cns)
    (cons (cdr cns) (car cns)))

  (define (read-frame evn? port)
    (if evn?
      (cons (read-d64le port) (read-i43le port))
      (xchng (cons (read-i43le port) (read-d64le port)))))


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
                         (1 . =<)
                         (2 . =)
                         (3 . >=)
                         (4 . >)))


  (define (process-instr i)
    (let ((a (bitwise-bit-field i 28 31)))
      (if (= a 0)
        ;; s-type
        (list (cdr (assq (bitwise-bit-field i 24 27) s-type-instr))
              ;; only cmpz uses this
              (cdr (assq (bitwise-bit-field i 20 23) imm-op-code))
              (bitwise-bit-field i 0 13))

        ;; d-type
        (list (cdr (assq a d-type-instr))
              (bitwise-bit-field i 14 27)
              (bitwise-bit-field i 0  13)) )))

  )

(import (obf))
(dump-obf "bin1.obf")
(exit)
