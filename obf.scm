(library (obf)
  (export
    hohmann-1001 test-run)
  (import
    (rnrs)
    (rnrs r5rs)
    (rnrs arithmetic bitwise)
    (rnrs bytevectors)
    (rnrs io ports))


  ;;
  ;; virtual machine
  ;;
  (define (read-d64le port)
    (bytevector-ieee-double-ref
      (get-bytevector-n port 8) 0 (endianness little)))

  (define (write-d64le port val)
    (let ((v (make-bytevector 8 0)))
      (bytevector-ieee-double-set! v 0 val (endianness little))
      (put-bytevector port v)))

  (define (read-i32le port)
    (bytevector-s32-ref
      (get-bytevector-n port 4) 0 (endianness little)))

  (define (write-i32le port val)
    (let ((v (make-bytevector 4 0)))
      (bytevector-u32-set! v 0 val (endianness little))
      (put-bytevector port v)))

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
  (define (inp vm addr)    (mem-get (orbit-vm-inp vm) addr))
  (define (inp! vm addr v) (mem-set! (orbit-vm-inp vm) addr v))
  (define (out! vm addr v) (mem-set! (orbit-vm-out vm) addr v))
  (define (status vm)      (orbit-vm-status vm))
  (define (status! vm x)   (orbit-vm-status-set! vm x))

  (define (op-instr op) (lambda (vm rd r1 r2)
                          (mem! vm rd (op (mem vm r1)
                                          (mem vm r2)))))

  (define eps 1.0e-20)
  (define (=0.0 x) (< (abs x) eps))
  (define (=e. a b eps) (< (abs (- a b)) eps))
  (define (=. a b) (< (abs (- a b)) eps))
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




  ;;
  ;; visualization
  ;;
  (define (string-join del strings)
    (fold-left (lambda (a b)
                 (if (string=? a "")
                   b
                   (string-append a del b))) "" strings))

  (define (plot-init)
    (display "set parametric")
    (newline))

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



  ;;
  ;; vector math
  ;;
  (define (v x y)
    (vector x y))

  (define (vx v) (vector-ref v 0))
  (define (vy v) (vector-ref v 1))

  (define (v+ a b)
    (vector
      (+ (vector-ref a 0) (vector-ref b 0))
      (+ (vector-ref a 1) (vector-ref b 1))))

  (define (v- a b)
    (v+ a (v* -1 b)))

  (define (v. a b) ;; dot product
    (+
      (* (vector-ref a 0) (vector-ref b 0))
      (* (vector-ref a 1) (vector-ref b 1))))

  (define (v* s a) ;; mul scalar
    (vector
      (* s (vector-ref a 0))
      (* s (vector-ref a 1))))

  (define (vm a) ;; maginute
    (sqrt (v. a a)))

  (define (vn a) ;; normalize
    (v* (/ 1 (vm a)) a))

  (define (v-cos a b)
    (/ (v. a b) (* (vm a) (vm b))))

  (define (va a b)
    (acos (v-cos a b)))

  (define (v-tangent a) ;; rotated counter clockwize 90
    (vector
      (* -1 (vector-ref a 1))
      (vector-ref a 0)))

  (define (v-invert a)
    (v* -1 a))

  (define (v-col a b)
    (cond
      ((or (=0.0 (vy a)) (=0.0 (vy b))) #f)
      ((and (=0.0 (vy a)) (=0.0 (vy b))) #t)
      (else (=. (/ (vx a) (vy a)) (/ (vx b) (vy b))) )))
  ;; or simpler, but with more float calculations
    ;(=. (abs (v. a b)) (* (vm a) (vm b))))


  ;;
  ;; physics
  ;;
  (define earth-radius 6.357e6) ; m
  (define g-constant 6.67428e-11) ; m^3 1/kg 1/s^2
  (define earth-mass 6.0e24)      ; kg
  ;(define earth-g-param 398600.4418)
  (define earth-g-param (* earth-mass g-constant))
  (define dt 1)                 ; s
  (define pi (acos -1))


  ;;
  ;; problems
  ;;

  (define team-id 138)
  (define magic-nr #xcafebabe)


  (define-syntax let-al
    (syntax-rules ()
      ((_ al ((n idx) ...) body ...)
       (let ((n (cdr (assq idx al))) ...)
         body ...))))

  (define (drop-same prev-o curr-o)
    (filter (lambda (o)
              (let ((po (assq (car o) prev-o)))
                (or (not po)
                    (not (= (cdr o) (cdr po)))) )) curr-o))


  (define (with-problem-output-file file scenario-id proc)
    (let ((port (open-file-output-port file (file-options no-fail))))
      ;; header
      (write-i32le port magic-nr)
      (write-i32le port team-id)
      (write-i32le port scenario-id)
      (proc port)
      (close-port port)))

  (define (write-frame port time-step ports)
    (write-i32le port time-step)
    (write-i32le port (length ports))
    (for-each (lambda (p)
                (write-i32le port (car p))
                (write-d64le port (cdr p))) ports))


  (define (solve-problem file scenario proc)
    (let-values (((vm code) (load-vm-from-file file)))
      (let ((time 0)
            (inp  '()))
        (with-problem-output-file
          (string-append file ".osf")
          scenario
          (lambda (o-port)

            (proc (lambda (input-ports)
                    (let ((o (time-step! vm code input-ports))
                          (d (drop-same inp input-ports)))
                      (if (not (null? d))
                        (begin
                          ;; write out
                          (write-frame o-port time d)
                          (set! inp input-ports)))
                      (set! time (+ time 1))
                      o)))
            ;; write out final frame
            (write-frame o-port time '())
            ))
        )))

  ;(define (solve-problem file proc)
    ;(let-values (((vm code) (load-vm-from-file file)))
      ;(proc (lambda (input-ports) (time-step! vm code input-ports)))))


  (define (hohmann-gp-vis sx sy fl sc tr . more-plots)
    (apply plot (append
                  (list (plot-circle 0 0 earth-radius "Earth")
                        (plot-circle sx sy (/ earth-radius 30) "Satallite")
                        (plot-circle 0 0 tr "Target orbit")
                        (plot-info "Fuel" fl)
                        (plot-info "Score" sc))
                  more-plots)))



  ;;
  ;; from: http://www.braeunig.us/space/orbmech.htm
  ;;
  (define (atx r1 r2) (/ (+ r1 r2) 2.0))

  (define (velocity-initial-a r1)
    (sqrt (/ earth-g-param r1)))

  (define (velocity-initial-b r2)
    (sqrt (/ earth-g-param r2)))

  (define (velocity-on-transfer-a r1 r2)
    (sqrt (* earth-g-param (- (/ 2.0 r1) (/ 1.0 (atx r1 r2))))))

  (define (velocity-on-transfer-b r1 r2)
    (sqrt (* earth-g-param (- (/ 2.0 r2) (/ 1.0 (atx r1 r2))))))

  ;; this for the first velocity change
  (define (velocity-initial-change-a r1 r2)
    (- (velocity-on-transfer-a r1 r2)
       (velocity-initial-a r1)))

  ;; this is for the second velocity change
  (define (velocity-initial-change-b r1 r2)
    (- (velocity-initial-b r2)
       (velocity-on-transfer-b r1 r2)))

  (define (time-period r1 r2)
    (/ (sqrt (/ (+ r1 r2) (* 8.0 earth-g-param))) 2.0))

  (define (delta-velocity org pos vel)
    (v* vel (vn (v-tangent (v- pos org)))))



  ; 0 - score
  ; 1 - fuel remaining
  ; 2 - sx
  ; 3 - sy
  ; 4 - target orbit radius
  (define (hohmann-1001)
    (plot-init)
    (solve-problem
      "bin1.obf"
      1001
      (lambda (step!)
        (define (s vx vy) (step! `((#x3e80 . 1001) (2 . ,vx) (3 . ,vy))))

        ;; read initial values
        (let-al (s 0 0) ((sx 2) (sy 3) (fl 1) (sc 0) (r2 4))
                (let* ((pos  (v sx sy))
                       (r1   (vm pos))
                       (dvm1 (velocity-initial-change-a r1 r2))
                       (dvm2 (velocity-initial-change-b r1 r2))
                       (dvv1 (delta-velocity (v 0 0) pos dvm1))
                       (dvx  (vx dvv1))
                       (dvy  (vy dvv1)))

                  (s dvx dvy) ;; first thrust

                  (let iterate ((t 1) (delta-vx 0) (delta-vy 0))
                    (let-al
                      (s delta-vx delta-vy) ((sx 2) (sy 3) (fl 1) (sc 0))
                      (if (= 0 (mod t 20)) (hohmann-gp-vis sx sy fl sc r2 ))
                      (cond
                        ((=e. pi (va pos (v sx sy)) 1e-4)
                         (let ((dvv2 (delta-velocity (v 0 0) (v sx sy)
                                                     (/ dvm2 4) )))
                           (iterate (+ t 1) (vx dvv2) (vy dvv2)))
                         )
                        ((> sc 0.0) (plot (plot-info "Score" sc))
                                    (display "pause mouse") (newline))
                        (else (iterate (+ t 1) 0 0))))
                    )))
        )))


  (define test-run hohmann-1001)

  )



(import (obf))
(test-run)

