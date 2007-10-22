(module String (lib "ml.scm" "lang")
  (provide String@)
  (require "String-sig.ss"
           "Strbase.ss"
           "List.ss")
  
  ;for name conflicts between Scheme and ML
  (require (rename (lib "plt-mzscheme.ss" "lang") mz-substring substring))
  (require (rename (lib "plt-mzscheme.ss" "lang") mz-map map))
  
  (define-structure
    String@
    String^
    (define maxSize +inf.0)
    (define size string-length)
    (define sub
      (match-lambda
        ((list (cons '1 s) (cons '2 i))
         (call-with-exception-handler
          (lambda (x) (raise (struct Subscript ())))
          (lambda () (string-ref s i))))))
    (define substring
      (match-lambda
        ((list (cons '1 s) (cons '2 start) (cons '3 end))
         (call-with-exception-handler
          (lambda (x) (raise (struct Subscript ())))
          (lambda () (mz-substring s start end))))))
    (define extract
      (match-lambda
        ((list (cons '1 s) (cons '2 start) (cons '3 (struct NONE ())))
         (call-with-exception-handler
          (lambda (x) (raise (struct Subscript ())))
          (lambda () (mz-substring s start))))
        ((list (cons '1 s) (cons '2 start) (cons '3 (struct SOME (end))))
         (call-with-exception-handler
          (lambda (x) (raise (struct Subscript ())))
          (lambda () (mz-substring s start end))))))
    (define (concat lst)
      (apply string-append lst))
    (define ^
      (match-lambda
        ((list (cons '1 s1) (cons '2 s2))
         (string-append s1 s2))))
    (define (str c)
      (make-string 1 c))
    (define implode list->string)
    (define explode string->list)
    (define map
      (lambda (f)
        (lambda (s)
          (list->string (mz-map f (string->list s))))))
    (define translate
      (lambda (f)
        (lambda (s)
          (apply string-append
                 (mz-map f (string->list s))))))
    (define tokens (lambda (p) (lambda (s) (((ml-dot List@ map) substring) (((ml-dot Strbase@ tokens) p) (list (cons '1 s) (cons '2 0) (cons '3 (string-length s))))))))
    (define fields (lambda (p) (lambda (s) (((ml-dot List@ map) substring) (((ml-dot Strbase@ fields) p) (list (cons '1 s) (cons '2 0) (cons '3 (string-length s))))))))
    (define
      isPrefix
      (lambda (s1)
        (lambda (s2)
          (let ()
            (define n1 (string-length s1))
            (define n2 (string-length s2))
            (define stop (if (< n1 n2) n1 n2))
            (define h (lambda (j) (or (eqv? j stop) (and (eqv? (string-ref s1 j) (string-ref s2 j)) #f))))
            (and (<= n1 n2) #f)))))
    #;(define
        foldl
        (lambda (f)
          (lambda (e)
            (lambda (s)
              (let ()
                (define stop (string-length s))
                (define h (lambda (j) (lambda (res) (if (>= j stop) res ((h (+ j 1)) (f (list (cons '1 (string-ref s j)) (cons '2 res))))))))
                ((h 0) e))))))
    #;(define
        foldr
        (lambda (f)
          (lambda (e)
            (lambda (s) (let () (define h (lambda (j) (lambda (res) (if (< j 0) res ((h (- j 1)) (f (list (cons '1 (string-ref s j)) (cons '2 res)))))))) ((h (- (string-length s) 1)) e))))))
    (define
      find
      (lambda (p)
        (lambda (s) (let () (define stop (string-length s)) (define h (lambda (j) (if (>= j stop) (struct NONE ()) (if (p (string-ref s j)) (struct SOME (j)) (h (+ j 1)))))) (h 0)))))
    (define
      fromString
      (lambda (s)
        (let ()
          (define getc (lambda (i) (if (< i (string-length s)) (struct SOME ((list (cons '1 (string-ref s i)) (cons '2 (+ i 1))))) (struct NONE ()))))
          (define h
            (lambda (src)
              (lambda (res)
                ((match-lambda
                   ((struct NONE ()) (struct SOME ((list->string ((ml-dot List@ rev) res)))))
                   ((struct SOME ((list-no-order (cons '1 #\\) (cons '2 src1))))
                    ((match-lambda ((struct NONE ()) (struct NONE ())) ((struct SOME ((list-no-order (cons '1 c) (cons '2 src2)))) ((h src2) (cons c res))))
                     (((ml-dot Strbase@ fromMLescape) getc) src1)))
                   ((struct SOME ((list-no-order (cons '1 c) (cons '2 src1)))) ((h src1) (cons c res))))
                 (getc src)))))
          ((h 0) (list)))))
    (define toString (lambda (s) (((ml-dot Strbase@ translate) (ml-dot Strbase@ toMLescape)) (list (cons '1 s) (cons '2 0) (cons '3 (string-length s))))))
    (define fromCString (ml-dot Strbase@ fromCString))
    (define toCString (lambda (s) (((ml-dot Strbase@ translate) (ml-dot Strbase@ toCescape)) (list (cons '1 s) (cons '2 0) (cons '3 (string-length s))))))
    (define compare
      (match-lambda
        ((list (cons '1 c1) (cons '2 c2))
         (cond ((string<? c1 c2)
                (struct LESS ()))
               ((string=? c1 c2)
                (struct EQUAL ()))
               (else
                (struct GREATER ()))))))
    (define <
      (match-lambda
        ((list (cons '1 c1) (cons '2 c2))
         (string<? c1 c2))))
    (define <=
      (match-lambda
        ((list (cons '1 c1) (cons '2 c2))
         (string<=? c1 c2))))
    (define >
      (match-lambda
        ((list (cons '1 c1) (cons '2 c2))
         (string>? c1 c2))))
    (define >=
      (match-lambda
        ((list (cons '1 c1) (cons '2 c2))
         (string>=? c1 c2))))
    (define
      collate
      (lambda (cmp)
        (match-lambda
          ((list-no-order (cons '1 s1) (cons '2 s2))
           (let ()
             (define n1 (string-length s1))
             (define n2 (string-length s2))
             (define stop (if (< n1 n2) n1 n2))
             (define h
               (lambda (j)
                 (if (eqv? j stop)
                     (if (< n1 n2) (struct LESS ()) (if (> n1 n2) (struct GREATER ()) (struct EQUAL ())))
                     ((match-lambda ((struct LESS ()) (struct LESS ())) ((struct GREATER ()) (struct GREATER ())) ((struct EQUAL ()) (h (+ j 1))))
                      (cmp (list (cons '1 (string-ref s1 j)) (cons '2 (string-ref s2 j))))))))
             (h 0))))))
    ))
