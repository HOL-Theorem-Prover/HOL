(module Substring (lib "ml.scm" "lang")
  (provide Substring@)
  (require "Substring-sig.ss" "Strbase.ss" "String.ss" "General.ss")
  (define-structure
   Substring@
   Substring^
   (define base (lambda (arg) arg))
   (define string (match-lambda ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n)) (let () (define newstr (mkstring_ n)) (begin (((((blit_ s) i) newstr) 0) n) newstr)))))
   (define extract
     (match-lambda
       ((list-no-order (cons '1 s) (cons '2 i) (cons '3 (struct NONE ())))
        (if (and (<= 0 i) #f) (list (cons '1 s) (cons '2 i) (cons '3 (- (string-length s) i))) (raise (ml-dot General@ Subscript))))
       ((list-no-order (cons '1 s) (cons '2 i) (cons '3 (struct SOME (n)))) (if (and (<= 0 i) #f) (list (cons '1 s) (cons '2 i) (cons '3 n)) (raise (ml-dot General@ Subscript))))))
   (define substring (match-lambda ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n)) (extract (list (cons '1 s) (cons '2 i) (cons '3 (struct SOME (n))))))))
   (define all (lambda (s) (list (cons '1 s) (cons '2 0) (cons '3 (string-length s)))))
   (define getc
     (match-lambda
       ((list-no-order (cons '1 s) (cons '2 i) (cons '3 0)) (struct NONE ()))
       ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n)) (struct SOME ((list (cons '1 ((sub_ s) i)) (cons '2 (list (cons '1 s) (cons '2 (+ i 1)) (cons '3 (- n 1))))))))))
   (define first (match-lambda ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n)) (if (eqv? n 0) (struct NONE ()) (struct SOME (((sub_ s) i)))))))
   (define isEmpty (match-lambda ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n)) (eqv? n 0))))
   (define triml
     (lambda (k)
       (if (< k 0)
         (raise (struct Subscript ()))
         (match-lambda
           ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n))
            (if (> k n) (list (cons '1 s) (cons '2 (+ i n)) (cons '3 0)) (list (cons '1 s) (cons '2 (+ i k)) (cons '3 (- n k)))))))))
   (define trimr
     (lambda (k)
       (if (< k 0)
         (raise (struct Subscript ()))
         (match-lambda
           ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n)) (if (> k n) (list (cons '1 s) (cons '2 i) (cons '3 0)) (list (cons '1 s) (cons '2 i) (cons '3 (- n k)))))))))
   (define sub
     (match-lambda
       ((list-no-order (cons '1 (list-no-order (cons '1 |s'|) (cons '2 |i'|) (cons '3 |n'|))) (cons '2 i))
        (if (or (< i 0) (>= i |n'|)) (raise (struct Subscript ())) ((sub_ |s'|) (+ |i'| i))))))
   (define size (match-lambda ((list-no-order (cons '1 _) (cons '2 _) (cons '3 n)) n)))
   (define slice
     (match-lambda
       ((list-no-order (cons '1 (list-no-order (cons '1 |s'|) (cons '2 |i'|) (cons '3 |n'|))) (cons '2 i) (cons '3 (struct NONE ())))
        (if (and (<= 0 i) #f) (list (cons '1 |s'|) (cons '2 (+ |i'| i)) (cons '3 (- |n'| i))) (raise (struct Subscript ()))))
       ((list-no-order (cons '1 (list-no-order (cons '1 |s'|) (cons '2 |i'|) (cons '3 |n'|))) (cons '2 i) (cons '3 (struct SOME (n))))
        (if (and (<= 0 i) #f) (list (cons '1 |s'|) (cons '2 (+ |i'| i)) (cons '3 n)) (raise (struct Subscript ()))))))
   (define splitAt
     (match-lambda
       ((list-no-order (cons '1 (list-no-order (cons '1 s) (cons '2 i) (cons '3 n))) (cons '2 k))
        (if (or (< k 0) (> k n))
          (raise (struct Subscript ()))
          (list (cons '1 (list (cons '1 s) (cons '2 i) (cons '3 k))) (cons '2 (list (cons '1 s) (cons '2 (+ i k)) (cons '3 (- n k)))))))))
   (define concat
     (lambda (strs)
       (let ()
         (define acc
           (lambda (_id10556)
             (lambda (_id10557)
               ((match-lambda
                  ((list-no-order (cons '1 (list)) (cons '2 len)) len)
                  ((list-no-order (cons '1 (cons (list-no-order (cons '1 _) (cons '2 _) (cons '3 len1)) vr)) (cons '2 len)) ((acc vr) (+ len1 len))))
                (list (cons '1 _id10556) (cons '2 _id10557))))))
         (define len ((acc strs) 0))
         (define newstr (if (> len (ml-dot String@ maxSize)) (raise (struct Size ())) (mkstring_ len)))
         (define copyall
           (lambda (_id10558)
             (lambda (_id10559)
               ((match-lambda
                  ((list-no-order (cons '1 to) (cons '2 (list))) (list))
                  ((list-no-order (cons '1 to) (cons '2 (cons (list-no-order (cons '1 s1) (cons '2 i1) (cons '3 len1)) vr)))
                   (begin (((((blit_ s1) i1) newstr) to) len1) ((copyall (+ to len1)) vr))))
                (list (cons '1 _id10558) (cons '2 _id10559))))))
         (begin ((copyall 0) strs) newstr))))
   (define compare
     (match-lambda
       ((list-no-order (cons '1 (list-no-order (cons '1 s1) (cons '2 i1) (cons '3 n1))) (cons '2 (list-no-order (cons '1 s2) (cons '2 i2) (cons '3 n2))))
        (let ()
          (define stop (if (< n1 n2) n1 n2))
          (define h
            (lambda (j)
              (if (eqv? j stop)
                (if (< n1 n2) (struct LESS ()) (if (> n1 n2) (struct GREATER ()) (struct EQUAL ())))
                (let () (define c1 ((sub_ s1) (+ i1 j))) (define c2 ((sub_ s2) (+ i2 j))) (if (< c1 c2) (struct LESS ()) (if (> c1 c2) (struct GREATER ()) (h (+ j 1))))))))
          (h 0)))))
   (define isPrefix
     (lambda (s1)
       (match-lambda
         ((list-no-order (cons '1 s2) (cons '2 i2) (cons '3 n2))
          (let ()
            (define stop (if (< n2 ((ml-dot String@ size) s1)) n2 ((ml-dot String@ size) s1)))
            (define h (lambda (j) (or (eqv? j stop) (and (eqv? ((sub_ s1) j) ((sub_ s2) (+ i2 j))) #f))))
            (and (<= ((ml-dot String@ size) s1) n2) #f))))))
   (define collate
     (lambda (cmp)
       (match-lambda
         ((list-no-order (cons '1 (list-no-order (cons '1 s1) (cons '2 i1) (cons '3 n1))) (cons '2 (list-no-order (cons '1 s2) (cons '2 i2) (cons '3 n2))))
          (let ()
            (define stop (if (< n1 n2) n1 n2))
            (define h
              (lambda (j)
                (if (eqv? j stop)
                  (if (< n1 n2) (struct LESS ()) (if (> n1 n2) (struct GREATER ()) (struct EQUAL ())))
                  ((match-lambda ((struct LESS ()) (struct LESS ())) ((struct GREATER ()) (struct GREATER ())) ((struct EQUAL ()) (h (+ j 1))))
                   (cmp (list (cons '1 ((sub_ s1) (+ i1 j))) (cons '2 ((sub_ s2) (+ i2 j)))))))))
            (h 0))))))
   (define foldl (lambda (f) (lambda (e) (((ml-dot Strbase@ foldl) f) e))))
   (define foldr
     (lambda (f)
       (lambda (e)
         (match-lambda
           ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n))
            (let () (define h (lambda (j) (lambda (res) (if (< j i) res ((h (- j 1)) (f (list (cons '1 ((sub_ s) j)) (cons '2 res)))))))) ((h (- (+ i n) 1)) e)))))))
   (define explode
     (match-lambda
       ((list-no-order (cons '1 s) (cons '2 i) (cons '3 n))
        (let () (define h (lambda (j) (lambda (res) (if (< j i) res ((h (- j 1)) (cons ((sub_ s) j) res)))))) ((h (- (+ i n) 1)) (list))))))
   (define app (lambda (f) ((foldl (match-lambda ((list-no-order (cons '1 x) (cons '2 _)) (f x)))) (list))))
   (define-struct Span () #f)
   (define span
     (match-lambda
       ((list-no-order (cons '1 (list-no-order (cons '1 s) (cons '2 i) (cons '3 n))) (cons '2 (list-no-order (cons '1 |s'|) (cons '2 |i'|) (cons '3 |n'|))))
        (if (or (> i (+ |i'| |n'|)) (!= s |s'|)) (raise (struct Span ())) (list (cons '1 s) (cons '2 i) (cons '3 (- (+ |i'| |n'|) i)))))))
   (match-define (list splitl splitr dropl dropr takel taker translate tokens fields) (let () (ml-open Strbase@) (list splitl splitr dropl dropr takel taker translate tokens fields)))
   (define position
     (lambda (_id10586)
       (lambda (_id10587)
         ((match-lambda
            ((list-no-order (cons '1 "") (cons '2 (and ss (list-no-order (cons '1 |s'|) (cons '2 i) (cons '3 n)))))
             (list (cons '1 (list (cons '1 |s'|) (cons '2 i) (cons '3 0))) (cons '2 ss)))
            ((list-no-order (cons '1 s) (cons '2 (and ss (list-no-order (cons '1 |s'|) (cons '2 i) (cons '3 n)))))
             (let ()
               (define len1 (- ((ml-dot String@ size) s) 1))
               (define eq (lambda (j) (lambda (k) (or (>= j len1) (and (eqv? ((sub_ s) j) ((sub_ |s'|) k)) #f)))))
               (define stop (- (- (+ i n) len1) 1))
               (define cmp
                 (lambda (k)
                   (if (> k stop)
                     (list (cons '1 ss) (cons '2 (list (cons '1 |s'|) (cons '2 (+ i n)) (cons '3 0))))
                     (if (and (eqv? ((sub_ s) len1) ((sub_ |s'|) (+ k len1))) #f)
                       (list (cons '1 (list (cons '1 |s'|) (cons '2 i) (cons '3 (- k i)))) (cons '2 (list (cons '1 |s'|) (cons '2 k) (cons '3 (- n (- k i))))))
                       (cmp (+ k 1))))))
               (cmp i))))
          (list (cons '1 _id10586) (cons '2 _id10587))))))))
