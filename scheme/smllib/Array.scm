(module Array (lib "ml.scm" "lang")
  (provide Array@)
  (require "Array-sig.scm"
           )
  (define-structure
    Array@
    Array^
    (define maxLen +inf.0)
    (define array
      (match-lambda
        ((list-no-order (cons '1 n) (cons '2 v))
         (if (or (< n 0)
                 (> n maxLen))
             (raise (struct Size ()))
             (make-vector n v)))))
    (define fromList list->vector)
    (define tabulate
      (match-lambda
        ((list-no-order (cons '1 n) (cons '2 f))
         (if (or (< n 0) (> n maxLen))
             (raise (struct Size ()))
             (let ()
               (define a (make-vector n))
               (define init
                 (lambda (i)
                   (if (>= i n)
                       (list)
                       (begin (vector-set! a i (f i))
                              (init (+ i 1))))))
               (init 0)
               a)))))
    (define length vector-length)
    (define sub
      (match-lambda
        ((list-no-order (cons '1 a) (cons '2 i))
         (if (or (< i 0)
                 (>= i (vector-length a)))
             (raise (struct Subscript ()))
             (vector-ref a i)))))
    (define update
      (match-lambda
        ((list-no-order (cons '1 a) (cons '2 i) (cons '3 v))
         (if (or (< i 0)
                 (>= i (vector-length a)))
             (raise (struct Subscript ()))
             (vector-set! a i)))))
    (define extract
      (match-lambda
        ((list-no-order (cons '1 a) (cons '2 i) (cons '3 slicelen))
         (let ()
           (define n
             ((match-lambda
                ((struct NONE ())
                 (- (vector-length a) i))
                ((struct SOME (n))
                 n))
              slicelen))
           (define newvec
             (if (or (< i 0)
                     (or (< n 0)
                         (> (+ i n) (vector-length a))))
                 (raise (struct Subscript ()))
                 (make-vector n)))
           (define copy
             (lambda (j)
               (if (< j n)
                   (begin (vector-set! newvec j
                                       (vector-ref a (+ i j)))
                          (copy (+ j 1))))))
           (copy 0)
           newvec))))
    (define copy
      (match-lambda
        ((list-no-order (cons 'src a1) (cons 'si i1) (cons 'len len) (cons 'dst a2) (cons 'di i2))
         (let ()
           (define n
             ((match-lambda
                ((struct NONE ())
                 (- (vector-length a1) i1))
                ((struct SOME (k))
                 k))
              len))
           (if (or (< n 0)
                   (or (< i1 0)
                       (or (> (+ i1 n)
                              (vector-length a1))
                           (or (< i2 0)
                               (> (+ i2 n) (vector-length a2))))))
               (raise (struct Subscript ()))
               (if (< i1 i2)
                   (let ()
                     (define hi2lo
                       (lambda (j)
                         (if (>= j 0)
                             (begin (vector-set! a2 (+ i2 j)
                                                 (vector-ref a1 (+ i1 j)))
                                    (hi2lo (- j 1))))))
                     (hi2lo (- n 1)))
                   (let ()
                     (define lo2hi
                       (lambda (j)
                         (if (< j n)
                             (begin (vector-set! a2 (+ i2 j)
                                                 (vector-ref a1 (+ i1 j)))
                                    (lo2hi (+ j 1))))))
                     (lo2hi 0))))))))
    (define copyVec
      (match-lambda
        ((list-no-order (cons 'src a1) (cons 'si i1) (cons 'len len) (cons 'dst a2) (cons 'di i2))
         (let ()
           (define n
             ((match-lambda
                ((struct NONE ())
                 (- (vector-length a1) i1))
                ((struct SOME (k))
                 k))
              len))
           (if (or (< n 0)
                   (or (< i1 0)
                       (or (> (+ i1 n)
                              (vector-length a1))
                           (or (< i2 0)
                               (> (+ i2 n) (vector-length a2))))))
               (raise (struct Subscript ()))
               (let ()
                 (define lo2hi
                   (lambda (j)
                     (if (< j n)
                         (begin (vector-set! a2 (+ i2 j) (vector-ref a1 (+ i1 j)))
                                (lo2hi (+ j 1))) ())))
                 (lo2hi 0)))))))
    (define appi
      (lambda (f)
        (match-lambda
          ((and slice (list-no-order (cons '1 a) (cons '2 i) (cons '3 _)))
           (let ()
             (define loop
               (lambda (stop)
                 (let ()
                   (define lr
                     (lambda (j)
                       (if (< j stop)
                           (begin (f (list (cons '1 j) (cons '2 (vector-ref a j))))
                                  (lr (+ j 1))))))
                   (lr i))))
             (loop (sliceend slice)))))))
    (define sliceend
      (match-lambda
        ((list-no-order (cons '1 a) (cons '2 i) (cons '3 (struct NONE ())))
         (if (or (< i 0)
                 (> i (length a)))
             (raise (struct Subscript ()))
             (length a)))
        ((list-no-order (cons '1 a) (cons '2 i) (cons '3 (struct SOME (n))))
         (if (or (< i 0)
                 (or (< n 0)
                     (> (+ i n) (length a))))
             (raise (struct Subscript ()))
             (+ i n)))))
    (define app
      (lambda (f)
        (lambda (a)
          (let ()
            (define stop (vector-length a))
            (define lr
              (lambda (j)
                (if (< j stop)
                    (begin (f (vector-ref a j))
                           (lr (+ j 1))))))
            (lr 0)))))
    (define foldl
      (lambda (f)
        (lambda (e)
          (lambda (a)
            (let ()
              (define stop (vector-length a))
              (define lr
                (lambda (j)
                  (lambda (res)
                    (if (< j stop)
                        ((lr (+ j 1))
                         (f (list (cons '1 (vector-ref a j))
                                  (cons '2 res))))
                        res))))
              ((lr 0) e))))))
    (define foldr
      (lambda (f)
        (lambda (e)
          (lambda (a)
            (let ()
              (define rl
                (lambda (j)
                  (lambda (res)
                    (if (>= j 0)
                        ((rl (- j 1))
                         (f (list (cons '1 (vector-ref a j))
                                  (cons '2 res))))
                        res))))
              ((rl (- (vector-length a) 1)) e))))))
    (define foldli
      (lambda (f)
        (lambda (e)
          (match-lambda
            ((and slice (list-no-order (cons '1 a) (cons '2 i) (cons '3 _)))
             (let ()
               (define loop
                 (lambda (stop)
                   (let ()
                     (define lr
                       (lambda (j)
                         (lambda (res)
                           (if (< j stop)
                               ((lr (+ j 1))
                                (f (list (cons '1 j)
                                         (cons '2 (vector-ref a j))
                                         (cons '3 res))))
                               res))))
                     ((lr i) e))))
               (loop (sliceend slice))))))))
    (define foldri
      (lambda (f)
        (lambda (e)
          (match-lambda
            ((and slice (list-no-order (cons '1 a) (cons '2 i) (cons '3 _)))
             (let ()
               (define loop
                 (lambda (start)
                   (let ()
                     (define rl
                       (lambda (j)
                         (lambda (res)
                           (if (>= j i)
                               ((rl (- j 1))
                                (f (list (cons '1 j)
                                         (cons '2 (vector-ref a j))
                                         (cons '3 res))))
                               res))))
                     ((rl start) e))))
               (loop (- (sliceend slice) 1))))))))
    (define modifyi
      (lambda (f)
        (match-lambda
          ((and slice (list-no-order (cons '1 a) (cons '2 i) (cons '3 _)))
           (let ()
             (define loop
               (lambda (stop)
                 (let ()
                   (define lr
                     (lambda (j)
                       (if (< j stop)
                           (begin (vector-set! a j (f (list (cons '1 j) (cons '2 (vector-ref a j)))))
                                  (lr (+ j 1))))))
                   (lr i))))
             (loop (sliceend slice)))))))
    (define modify
      (lambda (f)
        (lambda (a)
          (let ()
            (define stop (vector-length a))
            (define lr
              (lambda (j)
                (if (< j stop)
                    (begin (vector-set! a j (f (vector-ref a j)))
                           (lr (+ j 1))))))
            (lr 0)))))
    ))
