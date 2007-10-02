(module Binarymap (lib "ml.scm" "lang")
  (provide Binarymap@)
  (require "Binarymap-sig.ss")
  (define-structure
   Binarymap@
   Binarymap^
   (define-struct NotFound () #f)
   (define wt (lambda (i) (* 3 i)))
   (define-struct DICT (content) #f)
   (define-struct E () #f)
   (define-struct T (content) #f)
   (define treeSize (match-lambda ((struct E ()) 0) ((struct T ((list-no-order (cons 'cnt cnt) g11266 ...))) cnt)))
   (define numItems (match-lambda ((struct DICT ((list-no-order (cons '1 _) (cons '2 t)))) (treeSize t))))
   (match-define
     (list mkDict insert find peek remove listItems revapp app foldr foldl map transform)
     (let ()
       (define N
         (match-lambda
           ((list-no-order (cons '1 k) (cons '2 v) (cons '3 (struct E ())) (cons '4 (struct E ())))
            (struct
              T
              ((list (cons 'key k) (cons 'value v) (cons 'cnt 1) (cons 'left (struct E ())) (cons 'right (struct E ()))))))
           ((list-no-order (cons '1 k) (cons '2 v) (cons '3 (struct E ())) (cons '4 (and r (struct T (n)))))
            (struct
              T
              ((list
                (cons 'key k)
                (cons 'value v)
                (cons 'cnt (+ 1 ((match-lambda ((list-no-order (cons 'cnt _id10545) g11267 ...) _id10545)) n)))
                (cons 'left (struct E ()))
                (cons 'right r)))))
           ((list-no-order (cons '1 k) (cons '2 v) (cons '3 (and l (struct T (n)))) (cons '4 (struct E ())))
            (struct
              T
              ((list
                (cons 'key k)
                (cons 'value v)
                (cons 'cnt (+ 1 ((match-lambda ((list-no-order (cons 'cnt _id10546) g11268 ...) _id10546)) n)))
                (cons 'left l)
                (cons 'right (struct E ()))))))
           ((list-no-order (cons '1 k) (cons '2 v) (cons '3 (and l (struct T (n)))) (cons '4 (and r (struct T (n1)))))
            (struct
              T
              ((list
                (cons 'key k)
                (cons 'value v)
                (cons
                 'cnt
                 (+
                  (+ 1 ((match-lambda ((list-no-order (cons 'cnt _id10547) g11269 ...) _id10547)) n))
                  ((match-lambda ((list-no-order (cons 'cnt _id10548) g11270 ...) _id10548)) n1)))
                (cons 'left l)
                (cons 'right r)))))))
       (define single_L
         (match-lambda
           ((list-no-order
              (cons '1 a)
              (cons '2 av)
              (cons '3 x)
              (cons '4 (struct T ((list-no-order (cons 'key b) (cons 'value bv) (cons 'left y) (cons 'right z) g11271 ...)))))
            (N (list (cons '1 b) (cons '2 bv) (cons '3 (N (list (cons '1 a) (cons '2 av) (cons '3 x) (cons '4 y)))) (cons '4 z))))
           (_ (raise (struct Match ())))))
       (define single_R
         (match-lambda
           ((list-no-order
              (cons '1 b)
              (cons '2 bv)
              (cons '3 (struct T ((list-no-order (cons 'key a) (cons 'value av) (cons 'left x) (cons 'right y) g11272 ...))))
              (cons '4 z))
            (N (list (cons '1 a) (cons '2 av) (cons '3 x) (cons '4 (N (list (cons '1 b) (cons '2 bv) (cons '3 y) (cons '4 z)))))))
           (_ (raise (struct Match ())))))
       (define double_L
         (match-lambda
           ((list-no-order
              (cons '1 a)
              (cons '2 av)
              (cons '3 w)
              (cons
               '4
               (struct
                 T
                 ((list-no-order
                    (cons 'key c)
                    (cons 'value cv)
                    (cons
                     'left
                     (struct T ((list-no-order (cons 'key b) (cons 'value bv) (cons 'left x) (cons 'right y) g11273 ...))))
                    (cons 'right z)
                    g11274
                    ...)))))
            (N
             (list
              (cons '1 b)
              (cons '2 bv)
              (cons '3 (N (list (cons '1 a) (cons '2 av) (cons '3 w) (cons '4 x))))
              (cons '4 (N (list (cons '1 c) (cons '2 cv) (cons '3 y) (cons '4 z)))))))
           (_ (raise (struct Match ())))))
       (define double_R
         (match-lambda
           ((list-no-order
              (cons '1 c)
              (cons '2 cv)
              (cons
               '3
               (struct
                 T
                 ((list-no-order
                    (cons 'key a)
                    (cons 'value av)
                    (cons 'left w)
                    (cons
                     'right
                     (struct T ((list-no-order (cons 'key b) (cons 'value bv) (cons 'left x) (cons 'right y) g11275 ...))))
                    g11276
                    ...))))
              (cons '4 z))
            (N
             (list
              (cons '1 b)
              (cons '2 bv)
              (cons '3 (N (list (cons '1 a) (cons '2 av) (cons '3 w) (cons '4 x))))
              (cons '4 (N (list (cons '1 c) (cons '2 cv) (cons '3 y) (cons '4 z)))))))
           (_ (raise (struct Match ())))))
       (define T1
         (match-lambda
           ((list-no-order (cons '1 k) (cons '2 v) (cons '3 (struct E ())) (cons '4 (struct E ())))
            (struct
              T
              ((list (cons 'key k) (cons 'value v) (cons 'cnt 1) (cons 'left (struct E ())) (cons 'right (struct E ()))))))
           ((list-no-order
              (cons '1 k)
              (cons '2 v)
              (cons '3 (struct E ()))
              (cons '4 (and r (struct T ((list-no-order (cons 'right (struct E ())) (cons 'left (struct E ())) g11277 ...))))))
            (struct T ((list (cons 'key k) (cons 'value v) (cons 'cnt 2) (cons 'left (struct E ())) (cons 'right r)))))
           ((list-no-order
              (cons '1 k)
              (cons '2 v)
              (cons '3 (and l (struct T ((list-no-order (cons 'right (struct E ())) (cons 'left (struct E ())) g11278 ...)))))
              (cons '4 (struct E ())))
            (struct T ((list (cons 'key k) (cons 'value v) (cons 'cnt 2) (cons 'left l) (cons 'right (struct E ()))))))
           ((and p
                 (list-no-order
                   (cons '1 _)
                   (cons '2 _)
                   (cons '3 (struct E ()))
                   (cons '4 (struct T ((list-no-order (cons 'left (struct T (_))) (cons 'right (struct E ())) g11279 ...))))))
            (double_L p))
           ((and p
                 (list-no-order
                   (cons '1 _)
                   (cons '2 _)
                   (cons '3 (struct T ((list-no-order (cons 'left (struct E ())) (cons 'right (struct T (_))) g11280 ...))))
                   (cons '4 (struct E ()))))
            (double_R p))
           ((and p
                 (list-no-order
                   (cons '1 _)
                   (cons '2 _)
                   (cons '3 (struct E ()))
                   (cons
                    '4
                    (struct
                      T
                      ((list-no-order
                         (cons 'left (struct T ((list-no-order (cons 'cnt ln) g11281 ...))))
                         (cons 'right (struct T ((list-no-order (cons 'cnt rn) g11282 ...))))
                         g11283
                         ...))))))
            (if (< ln rn) (single_L p) (double_L p)))
           ((and p
                 (list-no-order
                   (cons '1 _)
                   (cons '2 _)
                   (cons
                    '3
                    (struct
                      T
                      ((list-no-order
                         (cons 'left (struct T ((list-no-order (cons 'cnt ln) g11284 ...))))
                         (cons 'right (struct T ((list-no-order (cons 'cnt rn) g11285 ...))))
                         g11286
                         ...))))
                   (cons '4 (struct E ()))))
            (if (> ln rn) (single_R p) (double_R p)))
           ((and p
                 (list-no-order
                   (cons '1 _)
                   (cons '2 _)
                   (cons '3 (struct E ()))
                   (cons '4 (struct T ((list-no-order (cons 'left (struct E ())) g11287 ...))))))
            (single_L p))
           ((and p
                 (list-no-order
                   (cons '1 _)
                   (cons '2 _)
                   (cons '3 (struct T ((list-no-order (cons 'right (struct E ())) g11288 ...))))
                   (cons '4 (struct E ()))))
            (single_R p))
           ((and p
                 (list-no-order
                   (cons '1 k)
                   (cons '2 v)
                   (cons '3 (and l (struct T ((list-no-order (cons 'cnt ln) (cons 'left ll) (cons 'right lr) g11289 ...)))))
                   (cons '4 (and r (struct T ((list-no-order (cons 'cnt rn) (cons 'left rl) (cons 'right rr) g11290 ...)))))))
            (if (>= rn (wt ln))
              (let () (define rln (treeSize rl)) (define rrn (treeSize rr)) (if (< rln rrn) (single_L p) (double_L p)))
              (if (>= ln (wt rn))
                (let () (define lln (treeSize ll)) (define lrn (treeSize lr)) (if (< lrn lln) (single_R p) (double_R p)))
                (struct T ((list (cons 'key k) (cons 'value v) (cons 'cnt (+ (+ ln rn) 1)) (cons 'left l) (cons 'right r)))))))))
       (match-define
         (list delete1)
         (let ()
           (define min
             (match-lambda
               ((struct T ((list-no-order (cons 'left (struct E ())) (cons 'key key) (cons 'value value) g11291 ...)))
                (list (cons '1 key) (cons '2 value)))
               ((struct T ((list-no-order (cons 'left left) g11292 ...))) (min left))
               (_ (raise (struct Match ())))))
           (define delmin
             (match-lambda
               ((struct T ((list-no-order (cons 'left (struct E ())) (cons 'right right) g11293 ...))) right)
               ((struct T ((list-no-order (cons 'key key) (cons 'value value) (cons 'left left) (cons 'right right) g11294 ...)))
                (T1 (list (cons '1 key) (cons '2 value) (cons '3 (delmin left)) (cons '4 right))))
               (_ (raise (struct Match ())))))
           (list
            (match-lambda
              ((list-no-order (cons '1 (struct E ())) (cons '2 r)) r)
              ((list-no-order (cons '1 l) (cons '2 (struct E ()))) l)
              ((list-no-order (cons '1 l) (cons '2 r))
               (let ()
                 (match-define (list-no-order (cons '1 mink) (cons '2 minv)) (min r))
                 (T1 (list (cons '1 mink) (cons '2 minv) (cons '3 l) (cons '4 (delmin r))))))))))
       (list
        (lambda (cmpKey) (struct DICT ((list (cons '1 cmpKey) (cons '2 (struct E ()))))))
        (match-lambda
          ((list-no-order (cons '1 (struct DICT ((list-no-order (cons '1 cmpKey) (cons '2 t))))) (cons '2 x) (cons '3 v))
           (let ()
             (define ins
               (match-lambda
                 ((struct E ())
                  (struct
                    T
                    ((list (cons 'key x) (cons 'value v) (cons 'cnt 1) (cons 'left (struct E ())) (cons 'right (struct E ()))))))
                 ((struct
                    T
                    ((and set
                          (list-no-order (cons 'key key) (cons 'left left) (cons 'right right) (cons 'value value) g11295 ...))))
                  ((match-lambda
                     ((struct GREATER ()) (T1 (list (cons '1 key) (cons '2 value) (cons '3 (ins left)) (cons '4 right))))
                     ((struct LESS ()) (T1 (list (cons '1 key) (cons '2 value) (cons '3 left) (cons '4 (ins right)))))
                     (_
                      (struct
                        T
                        ((list
                          (cons 'key x)
                          (cons 'value v)
                          (cons 'left left)
                          (cons 'right right)
                          (cons 'cnt ((match-lambda ((list-no-order (cons 'cnt _id10559) g11296 ...) _id10559)) set)))))))
                   (cmpKey (list (cons '1 key) (cons '2 x)))))))
             (struct DICT ((list (cons '1 cmpKey) (cons '2 (ins t))))))))
        (match-lambda
          ((list-no-order (cons '1 (struct DICT ((list-no-order (cons '1 cmpKey) (cons '2 t))))) (cons '2 x))
           (let ()
             (define mem
               (match-lambda
                 ((struct E ()) (raise (struct NotFound ())))
                 ((struct T ((and n (list-no-order (cons 'key key) (cons 'left left) (cons 'right right) g11297 ...))))
                  ((match-lambda
                     ((struct GREATER ()) (mem right))
                     ((struct LESS ()) (mem left))
                     (_ ((match-lambda ((list-no-order (cons 'value _id10562) g11298 ...) _id10562)) n)))
                   (cmpKey (list (cons '1 x) (cons '2 key)))))))
             (mem t))))
        (lambda (arg)
          (with-handlers
            (((match-lambda ((struct NotFound ()) #t)) (match-lambda ((struct NotFound ()) (struct NONE ())))))
            (struct SOME ((find arg)))))
        (match-lambda
          ((list-no-order (cons '1 (struct DICT ((list-no-order (cons '1 cmpKey) (cons '2 t))))) (cons '2 x))
           (let ()
             (define rm
               (match-lambda
                 ((struct E ()) (raise (struct NotFound ())))
                 ((and set
                       (struct
                         T
                         ((list-no-order (cons 'key key) (cons 'left left) (cons 'right right) (cons 'value value) g11299 ...))))
                  ((match-lambda
                     ((struct GREATER ())
                      (let ()
                        (match-define (list-no-order (cons '1 left1) (cons '2 v)) (rm left))
                        (list (cons '1 (T1 (list (cons '1 key) (cons '2 value) (cons '3 left1) (cons '4 right)))) (cons '2 v))))
                     ((struct LESS ())
                      (let ()
                        (match-define (list-no-order (cons '1 right1) (cons '2 v)) (rm right))
                        (list (cons '1 (T1 (list (cons '1 key) (cons '2 value) (cons '3 left) (cons '4 right1)))) (cons '2 v))))
                     (_ (list (cons '1 (delete1 (list (cons '1 left) (cons '2 right)))) (cons '2 value))))
                   (cmpKey (list (cons '1 key) (cons '2 x)))))))
             (match-define (list-no-order (cons '1 newtree) (cons '2 valrm)) (rm t))
             (list (cons '1 (struct DICT ((list (cons '1 cmpKey) (cons '2 newtree))))) (cons '2 valrm)))))
        (match-lambda
          ((struct DICT ((list-no-order (cons '1 _) (cons '2 d))))
           (let ()
             (define d2l
               (lambda (_id10568)
                 (lambda (_id10569)
                   ((match-lambda
                      ((list-no-order (cons '1 (struct E ())) (cons '2 res)) res)
                      ((list-no-order
                         (cons
                          '1
                          (struct
                            T
                            ((list-no-order
                               (cons 'key key)
                               (cons 'value value)
                               (cons 'left left)
                               (cons 'right right)
                               g11300
                               ...))))
                         (cons '2 res))
                       ((d2l left) (cons (list (cons '1 key) (cons '2 value)) ((d2l right) res)))))
                    (list (cons '1 _id10568) (cons '2 _id10569))))))
             ((d2l d) ()))))
        (lambda (f)
          (match-lambda
            ((struct DICT ((list-no-order (cons '1 _) (cons '2 d))))
             (let ()
               (define a
                 (match-lambda
                   ((struct E ()) ())
                   ((struct
                      T
                      ((list-no-order (cons 'key key) (cons 'value value) (cons 'left left) (cons 'right right) g11301 ...)))
                    (begin (a right) (f (list (cons '1 key) (cons '2 value))) (a left)))))
               (a d)))))
        (lambda (f)
          (match-lambda
            ((struct DICT ((list-no-order (cons '1 _) (cons '2 d))))
             (let ()
               (define a
                 (match-lambda
                   ((struct E ()) ())
                   ((struct
                      T
                      ((list-no-order (cons 'key key) (cons 'value value) (cons 'left left) (cons 'right right) g11302 ...)))
                    (begin (a left) (f (list (cons '1 key) (cons '2 value))) (a right)))))
               (a d)))))
        (lambda (f)
          (lambda (init)
            (match-lambda
              ((struct DICT ((list-no-order (cons '1 _) (cons '2 d))))
               (let ()
                 (define a
                   (lambda (_id10577)
                     (lambda (_id10578)
                       ((match-lambda
                          ((list-no-order (cons '1 (struct E ())) (cons '2 v)) v)
                          ((list-no-order
                             (cons
                              '1
                              (struct
                                T
                                ((list-no-order
                                   (cons 'key key)
                                   (cons 'value value)
                                   (cons 'left left)
                                   (cons 'right right)
                                   g11303
                                   ...))))
                             (cons '2 v))
                           ((a left) (f (list (cons '1 key) (cons '2 value) (cons '3 ((a right) v)))))))
                        (list (cons '1 _id10577) (cons '2 _id10578))))))
                 ((a d) init))))))
        (lambda (f)
          (lambda (init)
            (match-lambda
              ((struct DICT ((list-no-order (cons '1 _) (cons '2 d))))
               (let ()
                 (define a
                   (lambda (_id10582)
                     (lambda (_id10583)
                       ((match-lambda
                          ((list-no-order (cons '1 (struct E ())) (cons '2 v)) v)
                          ((list-no-order
                             (cons
                              '1
                              (struct
                                T
                                ((list-no-order
                                   (cons 'key key)
                                   (cons 'value value)
                                   (cons 'left left)
                                   (cons 'right right)
                                   g11304
                                   ...))))
                             (cons '2 v))
                           ((a right) (f (list (cons '1 key) (cons '2 value) (cons '3 ((a left) v)))))))
                        (list (cons '1 _id10582) (cons '2 _id10583))))))
                 ((a d) init))))))
        (lambda (f)
          (match-lambda
            ((struct DICT ((list-no-order (cons '1 cmpKey) (cons '2 d))))
             (let ()
               (define a
                 (match-lambda
                   ((struct E ()) (struct E ()))
                   ((struct
                      T
                      ((list-no-order (cons 'key key) (cons 'value value) (cons 'left left) (cons 'right right) (cons 'cnt cnt))))
                    (let ()
                      (define left1 (a left))
                      (define value1 (f (list (cons '1 key) (cons '2 value))))
                      (struct
                        T
                        ((list
                          (cons 'cnt cnt)
                          (cons 'key key)
                          (cons 'value value1)
                          (cons 'left left1)
                          (cons 'right (a right)))))))))
               (struct DICT ((list (cons '1 cmpKey) (cons '2 (a d)))))))))
        (lambda (f)
          (match-lambda
            ((struct DICT ((list-no-order (cons '1 cmpKey) (cons '2 d))))
             (let ()
               (define a
                 (match-lambda
                   ((struct E ()) (struct E ()))
                   ((struct
                      T
                      ((list-no-order (cons 'key key) (cons 'value value) (cons 'left left) (cons 'right right) (cons 'cnt cnt))))
                    (let ()
                      (define left1 (a left))
                      (struct
                        T
                        ((list
                          (cons 'cnt cnt)
                          (cons 'key key)
                          (cons 'value (f value))
                          (cons 'left left1)
                          (cons 'right (a right)))))))))
               (struct DICT ((list (cons '1 cmpKey) (cons '2 (a d))))))))))))))
