(module Binarymap (lib "ml.scm" "lang")
  (provide Binarymap@)
  (require "Binarymap-sig.ss")
  (define-structure
   Binarymap@
   Binarymap^
   (define-struct (struct NotFound ()) () #f)
   (define wt (lambda (i) (* 3 i)))
   (define-struct DICT (content) #f)
   (define-struct E () #f)
   (define-struct T (content) #f)
   (define treeSize (match-lambda ((struct E ()) 0) ((struct T ((list-no-order (cons 'cnt cnt) g3854 ...))) cnt)))
   (define numItems (match-lambda ((struct DICT ((list-no-order (cons '1 _) (cons '2 t)))) (treeSize t))))
   (define mkDict
     (let ()
       (define mkDict (lambda (cmpKey) (struct DICT ((list (cons '1 cmpKey) (cons '2 (struct E ())))))))
       (define insert
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
                           (list-no-order (cons 'key key) (cons 'left left) (cons 'right right) (cons 'value value) g3883 ...))))
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
                           (cons 'cnt ((match-lambda ((list-no-order (cons 'cnt _id10559) g3884 ...) _id10559)) set)))))))
                    (cmpKey (list (cons '1 key) (cons '2 x)))))))
              (struct DICT ((list (cons '1 cmpKey) (cons '2 (ins t)))))))))
       (define find
         (match-lambda
           ((list-no-order (cons '1 (struct DICT ((list-no-order (cons '1 cmpKey) (cons '2 t))))) (cons '2 x))
            (let ()
              (define mem
                (match-lambda
                  ((struct E ()) (raise (struct NotFound ())))
                  ((struct T ((and n (list-no-order (cons 'key key) (cons 'left left) (cons 'right right) g3885 ...))))
                   ((match-lambda
                      ((struct GREATER ()) (mem right))
                      ((struct LESS ()) (mem left))
                      (_ ((match-lambda ((list-no-order (cons 'value _id10562) g3886 ...) _id10562)) n)))
                    (cmpKey (list (cons '1 x) (cons '2 key)))))))
              (mem t)))))
       (define peek
         (lambda (arg)
           (with-handlers
             (((match-lambda ((struct NotFound ()) #t)) (match-lambda ((struct NotFound ()) (struct NONE ())))))
             (struct SOME ((find arg))))))
       (define remove
         (match-lambda
           ((list-no-order (cons '1 (struct DICT ((list-no-order (cons '1 cmpKey) (cons '2 t))))) (cons '2 x))
            (let ()
              (define rm
                (match-lambda
                  ((struct E ()) (raise (struct NotFound ())))
                  ((and set
                        (struct
                          T
                          ((list-no-order (cons 'key key) (cons 'left left) (cons 'right right) (cons 'value value) g3887 ...))))
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
              (list (cons '1 (struct DICT ((list (cons '1 cmpKey) (cons '2 newtree))))) (cons '2 valrm))))))
       (define listItems
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
                                g3888
                                ...))))
                          (cons '2 res))
                        ((d2l left) (cons (list (cons '1 key) (cons '2 value)) ((d2l right) res)))))
                     (list (cons '1 _id10568) (cons '2 _id10569))))))
              ((d2l d) ())))))
       (define revapp
         (lambda (f)
           (match-lambda
             ((struct DICT ((list-no-order (cons '1 _) (cons '2 d))))
              (let ()
                (define a
                  (match-lambda
                    ((struct E ()) ())
                    ((struct
                       T
                       ((list-no-order (cons 'key key) (cons 'value value) (cons 'left left) (cons 'right right) g3889 ...)))
                     (begin (a right) (f (list (cons '1 key) (cons '2 value))) (a left)))))
                (a d))))))
       (define app
         (lambda (f)
           (match-lambda
             ((struct DICT ((list-no-order (cons '1 _) (cons '2 d))))
              (let ()
                (define a
                  (match-lambda
                    ((struct E ()) ())
                    ((struct
                       T
                       ((list-no-order (cons 'key key) (cons 'value value) (cons 'left left) (cons 'right right) g3890 ...)))
                     (begin (a left) (f (list (cons '1 key) (cons '2 value))) (a right)))))
                (a d))))))
       (define foldr
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
                                    g3891
                                    ...))))
                              (cons '2 v))
                            ((a left) (f (list (cons '1 key) (cons '2 value) (cons '3 ((a right) v)))))))
                         (list (cons '1 _id10577) (cons '2 _id10578))))))
                  ((a d) init)))))))
       (define foldl
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
                                    g3892
                                    ...))))
                              (cons '2 v))
                            ((a right) (f (list (cons '1 key) (cons '2 value) (cons '3 ((a left) v)))))))
                         (list (cons '1 _id10582) (cons '2 _id10583))))))
                  ((a d) init)))))))
       (define map
         (lambda (f)
           (match-lambda
             ((struct DICT ((list-no-order (cons '1 cmpKey) (cons '2 d))))
              (let ()
                (define a
                  (match-lambda
                    ((struct E ()) (struct E ()))
                    ((struct
                       T
                       ((list-no-order
                          (cons 'key key)
                          (cons 'value value)
                          (cons 'left left)
                          (cons 'right right)
                          (cons 'cnt cnt))))
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
                (struct DICT ((list (cons '1 cmpKey) (cons '2 (a d))))))))))
       (define transform
         (lambda (f)
           (match-lambda
             ((struct DICT ((list-no-order (cons '1 cmpKey) (cons '2 d))))
              (let ()
                (define a
                  (match-lambda
                    ((struct E ()) (struct E ()))
                    ((struct
                       T
                       ((list-no-order
                          (cons 'key key)
                          (cons 'value value)
                          (cons 'left left)
                          (cons 'right right)
                          (cons 'cnt cnt))))
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
                (struct DICT ((list (cons '1 cmpKey) (cons '2 (a d))))))))))
       (lambda (cmpKey) (struct DICT ((list (cons '1 cmpKey) (cons '2 (struct E ()))))))))))
