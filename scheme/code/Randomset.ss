(module Randomset (lib "ml.scm" "lang")
  (provide Randomset@)
  (require "Randomset-sig.ss")
  (define-structure
   Randomset@
   Randomset^
   (define-struct Bug (content) #f)
   (define-struct (struct NotFound ()) () #f)
   (define snd (lambda (_ x) x))
   (define randomPriority
     (let ()
       (define randomPriority (lambda () (((ml-dot Random range) 0 MAXIMUM_PRIORITY) gen)))
       (lambda () (((ml-dot Random range) 0 MAXIMUM_PRIORITY) gen))))
   (define priorityOrder
     (lambda (_id10544)
       (lambda (_id10545)
         ((match-lambda*
            ((list
              cmp
              (list-no-order
                (cons '1 (list-no-order (cons '1 p1) (cons '2 k1)))
                (cons '2 (list-no-order (cons '1 p2) (cons '2 k2)))))
             ((match-lambda (LESS LESS) (EQUAL (cmp (list (cons '1 k1) (cons '2 k2)))) (GREATER GREATER))
              ((ml-dot Int compare) p1 p2))))
          _id10544
          _id10545))))
   (define-struct E () #f)
   (define-struct T (content) #f)
   (define-struct Set (content) #f)
   (define nodePriorityOrder
     (lambda (_id10546)
       (lambda (_id10547)
         ((match-lambda*
            ((list cmp (list-no-order (cons '1 x1) (cons '2 x2)))
             (let ()
               (match-define (list-no-order (cons 'priority p1) (cons 'key k1) g24911 ...) x1)
               (match-define (list-no-order (cons 'priority p2) (cons 'key k2) g24912 ...) x2)
               ((priorityOrder cmp) (list (cons '1 p1) (cons '2 k1)) (list (cons '1 p2) (cons '2 k2))))))
          _id10546
          _id10547))))
   (define checkWellformed
     (let ()
       (define checkWellformed
         (lambda (_id10554)
           (lambda (_id10555)
             ((match-lambda*
                ((list s (struct Set ((list-no-order (cons '1 cmp) (cons '2 t)))))
                 (with-handlers
                   (((match-lambda ((struct Bug (bug)) #t))
                     (match-lambda
                       ((struct Bug (bug))
                        (raise
                         (struct
                           Bug
                           ((string-append
                              (string-append (string-append (string-append "Randomset.checkWellformed: " bug) " (") s)
                              ")"))))))))
                   (let ()
                     (define _ (checkSizes t))
                     (define _ (((checkSorted cmp) t) (struct NONE ())))
                     (define _ ((checkPriorities cmp) t))
                     (match-define (list-no-order) (print "."))
                     t))))
              _id10554
              _id10555))))
       (lambda (_id10554)
         (lambda (_id10555)
           ((match-lambda*
              ((list s (struct Set ((list-no-order (cons '1 cmp) (cons '2 t)))))
               (with-handlers
                 (((match-lambda ((struct Bug (bug)) #t))
                   (match-lambda
                     ((struct Bug (bug))
                      (raise
                       (struct
                         Bug
                         ((string-append
                            (string-append (string-append (string-append "Randomset.checkWellformed: " bug) " (") s)
                            ")"))))))))
                 (let ()
                   (define _ (checkSizes t))
                   (define _ (((checkSorted cmp) t) (struct NONE ())))
                   (define _ ((checkPriorities cmp) t))
                   (match-define (list-no-order) (print "."))
                   t))))
            _id10554
            _id10555)))))
   (define empty (lambda (cmp) (struct Set ((list (cons '1 cmp) (cons '2 (struct E ())))))))
   (define size (match-lambda ((struct E ()) 0) ((struct T ((list-no-order (cons 'size s) g24916 ...))) s)))
   (define numItems (match-lambda ((struct Set ((list-no-order (cons '1 _) (cons '2 t)))) (size t))))
   (define mkT
     (lambda (p)
       (lambda (l)
         (lambda (k)
           (lambda (r)
             (struct
               T
               ((list
                 (cons 'size (+ (+ (size l) 1) (size r)))
                 (cons 'priority p)
                 (cons 'left l)
                 (cons 'key k)
                 (cons 'right r)))))))))
   (define singleton
     (lambda (cmp)
       (lambda (key)
         (struct
           Set
           ((list
             (cons '1 cmp)
             (cons
              '2
              (struct
                T
                ((list
                  (cons 'size 1)
                  (cons 'priority (randomPriority (list)))
                  (cons 'left (struct E ()))
                  (cons 'key key)
                  (cons 'right (struct E ()))))))))))))
   (define peek
     (let ()
       (define peek (match-lambda* ((list (struct Set ((list-no-order (cons '1 cmp) (cons '2 t)))) k) (((treePeek cmp) t) k))))
       (match-lambda* ((list (struct Set ((list-no-order (cons '1 cmp) (cons '2 t)))) k) (((treePeek cmp) t) k)))))
   (define treeAppend
     (lambda (_id10569)
       (lambda (_id10570)
         (lambda (_id10571)
           ((match-lambda*
              ((list _ t1 (struct E ())) t1)
              ((list _ (struct E ()) t2) t2)
              ((list cmp (and t1 (struct T (x1))) (and t2 (struct T (x2))))
               (let ()
                 (match-define (list-no-order (cons 'priority p1) (cons 'left l1) (cons 'key k1) (cons 'right r1) g24918 ...) x1)
                 (match-define (list-no-order (cons 'priority p2) (cons 'left l2) (cons 'key k2) (cons 'right r2) g24919 ...) x2)
                 ((match-lambda
                    (LESS ((((mkT p2) (((treeAppend cmp) t1) l2)) k2) r2))
                    (EQUAL (raise (struct Bug ("Randomset.treeAppend: equal keys"))))
                    (GREATER ((((mkT p1) l1) k1) (((treeAppend cmp) r1) t2))))
                  ((nodePriorityOrder cmp) x1 x2)))))
            _id10569
            _id10570
            _id10571)))))
   (define treePartition
     (let ()
       (define treePartition (lambda (cmp) (lambda (t) (lambda (pkey) (((((treePart cmp) pkey))) t)))))
       (define nodePartition (lambda (cmp) (lambda (x) (lambda (pkey) (((((nodePart cmp) pkey))) x)))))
       (lambda (cmp) (lambda (t) (lambda (pkey) (((((treePart cmp) pkey))) t))))))
   (define union
     (let ()
       (define union
         (match-lambda*
           ((list
             (struct Set ((list-no-order (cons '1 cmp) (cons '2 t1))))
             (struct Set ((list-no-order (cons '1 _) (cons '2 t2)))))
            (let ()
              (match-define (list-no-order (cons '1 t1) (cons '2 t2)) (((combineRemove cmp) t1) t2))
              (struct Set ((list (cons '1 cmp) (cons '2 (((unionDisjoint cmp) t1) t2)))))))))
       (match-lambda*
         ((list (struct Set ((list-no-order (cons '1 cmp) (cons '2 t1)))) (struct Set ((list-no-order (cons '1 _) (cons '2 t2)))))
          (let ()
            (match-define (list-no-order (cons '1 t1) (cons '2 t2)) (((combineRemove cmp) t1) t2))
            (struct Set ((list (cons '1 cmp) (cons '2 (((unionDisjoint cmp) t1) t2))))))))))
   (define intersection
     (let ()
       (define intersection
         (match-lambda*
           ((list
             (struct Set ((list-no-order (cons '1 cmp) (cons '2 t1))))
             (struct Set ((list-no-order (cons '1 _) (cons '2 t2)))))
            (struct Set ((list (cons '1 cmp) (cons '2 (((treeIntersect cmp) t1) t2))))))))
       (match-lambda*
         ((list (struct Set ((list-no-order (cons '1 cmp) (cons '2 t1)))) (struct Set ((list-no-order (cons '1 _) (cons '2 t2)))))
          (struct Set ((list (cons '1 cmp) (cons '2 (((treeIntersect cmp) t1) t2)))))))))
   (define delete
     (let ()
       (define delete
         (match-lambda*
           ((list (struct Set ((list-no-order (cons '1 cmp) (cons '2 t)))) k)
            (struct Set ((list (cons '1 cmp) (cons '2 (((treeDelete cmp) t) k))))))))
       (match-lambda*
         ((list (struct Set ((list-no-order (cons '1 cmp) (cons '2 t)))) k)
          (struct Set ((list (cons '1 cmp) (cons '2 (((treeDelete cmp) t) k)))))))))
   (define difference
     (let ()
       (define difference
         (match-lambda*
           ((list
             (struct Set ((list-no-order (cons '1 cmp) (cons '2 t1))))
             (struct Set ((list-no-order (cons '1 _) (cons '2 t2)))))
            (struct Set ((list (cons '1 cmp) (cons '2 (((treeDifference cmp) t1) t2))))))))
       (match-lambda*
         ((list (struct Set ((list-no-order (cons '1 cmp) (cons '2 t1)))) (struct Set ((list-no-order (cons '1 _) (cons '2 t2)))))
          (struct Set ((list (cons '1 cmp) (cons '2 (((treeDifference cmp) t1) t2)))))))))
   (define isSubset
     (let ()
       (define isSubset
         (match-lambda*
           ((list
             (struct Set ((list-no-order (cons '1 cmp) (cons '2 s1))))
             (struct Set ((list-no-order (cons '1 _) (cons '2 s2)))))
            (((subset cmp) s1) s2))))
       (match-lambda*
         ((list (struct Set ((list-no-order (cons '1 cmp) (cons '2 s1)))) (struct Set ((list-no-order (cons '1 _) (cons '2 s2)))))
          (((subset cmp) s1) s2)))))
   (define leftSpine
     (lambda (_id10619)
       (lambda (_id10620)
         ((match-lambda*
            ((list (struct E ()) acc) acc)
            ((list (and t (struct T ((list-no-order (cons 'left left) g24930 ...)))) acc) ((leftSpine left) (cons t acc))))
          _id10619
          _id10620))))
   (define rightSpine
     (lambda (_id10621)
       (lambda (_id10622)
         ((match-lambda*
            ((list (struct E ()) acc) acc)
            ((list (and t (struct T ((list-no-order (cons 'right right) g24931 ...)))) acc) ((rightSpine right) (cons t acc))))
          _id10621
          _id10622))))
   (define-struct LR (content) #f)
   (define-struct RL (content) #f)
   (define mkLR
     (match-lambda
       ((list) (struct NONE ()))
       ((cons (struct T ((list-no-order (cons 'key key) (cons 'right right) g24932 ...))) l)
        (struct SOME ((struct LR ((list (cons '1 key) (cons '2 right) (cons '3 l)))))))
       ((cons (struct E ()) _) (raise (struct Bug ("Randomset.mkLR"))))))
   (define mkRL
     (match-lambda
       ((list) (struct NONE ()))
       ((cons (struct T ((list-no-order (cons 'key key) (cons 'left left) g24933 ...))) l)
        (struct SOME ((struct RL ((list (cons '1 key) (cons '2 left) (cons '3 l)))))))
       ((cons (struct E ()) _) (raise (struct Bug ("Randomset.mkRL"))))))
   (define mkIterator (match-lambda ((struct Set ((list-no-order (cons '1 _) (cons '2 t)))) (mkLR ((leftSpine t))))))
   (define mkRevIterator (match-lambda ((struct Set ((list-no-order (cons '1 _) (cons '2 t)))) (mkRL ((rightSpine t))))))
   (define readIterator
     (match-lambda
       ((struct LR ((list-no-order (cons '1 key_value) (cons '2 _) (cons '3 _)))) key_value)
       ((struct RL ((list-no-order (cons '1 key_value) (cons '2 _) (cons '3 _)))) key_value)))
   (define advanceIterator
     (match-lambda
       ((struct LR ((list-no-order (cons '1 _) (cons '2 next) (cons '3 l)))) (mkLR ((leftSpine next) l)))
       ((struct RL ((list-no-order (cons '1 _) (cons '2 next) (cons '3 l)))) (mkRL ((rightSpine next) l)))))
   (define isEmpty (lambda (s) (= (list (cons '1 (numItems s)) (cons '2 0)))))
   (define retrieve
     (lambda (s k)
       ((match-lambda ((struct NONE ()) (raise (struct NotFound ()))) ((struct SOME (k)) k))
        (peek (list (cons '1 s) (cons '2 k))))))
   (define member (lambda (s k) ((ml-dot Option isSome) (peek (list (cons '1 s) (cons '2 k))))))
   (define add
     (match-lambda*
       ((list (and s (struct Set ((list-no-order (cons '1 cmp) (cons '2 _))))) k)
        (union (list (cons '1 s) (cons '2 ((singleton cmp) k)))))))
   (define foldl
     (let ()
       (define foldl (lambda (f) (lambda (b) (lambda (m) (((fold f) (mkIterator m)) b)))))
       (define foldr (lambda (f) (lambda (b) (lambda (m) (((fold f) (mkRevIterator m)) b)))))
       (lambda (f) (lambda (b) (lambda (m) (((fold f) (mkIterator m)) b))))))
   (define find
     (let ()
       (define find (lambda (p) (lambda (m) ((findi p) (mkIterator m)))))
       (lambda (p) (lambda (m) ((findi p) (mkIterator m))))))
   (define addList (lambda (s l) ((((ml-dot List foldl) (lambda (k z) (add (list (cons '1 z) (cons '2 k))))) s) l)))
   (define listItems ((foldr ::)))
   (define equal
     (lambda (s1 s2)
       (if ((ml-dot Portable pointer_eq) s1 s2)
         #t
         (if (= (list (cons '1 (numItems s1)) (cons '2 (numItems s2))))
           (if (isSubset (list (cons '1 s1) (cons '2 s2))) (isSubset (list (cons '1 s2) (cons '2 s1))) #f)
           #f))))
   (define app (lambda (f) (lambda (s) (((foldl (match-lambda* ((list k (list-no-order)) (f k))))) s))))
   (define revapp (lambda (f) (lambda (s) (((foldr (match-lambda* ((list k (list-no-order)) (f k))))) s))))))
