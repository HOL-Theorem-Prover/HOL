(module Binaryset (lib "ml.scm" "lang")
  (provide Binaryset@)
  (require "Binaryset-sig.ss")
  (define-structure
   Binaryset@
   Binaryset^
   (define-struct SET (content) #f)
   (define-struct E () #f)
   (define-struct T (content) #f)
   (define treeSize (match-lambda ((struct E ()) 0) ((struct T ((list-no-order (cons 'cnt cnt) g789 ...))) cnt)))
   (define numItems (match-lambda ((struct SET ((list-no-order (cons '1 _) (cons '2 t)))) (treeSize t))))
   (define isEmpty (match-lambda ((struct SET ((list-no-order (cons '1 _) (cons '2 (struct E ()))))) #t) (_ #f)))
   (define mkT
     (match-lambda
       ((list-no-order (cons '1 v) (cons '2 n) (cons '3 l) (cons '4 r))
        (struct T ((list (cons 'elt v) (cons 'cnt n) (cons 'left l) (cons 'right r)))))))
   (define N
     (match-lambda
       ((list-no-order (cons '1 v) (cons '2 (struct E ())) (cons '3 (struct E ())))
        (mkT (list (cons '1 v) (cons '2 1) (cons '3 (struct E ())) (cons '4 (struct E ())))))
       ((list-no-order (cons '1 v) (cons '2 (struct E ())) (cons '3 (and r (struct T ((list-no-order (cons 'cnt n) g790 ...))))))
        (mkT (list (cons '1 v) (cons '2 (+ n 1)) (cons '3 (struct E ())) (cons '4 r))))
       ((list-no-order (cons '1 v) (cons '2 (and l (struct T ((list-no-order (cons 'cnt n) g791 ...))))) (cons '3 (struct E ())))
        (mkT (list (cons '1 v) (cons '2 (+ n 1)) (cons '3 l) (cons '4 (struct E ())))))
       ((list-no-order
          (cons '1 v)
          (cons '2 (and l (struct T ((list-no-order (cons 'cnt n) g792 ...)))))
          (cons '3 (and r (struct T ((list-no-order (cons 'cnt m) g793 ...))))))
        (mkT (list (cons '1 v) (cons '2 (+ (+ n m) 1)) (cons '3 l) (cons '4 r))))))
   (define single_L
     (match-lambda
       ((list-no-order
          (cons '1 a)
          (cons '2 x)
          (cons '3 (struct T ((list-no-order (cons 'elt b) (cons 'left y) (cons 'right z) g794 ...)))))
        (N (list (cons '1 b) (cons '2 (N (list (cons '1 a) (cons '2 x) (cons '3 y)))) (cons '3 z))))
       (_ (raise (struct Match ())))))
   (define single_R
     (match-lambda
       ((list-no-order
          (cons '1 b)
          (cons '2 (struct T ((list-no-order (cons 'elt a) (cons 'left x) (cons 'right y) g795 ...))))
          (cons '3 z))
        (N (list (cons '1 a) (cons '2 x) (cons '3 (N (list (cons '1 b) (cons '2 y) (cons '3 z)))))))
       (_ (raise (struct Match ())))))
   (define double_L
     (match-lambda
       ((list-no-order
          (cons '1 a)
          (cons '2 w)
          (cons
           '3
           (struct
             T
             ((list-no-order
                (cons 'elt c)
                (cons 'left (struct T ((list-no-order (cons 'elt b) (cons 'left x) (cons 'right y) g796 ...))))
                (cons 'right z)
                g797
                ...)))))
        (N
         (list
          (cons '1 b)
          (cons '2 (N (list (cons '1 a) (cons '2 w) (cons '3 x))))
          (cons '3 (N (list (cons '1 c) (cons '2 y) (cons '3 z)))))))
       (_ (raise (struct Match ())))))
   (define double_R
     (match-lambda
       ((list-no-order
          (cons '1 c)
          (cons
           '2
           (struct
             T
             ((list-no-order
                (cons 'elt a)
                (cons 'left w)
                (cons 'right (struct T ((list-no-order (cons 'elt b) (cons 'left x) (cons 'right y) g798 ...))))
                g799
                ...))))
          (cons '3 z))
        (N
         (list
          (cons '1 b)
          (cons '2 (N (list (cons '1 a) (cons '2 w) (cons '3 x))))
          (cons '3 (N (list (cons '1 c) (cons '2 y) (cons '3 z)))))))
       (_ (raise (struct Match ())))))
   (define wt (lambda (i) (+ (+ i i) i)))
   (define T1
     (match-lambda
       ((list-no-order (cons '1 v) (cons '2 (struct E ())) (cons '3 (struct E ())))
        (mkT (list (cons '1 v) (cons '2 1) (cons '3 (struct E ())) (cons '4 (struct E ())))))
       ((list-no-order
          (cons '1 v)
          (cons '2 (struct E ()))
          (cons '3 (and r (struct T ((list-no-order (cons 'left (struct E ())) (cons 'right (struct E ())) g800 ...))))))
        (mkT (list (cons '1 v) (cons '2 2) (cons '3 (struct E ())) (cons '4 r))))
       ((list-no-order
          (cons '1 v)
          (cons '2 (and l (struct T ((list-no-order (cons 'left (struct E ())) (cons 'right (struct E ())) g801 ...)))))
          (cons '3 (struct E ())))
        (mkT (list (cons '1 v) (cons '2 2) (cons '3 l) (cons '4 (struct E ())))))
       ((and p
             (list-no-order
               (cons '1 _)
               (cons '2 (struct E ()))
               (cons '3 (struct T ((list-no-order (cons 'left (struct T (_))) (cons 'right (struct E ())) g802 ...))))))
        (double_L p))
       ((and p
             (list-no-order
               (cons '1 _)
               (cons '2 (struct T ((list-no-order (cons 'left (struct E ())) (cons 'right (struct T (_))) g803 ...))))
               (cons '3 (struct E ()))))
        (double_R p))
       ((and p
             (list-no-order
               (cons '1 _)
               (cons '2 (struct E ()))
               (cons
                '3
                (struct
                  T
                  ((list-no-order
                     (cons 'left (struct T ((list-no-order (cons 'cnt ln) g804 ...))))
                     (cons 'right (struct T ((list-no-order (cons 'cnt rn) g805 ...))))
                     g806
                     ...))))))
        (if (< ln rn) (single_L p) (double_L p)))
       ((and p
             (list-no-order
               (cons '1 _)
               (cons
                '2
                (struct
                  T
                  ((list-no-order
                     (cons 'left (struct T ((list-no-order (cons 'cnt ln) g807 ...))))
                     (cons 'right (struct T ((list-no-order (cons 'cnt rn) g808 ...))))
                     g809
                     ...))))
               (cons '3 (struct E ()))))
        (if (> ln rn) (single_R p) (double_R p)))
       ((and p
             (list-no-order
               (cons '1 _)
               (cons '2 (struct E ()))
               (cons '3 (struct T ((list-no-order (cons 'left (struct E ())) g810 ...))))))
        (single_L p))
       ((and p
             (list-no-order
               (cons '1 _)
               (cons '2 (struct T ((list-no-order (cons 'right (struct E ())) g811 ...))))
               (cons '3 (struct E ()))))
        (single_R p))
       ((and p
             (list-no-order
               (cons '1 v)
               (cons '2 (and l (struct T ((list-no-order (cons 'elt lv) (cons 'cnt ln) (cons 'left ll) (cons 'right lr))))))
               (cons '3 (and r (struct T ((list-no-order (cons 'elt rv) (cons 'cnt rn) (cons 'left rl) (cons 'right rr))))))))
        (if (>= rn (wt ln))
          (let () (define rln (treeSize rl)) (define rrn (treeSize rr)) (if (< rln rrn) (single_L p) (double_L p)))
          (if (>= ln (wt rn))
            (let () (define lln (treeSize ll)) (define lrn (treeSize lr)) (if (< lrn lln) (single_R p) (double_R p)))
            (mkT (list (cons '1 v) (cons '2 (+ (+ ln rn) 1)) (cons '3 l) (cons '4 r))))))))
   (define addt
     (lambda (cmpKey)
       (lambda (t)
         (lambda (x)
           (let ()
             (define h
               (match-lambda
                 ((struct E ()) (mkT (list (cons '1 x) (cons '2 1) (cons '3 (struct E ())) (cons '4 (struct E ())))))
                 ((struct T ((list-no-order (cons 'elt v) (cons 'left l) (cons 'right r) (cons 'cnt cnt))))
                  ((match-lambda
                     ((struct LESS ()) (T1 (list (cons '1 v) (cons '2 (h l)) (cons '3 r))))
                     ((struct GREATER ()) (T1 (list (cons '1 v) (cons '2 l) (cons '3 (h r)))))
                     ((struct EQUAL ()) (mkT (list (cons '1 x) (cons '2 cnt) (cons '3 l) (cons '4 r)))))
                   (cmpKey (list (cons '1 x) (cons '2 v)))))))
             (h t))))))
   (define concat3
     (lambda (_id10557)
       (lambda (_id10558)
         (lambda (_id10559)
           (lambda (_id10560)
             ((match-lambda
                ((list-no-order (cons '1 cmpKey) (cons '2 (struct E ())) (cons '3 v) (cons '4 r)) (((addt cmpKey) r) v))
                ((list-no-order (cons '1 cmpKey) (cons '2 l) (cons '3 v) (cons '4 (struct E ()))) (((addt cmpKey) l) v))
                ((list-no-order
                   (cons '1 cmpKey)
                   (cons '2 (and l (struct T ((list-no-order (cons 'elt v1) (cons 'cnt n1) (cons 'left l1) (cons 'right r1))))))
                   (cons '3 v)
                   (cons '4 (and r (struct T ((list-no-order (cons 'elt v2) (cons 'cnt n2) (cons 'left l2) (cons 'right r2)))))))
                 (if (< (wt n1) n2)
                   (T1 (list (cons '1 v2) (cons '2 ((((concat3 cmpKey) l) v) l2)) (cons '3 r2)))
                   (if (< (wt n2) n1)
                     (T1 (list (cons '1 v1) (cons '2 l1) (cons '3 ((((concat3 cmpKey) r1) v) r))))
                     (N (list (cons '1 v) (cons '2 l) (cons '3 r)))))))
              (list (cons '1 _id10557) (cons '2 _id10558) (cons '3 _id10559) (cons '4 _id10560))))))))
   (define split_lt
     (lambda (_id10561)
       (lambda (_id10562)
         (lambda (_id10563)
           ((match-lambda
              ((list-no-order (cons '1 cmpKey) (cons '2 (struct E ())) (cons '3 x)) (struct E ()))
              ((list-no-order
                 (cons '1 cmpKey)
                 (cons '2 (struct T ((list-no-order (cons 'elt v) (cons 'left l) (cons 'right r) g812 ...))))
                 (cons '3 x))
               ((match-lambda
                  ((struct GREATER ()) (((split_lt cmpKey) l) x))
                  ((struct LESS ()) ((((concat3 cmpKey) l) v) (((split_lt cmpKey) r) x)))
                  (_ l))
                (cmpKey (list (cons '1 v) (cons '2 x))))))
            (list (cons '1 _id10561) (cons '2 _id10562) (cons '3 _id10563)))))))
   (define split_gt
     (lambda (_id10564)
       (lambda (_id10565)
         (lambda (_id10566)
           ((match-lambda
              ((list-no-order (cons '1 cmpKey) (cons '2 (struct E ())) (cons '3 x)) (struct E ()))
              ((list-no-order
                 (cons '1 cmpKey)
                 (cons '2 (struct T ((list-no-order (cons 'elt v) (cons 'left l) (cons 'right r) g813 ...))))
                 (cons '3 x))
               ((match-lambda
                  ((struct LESS ()) (((split_gt cmpKey) r) x))
                  ((struct GREATER ()) ((((concat3 cmpKey) (((split_gt cmpKey) l) x)) v) r))
                  (_ r))
                (cmpKey (list (cons '1 v) (cons '2 x))))))
            (list (cons '1 _id10564) (cons '2 _id10565) (cons '3 _id10566)))))))
   (define min
     (match-lambda
       ((struct T ((list-no-order (cons 'elt v) (cons 'left (struct E ())) g814 ...))) v)
       ((struct T ((list-no-order (cons 'left l) g815 ...))) (min l))
       (_ (raise (struct Match ())))))
   (define delmin
     (match-lambda
       ((struct T ((list-no-order (cons 'left (struct E ())) (cons 'right r) g816 ...))) r)
       ((struct T ((list-no-order (cons 'elt v) (cons 'left l) (cons 'right r) g817 ...)))
        (T1 (list (cons '1 v) (cons '2 (delmin l)) (cons '3 r))))
       (_ (raise (struct Match ())))))
   (define delete1
     (match-lambda
       ((list-no-order (cons '1 (struct E ())) (cons '2 r)) r)
       ((list-no-order (cons '1 l) (cons '2 (struct E ()))) l)
       ((list-no-order (cons '1 l) (cons '2 r)) (T1 (list (cons '1 (min r)) (cons '2 l) (cons '3 (delmin r)))))))
   (define concat
     (lambda (_id10570)
       (lambda (_id10571)
         ((match-lambda
            ((list-no-order (cons '1 (struct E ())) (cons '2 s)) s)
            ((list-no-order (cons '1 s) (cons '2 (struct E ()))) s)
            ((list-no-order
               (cons '1 (and t1 (struct T ((list-no-order (cons 'elt v1) (cons 'cnt n1) (cons 'left l1) (cons 'right r1))))))
               (cons '2 (and t2 (struct T ((list-no-order (cons 'elt v2) (cons 'cnt n2) (cons 'left l2) (cons 'right r2)))))))
             (if (< (wt n1) n2)
               (T1 (list (cons '1 v2) (cons '2 ((concat t1) l2)) (cons '3 r2)))
               (if (< (wt n2) n1)
                 (T1 (list (cons '1 v1) (cons '2 l1) (cons '3 ((concat r1) t2))))
                 (T1 (list (cons '1 (min t2)) (cons '2 t1) (cons '3 (delmin t2))))))))
          (list (cons '1 _id10570) (cons '2 _id10571))))))
   (define hedge_union
     (lambda (_id10589)
       (lambda (_id10590)
         (lambda (_id10591)
           ((match-lambda
              ((list-no-order (cons '1 cmpKey) (cons '2 s) (cons '3 (struct E ()))) s)
              ((list-no-order (cons '1 cmpKey) (cons '2 (struct E ())) (cons '3 s)) s)
              ((list-no-order
                 (cons '1 cmpKey)
                 (cons '2 (struct T ((list-no-order (cons 'elt v) (cons 'left l1) (cons 'right r1) g818 ...))))
                 (cons '3 (and s2 (struct T ((list-no-order (cons 'elt v2) (cons 'left l2) (cons 'right r2) g819 ...))))))
               (let ()
                 (define trim
                   (lambda (_id10572)
                     (lambda (_id10573)
                       (lambda (_id10574)
                         ((match-lambda
                            ((list-no-order (cons '1 lo) (cons '2 hi) (cons '3 (struct E ()))) (struct E ()))
                            ((list-no-order
                               (cons '1 lo)
                               (cons '2 hi)
                               (cons
                                '3
                                (and s (struct T ((list-no-order (cons 'elt v) (cons 'left l) (cons 'right r) g820 ...))))))
                             (if (eqv? (cmpKey (list (cons '1 v) (cons '2 lo))) (struct GREATER ()))
                               (if (eqv? (cmpKey (list (cons '1 v) (cons '2 hi))) (struct LESS ())) s (((trim lo) hi) l))
                               (((trim lo) hi) r))))
                          (list (cons '1 _id10572) (cons '2 _id10573) (cons '3 _id10574)))))))
                 (define uni_bd
                   (lambda (_id10575)
                     (lambda (_id10576)
                       (lambda (_id10577)
                         (lambda (_id10578)
                           ((match-lambda
                              ((list-no-order (cons '1 s) (cons '2 (struct E ())) (cons '3 _) (cons '4 _)) s)
                              ((list-no-order
                                 (cons '1 (struct E ()))
                                 (cons '2 (struct T ((list-no-order (cons 'elt v) (cons 'left l) (cons 'right r) g821 ...))))
                                 (cons '3 lo)
                                 (cons '4 hi))
                               ((((concat3 cmpKey) (((split_gt cmpKey) l) lo)) v) (((split_lt cmpKey) r) hi)))
                              ((list-no-order
                                 (cons '1 (struct T ((list-no-order (cons 'elt v) (cons 'left l1) (cons 'right r1) g822 ...))))
                                 (cons
                                  '2
                                  (and s2 (struct T ((list-no-order (cons 'elt v2) (cons 'left l2) (cons 'right r2) g823 ...)))))
                                 (cons '3 lo)
                                 (cons '4 hi))
                               ((((concat3 cmpKey) ((((uni_bd l1) (((trim lo) v) s2)) lo) v)) v)
                                ((((uni_bd r1) (((trim v) hi) s2)) v) hi))))
                            (list (cons '1 _id10575) (cons '2 _id10576) (cons '3 _id10577) (cons '4 _id10578))))))))
                 (define trim_lo
                   (lambda (_id10579)
                     (lambda (_id10580)
                       ((match-lambda
                          ((list-no-order (cons '1 _) (cons '2 (struct E ()))) (struct E ()))
                          ((list-no-order
                             (cons '1 lo)
                             (cons '2 (and s (struct T ((list-no-order (cons 'elt v) (cons 'right r) g824 ...))))))
                           ((match-lambda ((struct GREATER ()) s) (_ ((trim_lo lo) r)))
                            (cmpKey (list (cons '1 v) (cons '2 lo))))))
                        (list (cons '1 _id10579) (cons '2 _id10580))))))
                 (define trim_hi
                   (lambda (_id10581)
                     (lambda (_id10582)
                       ((match-lambda
                          ((list-no-order (cons '1 _) (cons '2 (struct E ()))) (struct E ()))
                          ((list-no-order
                             (cons '1 hi)
                             (cons '2 (and s (struct T ((list-no-order (cons 'elt v) (cons 'left l) g825 ...))))))
                           ((match-lambda ((struct LESS ()) s) (_ ((trim_hi hi) l))) (cmpKey (list (cons '1 v) (cons '2 hi))))))
                        (list (cons '1 _id10581) (cons '2 _id10582))))))
                 (define uni_hi
                   (lambda (_id10583)
                     (lambda (_id10584)
                       (lambda (_id10585)
                         ((match-lambda
                            ((list-no-order (cons '1 s) (cons '2 (struct E ())) (cons '3 _)) s)
                            ((list-no-order
                               (cons '1 (struct E ()))
                               (cons '2 (struct T ((list-no-order (cons 'elt v) (cons 'left l) (cons 'right r) g826 ...))))
                               (cons '3 hi))
                             ((((concat3 cmpKey) l) v) (((split_lt cmpKey) r) hi)))
                            ((list-no-order
                               (cons '1 (struct T ((list-no-order (cons 'elt v) (cons 'left l1) (cons 'right r1) g827 ...))))
                               (cons
                                '2
                                (and s2 (struct T ((list-no-order (cons 'elt v2) (cons 'left l2) (cons 'right r2) g828 ...)))))
                               (cons '3 hi))
                             ((((concat3 cmpKey) (((uni_hi l1) ((trim_hi v) s2)) v)) v)
                              ((((uni_bd r1) (((trim v) hi) s2)) v) hi))))
                          (list (cons '1 _id10583) (cons '2 _id10584) (cons '3 _id10585)))))))
                 (define uni_lo
                   (lambda (_id10586)
                     (lambda (_id10587)
                       (lambda (_id10588)
                         ((match-lambda
                            ((list-no-order (cons '1 s) (cons '2 (struct E ())) (cons '3 _)) s)
                            ((list-no-order
                               (cons '1 (struct E ()))
                               (cons '2 (struct T ((list-no-order (cons 'elt v) (cons 'left l) (cons 'right r) g829 ...))))
                               (cons '3 lo))
                             ((((concat3 cmpKey) (((split_gt cmpKey) l) lo)) v) r))
                            ((list-no-order
                               (cons '1 (struct T ((list-no-order (cons 'elt v) (cons 'left l1) (cons 'right r1) g830 ...))))
                               (cons
                                '2
                                (and s2 (struct T ((list-no-order (cons 'elt v2) (cons 'left l2) (cons 'right r2) g831 ...)))))
                               (cons '3 lo))
                             ((((concat3 cmpKey) ((((uni_bd l1) (((trim lo) v) s2)) lo) v)) v)
                              (((uni_lo r1) ((trim_lo v) s2)) v))))
                          (list (cons '1 _id10586) (cons '2 _id10587) (cons '3 _id10588)))))))
                 ((((concat3 cmpKey) (((uni_hi l1) ((trim_hi v) s2)) v)) v) (((uni_lo r1) ((trim_lo v) s2)) v)))))
            (list (cons '1 _id10589) (cons '2 _id10590) (cons '3 _id10591)))))))
   (define old_union
     (lambda (_id10592)
       (lambda (_id10593)
         (lambda (_id10594)
           ((match-lambda
              ((list-no-order (cons '1 _) (cons '2 (struct E ())) (cons '3 s2)) s2)
              ((list-no-order (cons '1 _) (cons '2 s1) (cons '3 (struct E ()))) s1)
              ((list-no-order
                 (cons '1 cmpKey)
                 (cons '2 (struct T ((list-no-order (cons 'elt v) (cons 'left l) (cons 'right r) g832 ...))))
                 (cons '3 s2))
               (let ()
                 (define l2 (((split_lt cmpKey) s2) v))
                 (define r2 (((split_gt cmpKey) s2) v))
                 ((((concat3 cmpKey) (((old_union cmpKey) l) l2)) v) (((old_union cmpKey) r) r2)))))
            (list (cons '1 _id10592) (cons '2 _id10593) (cons '3 _id10594)))))))
   (define-struct NotFound () #f)
   (define empty (lambda (cmpKey) (struct SET ((list (cons '1 cmpKey) (cons '2 (struct E ())))))))
   (define singleton
     (lambda (cmpKey)
       (lambda (x)
         (struct
           SET
           ((list
             (cons '1 cmpKey)
             (cons
              '2
              (struct T ((list (cons 'elt x) (cons 'cnt 1) (cons 'left (struct E ())) (cons 'right (struct E ()))))))))))))
   (define addList
     (match-lambda
       ((list-no-order (cons '1 (struct SET ((list-no-order (cons '1 cmpKey) (cons '2 t))))) (cons '2 l))
        (struct
          SET
          ((list
            (cons '1 cmpKey)
            (cons
             '2
             ((((ml-dot List foldl) (match-lambda ((list-no-order (cons '1 i) (cons '2 s)) (((addt cmpKey) s) i)))) t) l))))))))
   (define add
     (match-lambda
       ((list-no-order (cons '1 (struct SET ((list-no-order (cons '1 cmpKey) (cons '2 t))))) (cons '2 x))
        (struct SET ((list (cons '1 cmpKey) (cons '2 (((addt cmpKey) t) x))))))))
   (define peekt
     (lambda (cmpKey)
       (lambda (t)
         (lambda (x)
           (let ()
             (define pk
               (match-lambda
                 ((struct E ()) (struct NONE ()))
                 ((struct T ((list-no-order (cons 'elt v) (cons 'left l) (cons 'right r) g833 ...)))
                  ((match-lambda ((struct LESS ()) (pk l)) ((struct GREATER ()) (pk r)) (_ (struct SOME (v))))
                   (cmpKey (list (cons '1 x) (cons '2 v)))))))
             (pk t))))))
   (define membert
     (lambda (cmpKey) (lambda (t) (lambda (x) ((match-lambda ((struct NONE ()) #f) (_ #t)) (((peekt cmpKey) t) x))))))
   (define peek
     (match-lambda
       ((list-no-order (cons '1 (struct SET ((list-no-order (cons '1 cmpKey) (cons '2 t))))) (cons '2 x))
        (((peekt cmpKey) t) x))))
   (define member (lambda (arg) ((match-lambda ((struct NONE ()) #f) (_ #t)) (peek arg))))
   (match-define
     (list isSubset equal)
     (let ()
       (define treeIn
         (lambda (cmpKey)
           (match-lambda
             ((list-no-order (cons '1 t) (cons '2 t1))
              (let ()
                (define isIn
                  (match-lambda
                    ((struct E ()) #t)
                    ((struct T ((list-no-order (cons 'elt elt) (cons 'left (struct E ())) (cons 'right (struct E ())) g834 ...)))
                     (((membert cmpKey) t1) elt))
                    ((struct T ((list-no-order (cons 'elt elt) (cons 'left left) (cons 'right (struct E ())) g835 ...)))
                     (and (((membert cmpKey) t1) elt) #f))
                    ((struct T ((list-no-order (cons 'elt elt) (cons 'left (struct E ())) (cons 'right right) g836 ...)))
                     (and (((membert cmpKey) t1) elt) #f))
                    ((struct T ((list-no-order (cons 'elt elt) (cons 'left left) (cons 'right right) g837 ...)))
                     (and (((membert cmpKey) t1) elt) #f))))
                (isIn t))))))
       (list
        (match-lambda
          ((list-no-order (cons '1 (struct SET ((list-no-order (cons '1 _) (cons '2 (struct E ())))))) (cons '2 _)) #t)
          ((list-no-order (cons '1 _) (cons '2 (struct SET ((list-no-order (cons '1 _) (cons '2 (struct E ()))))))) #f)
          ((list-no-order
             (cons
              '1
              (struct
                SET
                ((list-no-order (cons '1 cmpKey) (cons '2 (and t (struct T ((list-no-order (cons 'cnt n) g838 ...)))))))))
             (cons
              '2
              (struct SET ((list-no-order (cons '1 _) (cons '2 (and t1 (struct T ((list-no-order (cons 'cnt n1) g839 ...))))))))))
           (and (<= n n1) #f)))
        (match-lambda
          ((list-no-order
             (cons '1 (struct SET ((list-no-order (cons '1 _) (cons '2 (struct E ()))))))
             (cons '2 (struct SET ((list-no-order (cons '1 _) (cons '2 (struct E ())))))))
           #t)
          ((list-no-order
             (cons
              '1
              (struct
                SET
                ((list-no-order (cons '1 cmpKey) (cons '2 (and t (struct T ((list-no-order (cons 'cnt n) g840 ...)))))))))
             (cons
              '2
              (struct SET ((list-no-order (cons '1 _) (cons '2 (and t1 (struct T ((list-no-order (cons 'cnt n1) g841 ...))))))))))
           (and (eqv? n n1) #f))
          (_ #f)))))
   (define retrieve
     (lambda (arg) ((match-lambda ((struct NONE ()) (raise (struct NotFound ()))) ((struct SOME (v)) v)) (peek arg))))
   (define delete
     (match-lambda
       ((list-no-order (cons '1 (struct SET ((list-no-order (cons '1 cmpKey) (cons '2 t))))) (cons '2 x))
        (let ()
          (define delt
            (match-lambda
              ((struct E ()) (raise (struct NotFound ())))
              ((and t (struct T ((list-no-order (cons 'elt v) (cons 'left l) (cons 'right r) g842 ...))))
               ((match-lambda
                  ((struct LESS ()) (T1 (list (cons '1 v) (cons '2 (delt l)) (cons '3 r))))
                  ((struct GREATER ()) (T1 (list (cons '1 v) (cons '2 l) (cons '3 (delt r)))))
                  (_ (delete1 (list (cons '1 l) (cons '2 r)))))
                (cmpKey (list (cons '1 x) (cons '2 v)))))))
          (struct SET ((list (cons '1 cmpKey) (cons '2 (delt t)))))))))
   (define union
     (match-lambda
       ((list-no-order
          (cons '1 (struct SET ((list-no-order (cons '1 cmpKey) (cons '2 t1)))))
          (cons '2 (struct SET ((list-no-order (cons '1 _) (cons '2 t2))))))
        (struct SET ((list (cons '1 cmpKey) (cons '2 (((hedge_union cmpKey) t1) t2))))))))
   (define intersection
     (match-lambda
       ((list-no-order
          (cons '1 (struct SET ((list-no-order (cons '1 cmpKey) (cons '2 t1)))))
          (cons '2 (struct SET ((list-no-order (cons '1 _) (cons '2 t2))))))
        (let ()
          (define intert
            (lambda (_id10618)
              (lambda (_id10619)
                ((match-lambda
                   ((list-no-order (cons '1 (struct E ())) (cons '2 _)) (struct E ()))
                   ((list-no-order (cons '1 _) (cons '2 (struct E ()))) (struct E ()))
                   ((list-no-order
                      (cons '1 t)
                      (cons '2 (struct T ((list-no-order (cons 'elt v) (cons 'left l) (cons 'right r) g843 ...)))))
                    (let ()
                      (define l2 (((split_lt cmpKey) t) v))
                      (define r2 (((split_gt cmpKey) t) v))
                      ((match-lambda
                         ((struct NONE ()) ((concat ((intert l2) l)) ((intert r2) r)))
                         (_ ((((concat3 cmpKey) ((intert l2) l)) v) ((intert r2) r))))
                       (((peekt cmpKey) t) v)))))
                 (list (cons '1 _id10618) (cons '2 _id10619))))))
          (struct SET ((list (cons '1 cmpKey) (cons '2 ((intert t1) t2)))))))))
   (define difference
     (match-lambda
       ((list-no-order
          (cons '1 (struct SET ((list-no-order (cons '1 cmpKey) (cons '2 t1)))))
          (cons '2 (struct SET ((list-no-order (cons '1 _) (cons '2 t2))))))
        (let ()
          (define difft
            (lambda (_id10621)
              (lambda (_id10622)
                ((match-lambda
                   ((list-no-order (cons '1 (struct E ())) (cons '2 s)) (struct E ()))
                   ((list-no-order (cons '1 s) (cons '2 (struct E ()))) s)
                   ((list-no-order
                      (cons '1 s)
                      (cons '2 (struct T ((list-no-order (cons 'elt v) (cons 'left l) (cons 'right r) g844 ...)))))
                    (let ()
                      (define l2 (((split_lt cmpKey) s) v))
                      (define r2 (((split_gt cmpKey) s) v))
                      ((concat ((difft l2) l)) ((difft r2) r)))))
                 (list (cons '1 _id10621) (cons '2 _id10622))))))
          (struct SET ((list (cons '1 cmpKey) (cons '2 ((difft t1) t2)))))))))
   (define foldr
     (lambda (f)
       (lambda (b)
         (match-lambda
           ((struct SET ((list-no-order (cons '1 _) (cons '2 t))))
            (let ()
              (define foldf
                (lambda (_id10624)
                  (lambda (_id10625)
                    ((match-lambda
                       ((list-no-order (cons '1 (struct E ())) (cons '2 b)) b)
                       ((list-no-order
                          (cons '1 (struct T ((list-no-order (cons 'elt elt) (cons 'left left) (cons 'right right) g845 ...))))
                          (cons '2 b))
                        ((foldf left) (f (list (cons '1 elt) (cons '2 ((foldf right) b)))))))
                     (list (cons '1 _id10624) (cons '2 _id10625))))))
              ((foldf t) b)))))))
   (define foldl
     (lambda (f)
       (lambda (b)
         (match-lambda
           ((struct SET ((list-no-order (cons '1 _) (cons '2 t))))
            (let ()
              (define foldf
                (lambda (_id10629)
                  (lambda (_id10630)
                    ((match-lambda
                       ((list-no-order (cons '1 (struct E ())) (cons '2 b)) b)
                       ((list-no-order
                          (cons '1 (struct T ((list-no-order (cons 'elt elt) (cons 'left left) (cons 'right right) g846 ...))))
                          (cons '2 b))
                        ((foldf right) (f (list (cons '1 elt) (cons '2 ((foldf left) b)))))))
                     (list (cons '1 _id10629) (cons '2 _id10630))))))
              ((foldf t) b)))))))
   (define listItems ((foldr ::) ()))
   (define revapp
     (lambda (f)
       (match-lambda
         ((struct SET ((list-no-order (cons '1 _) (cons '2 t))))
          (let ()
            (define apply
              (match-lambda
                ((struct E ()) ())
                ((struct T ((list-no-order (cons 'elt elt) (cons 'left left) (cons 'right right) g847 ...)))
                 (begin (apply right) (f elt) (apply left)))))
            (apply t))))))
   (define app
     (lambda (f)
       (match-lambda
         ((struct SET ((list-no-order (cons '1 _) (cons '2 t))))
          (let ()
            (define apply
              (match-lambda
                ((struct E ()) ())
                ((struct T ((list-no-order (cons 'elt elt) (cons 'left left) (cons 'right right) g848 ...)))
                 (begin (apply left) (f elt) (apply right)))))
            (apply t))))))
   (define find
     (lambda (p)
       (match-lambda
         ((struct SET ((list-no-order (cons '1 _) (cons '2 t))))
          (let ()
            (define findt
              (match-lambda
                ((struct E ()) (struct NONE ()))
                ((struct T ((list-no-order (cons 'elt elt) (cons 'left left) (cons 'right right) g849 ...)))
                 (if (p elt) (struct SOME (elt)) ((match-lambda ((struct NONE ()) (findt right)) (a a)) (findt left))))))
            (findt t))))))))
