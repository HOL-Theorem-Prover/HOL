(module Listsort (lib "ml.scm" "lang")
  (provide Listsort@)
  (require "Listsort-sig.ss" "List.ss")
  (define-structure
   Listsort@
   Listsort^
   (define sort
     (lambda (_id10552)
       (lambda (_id10553)
         ((match-lambda
            ((list-no-order (cons '1 ordr) (cons '2 (list))) (list))
            ((list-no-order (cons '1 ordr) (cons '2 (and xs (cons _ (list)))))
             xs)
            ((list-no-order
               (cons '1 ordr)
               (cons '2 (and xs (cons x1 (cons x2 (list))))))
             ((match-lambda
                ((struct GREATER ()) (cons x2 (cons x1 (list))))
                (_ xs))
              (ordr (list (cons '1 x1) (cons '2 x2)))))
            ((list-no-order (cons '1 ordr) (cons '2 xs))
             (let ()
               (define merge
                 (lambda (_id10542)
                   (lambda (_id10543)
                     ((match-lambda
                        ((list-no-order (cons '1 (list)) (cons '2 ys)) ys)
                        ((list-no-order (cons '1 xs) (cons '2 (list))) xs)
                        ((list-no-order
                           (cons '1 (cons x xs))
                           (cons '2 (cons y ys)))
                         (if (!=
                              (ordr (list (cons '1 x) (cons '2 y)))
                              (struct GREATER ()))
                           (cons x ((merge xs) (cons y ys)))
                           (cons y ((merge (cons x xs)) ys)))))
                      (list (cons '1 _id10542) (cons '2 _id10543))))))
               (define mergepairs
                 (lambda (_id10544)
                   (lambda (_id10545)
                     (lambda (_id10546)
                       ((match-lambda
                          ((list-no-order
                             (cons '1 l1)
                             (cons '2 (list))
                             (cons '3 k))
                           (cons l1 (list)))
                          ((list-no-order
                             (cons '1 l1)
                             (cons '2 (and ls (cons l2 lr)))
                             (cons '3 k))
                           (if (eqv? (modulo k 2) 1)
                             (cons l1 ls)
                             (((mergepairs ((merge l1) l2)) lr) (/ k 2)))))
                        (list
                         (cons '1 _id10544)
                         (cons '2 _id10545)
                         (cons '3 _id10546)))))))
               (define nextrun
                 (lambda (_id10547)
                   (lambda (_id10548)
                     ((match-lambda
                        ((list-no-order (cons '1 run) (cons '2 (list)))
                         (list (cons '1 run) (cons '2 (list))))
                        ((list-no-order
                           (cons '1 run)
                           (cons '2 (and xs (cons x xr))))
                         (if (eqv?
                              (ordr
                               (list
                                (cons '1 x)
                                (cons '2 ((ml-dot List@ hd) run))))
                              (struct LESS ()))
                           (list (cons '1 run) (cons '2 xs))
                           ((nextrun (cons x run)) xr))))
                      (list (cons '1 _id10547) (cons '2 _id10548))))))
               (define sorting
                 (lambda (_id10549)
                   (lambda (_id10550)
                     (lambda (_id10551)
                       ((match-lambda
                          ((list-no-order
                             (cons '1 (list))
                             (cons '2 ls)
                             (cons '3 r))
                           ((ml-dot List@ hd) (((mergepairs (list)) ls) 0)))
                          ((list-no-order
                             (cons '1 (cons x xs))
                             (cons '2 ls)
                             (cons '3 r))
                           (let ()
                             (match-define
                               (list-no-order (cons '1 revrun) (cons '2 tail))
                               ((nextrun (cons x (list))) xs))
                             (((sorting tail)
                               (((mergepairs ((ml-dot List@ rev) revrun)) ls)
                                (+ r 1)))
                              (+ r 1)))))
                        (list
                         (cons '1 _id10549)
                         (cons '2 _id10550)
                         (cons '3 _id10551)))))))
               (((sorting xs) (list)) 0))))
          (list (cons '1 _id10552) (cons '2 _id10553))))))
   (define sorted
     (lambda (_id10556)
       (lambda (_id10557)
         ((match-lambda
            ((list-no-order (cons '1 ordr) (cons '2 (list))) #t)
            ((list-no-order (cons '1 ordr) (cons '2 (cons y1 yr)))
             (let ()
               (define h
                 (lambda (_id10554)
                   (lambda (_id10555)
                     ((match-lambda
                        ((list-no-order (cons '1 x0) (cons '2 (list))) #t)
                        ((list-no-order (cons '1 x0) (cons '2 (cons x1 xr)))
                         (and (!=
                               (ordr (list (cons '1 x0) (cons '2 x1)))
                               (struct GREATER ()))
                              #f)))
                      (list (cons '1 _id10554) (cons '2 _id10555))))))
               ((h y1) yr))))
          (list (cons '1 _id10556) (cons '2 _id10557))))))))
