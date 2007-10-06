(module ListPair (lib "ml.scm" "lang")
  (provide ListPair@)
  (require "ListPair-sig.ss" "List.ss")
  (define-structure
   ListPair@
   ListPair^
   (define zip
     (match-lambda
       ((list-no-order (cons '1 xs) (cons '2 ys))
        (let ()
          (define h
            (lambda (_id10542)
              (lambda (_id10543)
                (lambda (_id10544)
                  (match
                   (list (cons '1 _id10542) (cons '2 _id10543) (cons '3 _id10544))
                   ((list-no-order (cons '1 (cons x xr)) (cons '2 (cons y yr)) (cons '3 res))
                    (((h xr) yr) (cons (list (cons '1 x) (cons '2 y)) res)))
                   ((list-no-order (cons '1 _) (cons '2 _) (cons '3 res)) ((ml-dot List@ rev) res)))))))
          (((h xs) ys) (list))))))
   (define unzip
     (lambda (xys)
       (let ()
         (define h
           (match-lambda
             ((list-no-order (cons '1 (list)) (cons '2 xs) (cons '3 ys))
              (list (cons '1 ((ml-dot List@ rev) xs)) (cons '2 ((ml-dot List@ rev) ys))))
             ((list-no-order (cons '1 (cons (list-no-order (cons '1 x) (cons '2 y)) xyr)) (cons '2 xs) (cons '3 ys))
              (h (list (cons '1 xyr) (cons '2 (cons x xs)) (cons '3 (cons y ys)))))))
         (h (list (cons '1 xys) (cons '2 (list)) (cons '3 (list)))))))
   (define map
     (lambda (f)
       (match-lambda
         ((list-no-order (cons '1 xs) (cons '2 ys))
          (let ()
            (define h
              (lambda (_id10548)
                (lambda (_id10549)
                  (lambda (_id10550)
                    (match
                     (list (cons '1 _id10548) (cons '2 _id10549) (cons '3 _id10550))
                     ((list-no-order (cons '1 (cons x xr)) (cons '2 (cons y yr)) (cons '3 res))
                      (((h xr) yr) (cons (f (list (cons '1 x) (cons '2 y))) res)))
                     ((list-no-order (cons '1 _) (cons '2 _) (cons '3 res)) ((ml-dot List@ rev) res)))))))
            (((h xs) ys) (list)))))))
   (define app
     (lambda (f)
       (match-lambda
         ((list-no-order (cons '1 xs) (cons '2 ys))
          (let ()
            (define h
              (lambda (_id10553)
                (lambda (_id10554)
                  (match
                   (list (cons '1 _id10553) (cons '2 _id10554))
                   ((list-no-order (cons '1 (cons x xr)) (cons '2 (cons y yr)))
                    ((match-lambda (_ ((h xr) yr))) (f (list (cons '1 x) (cons '2 y)))))
                   ((list-no-order (cons '1 _) (cons '2 _)) (list))))))
            ((h xs) ys))))))
   (define all
     (lambda (p)
       (match-lambda
         ((list-no-order (cons '1 xs) (cons '2 ys))
          (let ()
            (define h
              (lambda (_id10557)
                (lambda (_id10558)
                  (match
                   (list (cons '1 _id10557) (cons '2 _id10558))
                   ((list-no-order (cons '1 (cons x xr)) (cons '2 (cons y yr)))
                    ((match-lambda (#t ((h xr) yr)) (#f #f)) (p (list (cons '1 x) (cons '2 y)))))
                   ((list-no-order (cons '1 _) (cons '2 _)) #t)))))
            ((h xs) ys))))))
   (define exists
     (lambda (p)
       (match-lambda
         ((list-no-order (cons '1 xs) (cons '2 ys))
          (let ()
            (define h
              (lambda (_id10561)
                (lambda (_id10562)
                  (match
                   (list (cons '1 _id10561) (cons '2 _id10562))
                   ((list-no-order (cons '1 (cons x xr)) (cons '2 (cons y yr)))
                    ((match-lambda (#t #t) (#f ((h xr) yr))) (p (list (cons '1 x) (cons '2 y)))))
                   ((list-no-order (cons '1 _) (cons '2 _)) #f)))))
            ((h xs) ys))))))
   (define foldr
     (lambda (f)
       (lambda (e)
         (match-lambda
           ((list-no-order (cons '1 xs) (cons '2 ys))
            (let ()
              (define h
                (lambda (_id10565)
                  (lambda (_id10566)
                    (match
                     (list (cons '1 _id10565) (cons '2 _id10566))
                     ((list-no-order (cons '1 (cons x xr)) (cons '2 (cons y yr)))
                      (f (list (cons '1 x) (cons '2 y) (cons '3 ((h xr) yr)))))
                     ((list-no-order (cons '1 _) (cons '2 _)) e)))))
              ((h xs) ys)))))))
   (define foldl
     (lambda (f)
       (lambda (e)
         (match-lambda
           ((list-no-order (cons '1 xs) (cons '2 ys))
            (let ()
              (define h
                (lambda (_id10570)
                  (lambda (_id10571)
                    (lambda (_id10572)
                      (match
                       (list (cons '1 _id10570) (cons '2 _id10571) (cons '3 _id10572))
                       ((list-no-order (cons '1 e) (cons '2 (cons x xr)) (cons '3 (cons y yr)))
                        (((h (f (list (cons '1 x) (cons '2 y) (cons '3 e)))) xr) yr))
                       ((list-no-order (cons '1 e) (cons '2 _) (cons '3 _)) e))))))
              (((h e) xs) ys)))))))))
