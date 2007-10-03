(module List (lib "ml.scm" "lang")
  (provide List@)
  (require "List-sig.ss")
  (define-structure
   List@
   List^
   (define-struct Empty () #f)
   (define null (match-lambda (() #t) (_ #f)))
   (define hd (match-lambda (() (raise (struct Empty ()))) ((cons x xr) x)))
   (define tl (match-lambda (() (raise (struct Empty ()))) ((cons x xr) xr)))
   (define last (match-lambda (() (raise (struct Empty ()))) ((cons x ()) x) ((cons x xr) (last xr))))
   (define nth
     (match-lambda
       ((list-no-order (cons '1 xs) (cons '2 n))
        (let ()
          (define h
            (lambda (_id10546)
              (lambda (_id10547)
                (match
                 (list (cons '1 _id10546) (cons '2 _id10547))
                 ((list-no-order (cons '1 ()) (cons '2 _)) (raise (struct Subscript ())))
                 ((list-no-order (cons '1 (cons x xr)) (cons '2 n)) ((match-lambda (#t x) (#f ((h xr) (- n 1)))) (eqv? n 0)))))))
          (if (< n 0) (raise (struct Subscript ())) ((h xs) n))))))
   (define drop
     (match-lambda
       ((list-no-order (cons '1 xs) (cons '2 n))
        (let ()
          (define h
            (lambda (_id10549)
              (lambda (_id10550)
                (match
                 (list (cons '1 _id10549) (cons '2 _id10550))
                 ((list-no-order (cons '1 xs) (cons '2 0)) xs)
                 ((list-no-order (cons '1 ()) (cons '2 n)) (raise (struct Subscript ())))
                 ((list-no-order (cons '1 (cons x xr)) (cons '2 n)) ((h xr) (- n 1)))))))
          (if (< n 0) (raise (struct Subscript ())) ((h xs) n))))))
   (define take
     (match-lambda
       ((list-no-order (cons '1 xs) (cons '2 n))
        (let ()
          (define h
            (lambda (_id10552)
              (lambda (_id10553)
                (match
                 (list (cons '1 _id10552) (cons '2 _id10553))
                 ((list-no-order (cons '1 xs) (cons '2 0)) ())
                 ((list-no-order (cons '1 ()) (cons '2 n)) (raise (struct Subscript ())))
                 ((list-no-order (cons '1 (cons x xr)) (cons '2 n)) (cons x ((h xr) (- n 1))))))))
          (if (< n 0) (raise (struct Subscript ())) ((h xs) n))))))
   (define length
     (lambda (xs)
       (let ()
         (define acc
           (lambda (_id10555)
             (lambda (_id10556)
               (match
                (list (cons '1 _id10555) (cons '2 _id10556))
                ((list-no-order (cons '1 ()) (cons '2 k)) k)
                ((list-no-order (cons '1 (cons x xr)) (cons '2 k)) ((acc xr) (+ k 1)))))))
         ((acc xs) 0))))
   (match-define
     (list rev revAppend)
     (let ()
       (define revAcc
         (lambda (_id10558)
           (lambda (_id10559)
             (match
              (list (cons '1 _id10558) (cons '2 _id10559))
              ((list-no-order (cons '1 ()) (cons '2 ys)) ys)
              ((list-no-order (cons '1 (cons x xs)) (cons '2 ys)) ((revAcc xs) (cons x ys)))))))
       (list
        match
        (match-lambda (_id10561 ((match-lambda ((list-no-order (cons '1 xs) (cons '2 ys)) ((revAcc xs) ys))) _id10561)))
        (_id10560 ((match-lambda (xs ((revAcc xs) ()))) _id10560)))))
   (match-define
     (list @)
     (let ()
       (define append
         (lambda (_id10562)
           (lambda (_id10563)
             (match
              (list (cons '1 _id10562) (cons '2 _id10563))
              ((list-no-order (cons '1 ()) (cons '2 ys)) ys)
              ((list-no-order (cons '1 (cons x xs)) (cons '2 ys)) (cons x ((append xs) ys)))))))
       (list
        (match-lambda
          ((list-no-order (cons '1 xs) (cons '2 ())) xs)
          ((list-no-order (cons '1 xs) (cons '2 ys)) ((append xs) ys))))))
   (define concat (match-lambda (() ()) ((cons xs xsr) (append xs (concat xsr)))))
   (define app
     (lambda (_id10566)
       (lambda (_id10567)
         (match
          (list (cons '1 _id10566) (cons '2 _id10567))
          ((list-no-order (cons '1 f) (cons '2 ())) ())
          ((list-no-order (cons '1 f) (cons '2 (cons x xr))) ((match-lambda (_ ((app f) xr))) (f x)))))))
   (define map
     (lambda (_id10568)
       (lambda (_id10569)
         (match
          (list (cons '1 _id10568) (cons '2 _id10569))
          ((list-no-order (cons '1 f) (cons '2 ())) ())
          ((list-no-order (cons '1 f) (cons '2 (cons x xs))) (cons (f x) ((map f) xs)))))))
   (define mapPartial
     (lambda (_id10570)
       (lambda (_id10571)
         (match
          (list (cons '1 _id10570) (cons '2 _id10571))
          ((list-no-order (cons '1 f) (cons '2 ())) ())
          ((list-no-order (cons '1 f) (cons '2 (cons x xr)))
           ((match-lambda ((struct NONE ()) ((mapPartial f) xr)) ((struct SOME (r)) (cons r ((mapPartial f) xr)))) (f x)))))))
   (define find
     (lambda (_id10572)
       (lambda (_id10573)
         (match
          (list (cons '1 _id10572) (cons '2 _id10573))
          ((list-no-order (cons '1 p) (cons '2 ())) (struct NONE ()))
          ((list-no-order (cons '1 p) (cons '2 (cons x xr))) ((match-lambda (#t (struct SOME (x))) (#f ((find p) xr))) (p x)))))))
   (define filter
     (lambda (_id10574)
       (lambda (_id10575)
         (match
          (list (cons '1 _id10574) (cons '2 _id10575))
          ((list-no-order (cons '1 p) (cons '2 ())) ())
          ((list-no-order (cons '1 p) (cons '2 (cons x xr)))
           ((match-lambda (#t (cons x ((filter p) xr))) (#f ((filter p) xr))) (p x)))))))
   (define partition
     (lambda (p)
       (lambda (xs)
         (let ()
           (define h
             (lambda (_id10576)
               (lambda (_id10577)
                 (lambda (_id10578)
                   (match
                    (list (cons '1 _id10576) (cons '2 _id10577) (cons '3 _id10578))
                    ((list-no-order (cons '1 ()) (cons '2 are) (cons '3 |aren't|))
                     (list (cons '1 (rev are)) (cons '2 (rev |aren't|))))
                    ((list-no-order (cons '1 (cons x xr)) (cons '2 are) (cons '3 |aren't|))
                     ((match-lambda (#t (((h xr) (cons x are)) |aren't|)) (#f (((h xr) are) (cons x |aren't|)))) (p x))))))))
           (((h xs) ()) ())))))
   (define foldr
     (lambda (_id10581)
       (lambda (_id10582)
         (lambda (_id10583)
           (match
            (list (cons '1 _id10581) (cons '2 _id10582) (cons '3 _id10583))
            ((list-no-order (cons '1 f) (cons '2 e) (cons '3 ())) e)
            ((list-no-order (cons '1 f) (cons '2 e) (cons '3 (cons x xr)))
             (f (list (cons '1 x) (cons '2 (((foldr f) e) xr))))))))))
   (define foldl
     (lambda (_id10584)
       (lambda (_id10585)
         (lambda (_id10586)
           (match
            (list (cons '1 _id10584) (cons '2 _id10585) (cons '3 _id10586))
            ((list-no-order (cons '1 f) (cons '2 e) (cons '3 ())) e)
            ((list-no-order (cons '1 f) (cons '2 e) (cons '3 (cons x xr)))
             (((foldl f) (f (list (cons '1 x) (cons '2 e)))) xr)))))))
   (define exists
     (lambda (_id10587)
       (lambda (_id10588)
         (match
          (list (cons '1 _id10587) (cons '2 _id10588))
          ((list-no-order (cons '1 p) (cons '2 ())) #f)
          ((list-no-order (cons '1 p) (cons '2 (cons x xr))) ((match-lambda (#t #t) (#f ((exists p) xr))) (p x)))))))
   (define all
     (lambda (_id10589)
       (lambda (_id10590)
         (match
          (list (cons '1 _id10589) (cons '2 _id10590))
          ((list-no-order (cons '1 p) (cons '2 ())) #t)
          ((list-no-order (cons '1 p) (cons '2 (cons x xr))) ((match-lambda (#t ((all p) xr)) (#f #f)) (p x)))))))
   (define tabulate
     (match-lambda
       ((list-no-order (cons '1 n) (cons '2 f))
        (let () (define h (lambda (i) (if (< i n) (cons (f i) (h (+ i 1)))))) (if (< n 0) (raise (struct Size ())) (h 0))))))
   (define getItem (match-lambda (() (struct NONE ())) ((cons x xr) (struct SOME ((list (cons '1 x) (cons '2 xr)))))))))
