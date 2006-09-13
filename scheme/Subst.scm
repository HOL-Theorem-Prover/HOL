(module Subst mzscheme
  
  (require (lib "plt-match.ss"))
  
  (require "records.scm"
           "0Records.scm")
  
  (provide (all-defined))
  
  (define id 'Id)
  ;cons is a Scheme prim and we dont want to override it
  
  (define shift
    (match-lambda
      ((vector 0 s)
       s)
      ((vector k (struct Shift (k1 s)))
       (shift (vector (+ k k1) s)))
      ((vector k s)
       (make-Shift k s))))
  
  (define lift
    (match-lambda
      ((vector 0 s)
       s)
      ((vector k 'Id)
       'Id)
      ((vector k (struct Lift (k1 s)))
       (lift (vector (+ k k1) s)))
      ((vector k s)
       (make-Lift k s))))
  
  (define (is_id t)
    (eq? t 'Id))
  
  (define exp_rel
    (letrec ((exp
              (match-lambda
                ((vector lams 'Id n)
                 (vector (+ lams n) 'NONE))
                ((vector lams (struct Cons (s x)) 0)
                 (vector lams (make-SOME x)))
                ((vector lams (struct Cons (s x)) n)
                 (exp (vector lams s (sub1 n))))
                ((vector lams (struct Shift (k s)) n)
                 (exp (vector (+ lams k) s n)))
                ((vector lams (struct Lift (k s)) n)
                 (if (< n k)
                     (vector (+ lams n) 'NONE)
                     (exp (vector (+ lams k) s (- n k))))))))
      (lambda (t)
        (let ((subs (vector-ref t 0))
              (db (vector-ref t 1)))
          (exp (vector 0 subs db))))))
  
  (define comp
    (match-lambda*
      ((list mk_cl 'Id s1)
       s1)
      ((list mk_cl s 'Id)
       s)
      ((list mk_cl s (struct Cons (s1 x)))
       (make-Cons (comp mk_cl s s1)
                  (mk_cl (vector s x))))
      ((list mk_cl (struct Cons (s x)) (struct Shift (k s1)))
       (comp mk_cl s (shift (vector (sub1 k) s1))))
      ((list  mk_cl (struct Cons (s x)) (struct Lift (k s1)))
       (make-Cons (comp mk_cl s (lift (vector (sub1 k) s1))) x))
      ((list mk_cl (struct Lift (k s)) (struct Shift (k1 s1)))
       (if (< k k1)
           (shift (vector k (comp mk_cl s (shift (vector (- k1 k) s1)))))
           (shift (vector k1 (comp mk_cl (lift (vector (- k k1) s)) s1)))))
      ((list mk_cl (struct Lift (k s)) (struct Lift (k1 s1)))
       (if (< k k1)
           (lift (vector k (comp mk_cl s (lift (vector (- k1 k) s1)))))
           (lift (vector k1 (comp mk_cl (lift (vector (- k k1) s)) s1)))))))
  )
  