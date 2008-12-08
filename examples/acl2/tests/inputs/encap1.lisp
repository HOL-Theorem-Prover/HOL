; formerly (approximately) examples/acl2/examples/encap/example.lisp

(in-package "ACL2")

; This one is trivial, in the sense that its first argument is the empty list
; of signatures.  The encapsulate should simply be removed.
(encapsulate
 ()
 (defthm car-cons-1
   (equal (car (cons x y))
          x)))

; This one is trivial, just as the one above, but has a local event, which
; (like all local events inside an encapsulate) should be ignored.
(encapsulate
 ()
 (local (defthm a-local-theorem
          (equal (cdr (cons x y)) y)))
 (defthm car-cons-2
   (equal (car (cons x y))
          x)))

; This one is like the one just above except that it has three non-local
; events.  This time, two of them are function definitions.
(encapsulate
 ()
 (local (defthm a-local-theorem
          (equal (cdr (cons x y)) y)))
 (defun f1 (x)
   x)
 (defthm car-cons-3
   (equal (car (cons x y))
          x))
 (defun f2 (x)
   x))

; Next we have an encapsulate whose signature is non-empty, thus introducing a
; new function.  In this example, that function is axiomatized to return an
; integer.  The translation could be a definition, along with a corresponding
; theorem (presumably proved by showing the existence of the g1 guaranteed by
; "some g1" below).
; Definition.  g1 = some g1 . forall x . (integerp (g1 x))
; |- forall x . |= (integerp (g1 x))
(encapsulate
 ((g1 (x) t))
 (local (defun g1 (x)
          (declare (ignore x))
          0))
 (defthm integerp-g1
   (integerp (g1 x))))

; The next one is similar to the one just above, except that the function
; returns two values -- well, every function returns one value actually, so we
; needn't explain the "two values" idea here, and maybe we won't have to deal
; with it until we do a round trip.
; Definition.  g2 = some g2 . (integerp (mv-nth 0 (g2 x)))
; |- forall x . |= (integerp (mv-nth 0 (g2 x)))
(encapsulate
 ((g2 (x) (mv t t)))
 (local (defun g2 (x)
          (declare (ignore x))
          (mv 0 0)))
 (defthm integerp-first-g2
   (integerp (mv-nth 0 (g2 x)))))

; The next encapsulate is like the preceding one, except that it introduces two
; functions.  We also use alternate syntax for encapsulate.  Presumably the
; corresponding HOL might look sort of as follows.
; Definition.  temp = some pair . let h1 = first(pair), h2 = second(pair) .
;                                 forall x . forall y .
;                                 (implies (integerp x) (integerp (h1 x)))
;                              /\ (implies (integerp y)
;                                          (integerp (mv-nth 0 (h2 x y))))
; Definition.  h1 = first(temp)
; Definition.  h2 = second(temp)
; |- forall x . |= (implies (integerp x) (integerp (h1 x)))
; |- forall x . forall y . |= (implies (integerp y)
;                                      (integerp (mv-nth 0 (h2 x y))))
(encapsulate
 (((h1 *)   => *)
  ((h2 * *) => (mv * *)))
 (local (defun h1 (x) x))
 (local (defun h2 (x y) (mv y x)))
 (defthm h1-prop
   (implies (integerp x)
            (integerp (h1 x))))
 (defthm h2-prop
   (implies (integerp y)
            (integerp (mv-nth 0 (h2 x y))))))

; The next encapsulate is like the preceding one, except that it introduces
; more axioms and a function not in the signature.  The idea is to treat h5 as
; though it were being introduced too, because that is indeed the case.
(encapsulate
 (((h3 *)   => *)
  ((h4 * *) => (mv * *)))
 (local (defun h3 (x) x))
 (local (defun h4 (x y) (mv y x)))
 (defthm h3-prop
   (implies (integerp x)
            (integerp (h3 x))))
 (defun h5 (x) (h3 x))
 (defthm h4-h5-prop
   (implies (integerp y)
            (integerp (h5 (mv-nth 0 (h4 x y)))))))
