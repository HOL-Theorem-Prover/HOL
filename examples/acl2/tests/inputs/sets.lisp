(in-package "ACL2")

#|

  sets.lisp
  ~~~~~~~~~

In this book, we discuss the basic theory of flat sets. We define the functions
subset, set-intersect, set-union and set-equal, and prove properties of these
functions. I include the records book here, just so that I dont have two
set-memberp functions. I do not know if this is going to be useful, but now I
am not feeling like I want to do much (what with feeling drowsy and depressed
and all) and so I thought this would just be an interesting exercise and be
useful later, since anyway I would need to reason about sets in model-checking.

|#

(include-book "records")

(defun subset (x y)
  (if (endp x) T
    (and (memberp (first x) y)
         (subset (rest x) y))))

(defun set-intersect (x y)
  (cond ((endp x) nil)
        ((memberp (first x) y) 
         (cons (first x) (set-intersect (rest x) y)))
        (t (set-intersect (rest x) y))))

(defun set-union (x y)
  (cond ((endp x) y)
        ((memberp (first x) y)
         (set-union (rest x) y))
        (t (cons (first x) (set-union (rest x) y)))))

(defun set-equal (x y)
  (and (subset x y)
       (subset y x)))

;; We prove that set-equal is an equivalence relation.

(local
(defthm proper-subset-is-a-subset
  (implies (subset x y)
           (subset x (cons a y))))
)

(defthm subset-is-reflexive
  (subset x x))

(defthm subset-is-transitive
  (implies (and (subset x y)
                (subset y z))
           (subset x z)))

(defthm subset-of-empty-is-empty
  (implies (and (not (consp x))
                (subset y X))
           (not (consp y))))


;; Just prove that set-equal is an equivalence now, should be trivial.

(defequiv set-equal)       

;; We have got reflexivity, and transitivity so far for subset, show that it is
;; anti-symmetric.

(defthm subset-is-antisymmetric
  (implies (and (subset x y)
                (subset y x))
           (set-equal x y))
  :rule-classes :forward-chaining)

;; This completes the properties of subset relation. 


;; Now show how union and intersection work with subset.

(defthm intersect-is-a-subset-1
  (subset (set-intersect x y) x))

(defthm intersect-is-a-subset-2
  (subset (set-intersect x y) y))

(defthm union-is-a-subset-1
  (subset x (set-union x y)))

(defthm union-is-a-subset-2
  (subset y (set-union x y)))

;; This completes interaction of union and intersection with subset. 

;; Now show interaction between subset and memberp functions

(defthm superset-contains-everything
  (implies (and (memberp e x)
                (subset x y))
           (memberp e y))
  :rule-classes :forward-chaining)

;; And let us do the consp of subset reduction

(defthm subset-of-nil-is-nil
  (implies (and (not (consp y))
                (subset x y))
           (not (consp x))))

;; This completes interaction between subset and memberp. 

;; Now we define a proper subset and show it is irreflexive.

(defun proper-subset (x y)
  (and (subset x y)
       (not (subset y x))))

(defthm proper-subset-is-irreflexive
  (not (proper-subset x x)))

(defthm proper-subset-is-transitive
  (implies (and (proper-subset x y)
                (proper-subset y z))
           (proper-subset x z)))

(defthm proper-subset-is-stronger-than-subset
  (implies (proper-subset x y)
           (subset x y)))

;; So I think we have proved enough theorems about sets for now, and we disable
;; all the functions. 

(in-theory (disable proper-subset set-union set-equal set-intersect))

;; Note: Unfortunately we cannot disable subset, since it is used everywhere
;; else. It might be worthwhile to do a more thorough job of the rewrite rules
;; and at least try doing it. But I am not sure.
