(in-package "ACL2")

#|

  apply-total-order.lisp
  ~~~~~~~~~~~~~~~~~~~~~~

In this book, we describe some simple functions like insert and drop
on a totally ordered list, and provide rules to manipulate them. The
functions that we introduce are insert, drop, memberp, orderedp, and
uniquep. Then we prove some theorems that we wish to export from this
book.

|#

(include-book "total-order")

(defun memberp (a x)
  (and (consp x)
       (or (equal a (first x))
           (memberp a (rest x)))))

(defun drop (a x)
  (cond ((endp x) ())
        ((equal a (first x)) 
         (drop a (rest x)))
        (t (cons (first x) 
                 (drop a (rest x))))))

(defun insert (a x)
  (cond ((endp x) (list a))
        ((equal a (first x)) x)
        ((<< a (first x)) (cons a x))
        (t (cons (first x)
                 (insert a (rest x))))))

(defun orderedp (x)
  (or (endp (rest x))
      (and (<< (first x) (second x))
           (orderedp (rest x)))))

(defun uniquep (x)
  (or (endp x)
      (and (not (memberp (first x) (rest x)))
           (uniquep (rest x)))))

;;;; some simple properties about insert, drop, and member

(defthm memberp-insert-same
  (equal (memberp a (insert a x)) T))

(defthm memberp-insert-diff
  (implies (not (equal a b))
           (equal (memberp a (insert b x))
                  (memberp a x))))

(defthm memberp-drop-same
  (equal (memberp a (drop a x)) nil))

(defthm memberp-drop-diff
  (implies (not (equal a b))
           (equal (memberp a (drop b x))
                  (memberp a x))))

(defthm ordered-implies-unique
  (implies (orderedp x)
           (uniquep x))
  :rule-classes (:forward-chaining
                 :rewrite))

(defthm memberp-yes-reduce-insert
  (implies (and (orderedp x)
                (memberp a x))
           (equal (insert a x) x)))

(defthm memberp-no-reduce-drop
  (implies (and (true-listp x)
                (not (memberp a x)))
           (equal (drop a x) x)))

(local
(defthm drop-is-monotonic
  (implies (and (orderedp x)
                (<< y (first x))
                (consp (drop a x)))
           (<< y (first (drop a x)))))
)

(defthm drop-preserves-orderedp
  (implies (orderedp x)
           (orderedp (drop a x))))

(defthm insert-preserves-orderedp
  (implies (orderedp x)
           (orderedp (insert a x))))

(defthm drop-of-insert-is-same
  (implies (and (true-listp x)
                (not (memberp a x)))
           (equal (drop a (insert a x)) x)))

(defthm insert-of-drop-is-same
  (implies (and (orderedp x)
                (true-listp x)
                (memberp a x))
           (equal (insert a (drop a x)) x)))

(defthm insert-returns-true-lists
  (implies (true-listp x)
           (true-listp (insert a x)))
  :rule-classes :type-prescription)
