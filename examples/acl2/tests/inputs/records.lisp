(in-package "ACL2")


#|

     records.lisp
     ~~~~~~~~~~~~

We define properties of a generic record accessor function and updater
function.  The basic functions are (g a r) and (s a v r) where a is an
address/key, v is a value, r is a record, and (g a r) returns the
value set to address a in record r, and (s a v r) returns a new record
with address a set to value v in record r.

We normalize the record structures (which allows the 'equal-ity based
rewrite rules) as alists where the keys (cars) are ordered using
Pete's total-order added to ACL2. We define a set of -aux functions
which assume well-formed records -- defined by rcdp -- and then prove
the desired properties using hypothesis assuming well-formed objects.

We then remove these well-formed object hypothesis by defining a invertible
mapping (acl2->rcd) from any ACL2 object to a well-formed records. We then
prove the desired properties using the proper translations of the -aux
functions to the acl2 objects, and subsequently remove the well-founded
hypothesis.

|#

(include-book "apply-total-order")

;; BEGIN records definitions.

(defun rcdp (x)
  (or (null x)
      (and (consp x)
           (consp (car x))
           (rcdp (cdr x))
           (cdar x)
           (or (null (cdr x))
               (<< (caar x) (caadr x))))))

(defun ifrp (x) ;; ill-formed rcdp 
  (or (not (rcdp x))
      (and (consp x)
           (null (cdr x))
           (consp (car x))
           (null (caar x))
           (ifrp (cdar x)))))

(defun acl2->rcd (x)
  (if (ifrp x) (list (cons nil x)) x))

(defun rcd->acl2 (x)
  (if (ifrp x) (cdar x) x))

(defun g-aux (a x)
  (cond ((or (endp x)
             (<< a (caar x)))
         nil)
        ((equal a (caar x))
         (cdar x))
        (t
         (g-aux a (cdr x)))))

(defun g (a x)
  (g-aux a (acl2->rcd x)))

(defun s-aux (a v r)
  (cond ((or (endp r)
             (<< a (caar r)))
         (if v (cons (cons a v) r) r))
        ((equal a (caar r))
         (if v (cons (cons a v) (cdr r)) (cdr r)))
        (t 
         (cons (car r) (s-aux a v (cdr r))))))

(defun s (a v x)
  (rcd->acl2 (s-aux a v (acl2->rcd x))))

(defun keys-aux (x)
  (cond ((endp x)
         ())
        (t (cons (caar x)
                 (keys-aux (cdr x))))))

(defun keys (x)
  (keys-aux (acl2->rcd x)))



;;;; basic property of records ;;;;

(local
(defthm rcdp-implies-true-listp
  (implies (rcdp x)
           (true-listp x))
  :rule-classes (:forward-chaining
                 :rewrite)))


;;;; initial properties of s-aux and g-aux ;;;;

(local
(defthm s-aux-is-bounded
  (implies (and (rcdp r)
                (s-aux a v r)
                (<< e a)
                (<< e (caar r)))
           (<< e (caar (s-aux a v r))))))

(local
(defthm s-aux-preserves-rcdp
  (implies (rcdp r)
           (rcdp (s-aux a v r)))))

(local
(defthm g-aux-same-s-aux
  (implies (rcdp r)
           (equal (g-aux a (s-aux a v r))
                  v))))

(local
(defthm g-aux-diff-s-aux
  (implies (and (rcdp r)
                (not (equal a b)))
           (equal (g-aux a (s-aux b v r))
                  (g-aux a r)))))

(local
(defthm s-aux-same-g-aux
  (implies (rcdp r)
           (equal (s-aux a (g-aux a r) r) 
                  r))))

(local
(defthm s-aux-same-s-aux
  (implies (rcdp r)
           (equal (s-aux a y (s-aux a x r))
                  (s-aux a y r)))))

(local
(defthm s-aux-diff-s-aux
  (implies (and (rcdp r)
                (not (equal a b)))
           (equal (s-aux b y (s-aux a x r))
                  (s-aux a x (s-aux b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s))))))

(local
(defthm s-aux-non-nil-cannot-be-nil
  (implies (and v (rcdp r))
           (s-aux a v r))))

(local
(defthm g-aux-is-nil-for-<<
  (implies (and (rcdp r)
                (<< a (caar r)))
           (equal (g-aux a r) nil))))

(local
(defthm g-keys-aux-relationship
  (implies (rcdp r)
           (iff (memberp a (keys-aux r))
                (g-aux a r)))))

(local
(defthm s-keys-aux-reduction
  (implies (rcdp r)
           (equal (keys-aux (s-aux a v r))
                  (if v 
                      (insert a (keys-aux r))
                    (drop a (keys-aux r)))))))

(local
(defthm keys-aux-are-ordered
  (implies (rcdp r)
           (orderedp (keys-aux r)))))


;;;; properties of acl2->rcd and rcd->acl2 ;;;;

(local
(defthm acl2->rcd-rcd->acl2-of-rcdp
  (implies (rcdp x)
           (equal (acl2->rcd (rcd->acl2 x))
                  x))))

(local
(defthm acl2->rcd-returns-rcdp
  (rcdp (acl2->rcd x))))

(local
(defthm acl2->rcd-preserves-equality
  (iff (equal (acl2->rcd x) (acl2->rcd y))
       (equal x y))))

(local
(defthm rcd->acl2-acl2->rcd-inverse
  (equal (rcd->acl2 (acl2->rcd x)) x)))

(local
(defthm rcd->acl2-of-record-non-nil
  (implies (and r (rcdp r))
           (rcd->acl2 r))))

(in-theory (disable acl2->rcd rcd->acl2))


;;;; final properties of record g(et) and s(et) ;;;;

(defthm g-same-s
  (equal (g a (s a v r)) 
	 v))

(defthm g-diff-s
  (implies (not (equal a b))
           (equal (g a (s b v r))
                  (g a r))))

;;;; NOTE: I often use the following instead of the above rules
;;;; to force ACL2 to do a case-split. In some cases, I will
;;;; disable this rule ACL2 is sluggish or if the number of cases
;;;; is unreasonable

(defthm g-of-s-redux
  (equal (g a (s b v r))
         (if (equal a b) v (g a r))))

(in-theory (disable g-of-s-redux))

(defthm s-same-g
  (equal (s a (g a r) r) 
	 r))

(defthm s-same-s
  (equal (s a y (s a x r))
	 (s a y r)))

(defthm s-diff-s
  (implies (not (equal a b))
           (equal (s b y (s a x r))
                  (s a x (s b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s)))))

(defthm g-keys-relationship
  (iff (memberp a (keys r))
       (g a r)))

(defthm s-keys-reduction
  (equal (keys (s a v r))
         (if v 
             (insert a (keys r))
           (drop a (keys r)))))

(defthm keys-are-ordered
  (orderedp (keys r)))

(defthm g-of-nil-is-nil
  (not (g a nil)))

(defthm s-non-nil-cannot-be-nil
  (implies v (s a v r))
  :hints (("Goal" 
           :in-theory (disable rcd->acl2-of-record-non-nil)
           :use (:instance rcd->acl2-of-record-non-nil
                           (r (s-aux a v (acl2->rcd r)))))))

(defthm non-nil-if-g-non-nil
  (implies (g a r) r)
  :rule-classes :forward-chaining)


(defthm s-same-g-back-chaining
  (implies (equal v (g a r))
           (equal (s a v r) r)))
                  

;; We disable s and g, assuming the rules proven in this book are sufficient to
;; manipulate record terms which are encountered

(in-theory (disable s g keys))

(defmacro <- (x a) `(g ,a ,x))

(defmacro -> (x a v) `(s ,a ,v ,x))

(defun update-macro (upds result)
  (declare (xargs :guard (keyword-value-listp upds)))
  (if (endp upds) result
    (update-macro (cddr upds)
                  (list 's (car upds) (cadr upds) result))))

(defmacro update (old &rest updates)
  (declare (xargs :guard (keyword-value-listp updates)))
  (update-macro updates old))




