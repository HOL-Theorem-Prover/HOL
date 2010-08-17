#|
(defpkg "M1"
  '(defun declare ignore xargs defthm mutual-recursion
    include-book in-theory disable defconst
    defmacro &rest
    intern-in-package-of-symbol
    coerce symbol-name
    string
    otherwise
    concatenate progn strip-cars syntaxp quotep assoc pairlis$ pairlis-x2 e/d

    o-p o< acl2-count
    let let*
    cond case
    and or not implies t nil quote
    cons consp car cdr endp
    list list*
    atom symbolp natp
    if equal
    zp + - * / mod expt < <= > >=))

(begin-book t :ttags :all)
|#

(in-package "M1")

; Problem Set 1

; The bulk of this problem set asks you to define some ACL2 functions.  I do
; not particularly want you to use the mechanized version of ACL2 to check your
; answers, but you are welcome to do so if you wish.  If you do use the mechanized
; system you will find that some of the function symbols I ask you to define are
; already defined and the definitions are not always the ones I ask for below!
; We will eventually learn how to use Common Lisp's ``package system'' to
; avoid name conflicts; in the meanwhile, you can avoid name conflicts manually,
; by choosing different names when you test your proposed definitions.

; Answers should be typed and submitted by 3:30 pm Tuesday, Jan 23, 2007.  To
; submit your answers put all your answer files in a directory, myname-asgi,
; where myname is your login name and i is the assignment number: 1, 2, ....
; (Typically all your answers will be in a single file.)

; Then execute on a CS Unix machine:

;  turnin --submit alexsp cs378 myname-asgi

; To check your submissions:

;  turnin --list alexsp cs378

; In my presentation of the problems below, when I write 

; expr ==> value

; I mean that the expression expr evaluates to value.  For example,

; (+ 2 2) ==> 4.

; In defining the required functions, limit yourself to the following
; ACL2 forms and functions:

;   expression                  meaning

; (defun fn (v1 ... vn)  Define fn to take the formal arguments v1, ..., vn,
;   body)                and to return the value of body (evaluated in an
;                     environment where the vi are bound to the values
;                     of the actuals).  Thus, if I define
;                     (defun sq (x) (* x x))
;                     then (sq 7) ==> 49.

; (let ((v1 t1)       Evaluate each of the ti.  Then let the vi have those
;       ...           respective values.  In that environment, evaluate and
;       (vn tn))      return the value of body.
;  body)              

; (let* ((v1 t1)      Evaluate t1 and let v1 have that value.  Then ...
;        ...          then evaluate tn and let vn have that value.  In
;        (vn tn))     that environment, evaluate and return body.
;  body)

; [Note: the difference between let and let* is that in the former the
; variables get their values ``in parallel'' and in the latter they get them
; ``in sequence.''  For example, suppose x has the value 1 in the ``global
; environment.''  Then 

; (let  ((x 5) (y (+ 1 x))) (* x y)) ==> 10

; but

; (let* ((x 5) (y (+ 1 x))) (* x y)) ==> 30

; end of note]

; (cond (p1 x1)       Evaluate p1 and if non-nil, evaluate and return x1;
;       (p2 x2)       else, evaluate p2 and if non-nil, evaluate and return x2;
;       ...           ...
;       (t  xk))      else, evaluate and return xk.

; [Note: The cond above is just an abbreviation for
; (if p1 x1 (if p2 x2 ... xk)).]

; (case x             Evaluate x and and if the value is literally
;   (sym1 y1)         sym1, evaluate and return y1; else if the value is
;   (sym2 y2)         sym2, evaluate and return y2; else if the value is
;   ...               ...
;   (otherwise yk))   else, evaluate and return yk.

; [Note: The symi MUST be symbols.  Note that they are not evaluated!
; The case above is just an abbreviation for:
; (cond ((equal x 'sym1) y1)
;       ((equal x 'sym2) y2)
;       ...
;       (t yk)).]

; (and p1 ... pn)       t or nil depending on whether all the pi are non-nil.

; (or p1 ... pn)        t or nil depending on whether at least one pi is non-nil.

; (not p1)              t if p1 is nil and nil if p1 is t.

; (implies p1 p2)       t if either p1 is nil or p2 is t.

; [Note: The descriptions above are right only if the pi are Boolean valued.
; If the pi can return values other than t or nil, the descriptions are more
; complicated.  I recommend not testing non-Boolean expressions!]

; (cons x y)            the ordered pair whose left component (car) is x and
;                       whose right component (cdr) is y

; (consp x)             t or nil indicating whether x is an ordered pair

; (car x)               the left component of the ordered pair x; or
;                       nil if x is not an ordered pair.

; (cdr x)               the right component of the ordered pair x; or
;                       nil if x is not an ordered pair.

; (list x1 ... xn)      same as (cons x1 (cons x2 ... (cons xn nil)))

; (list* x1 ... xn)     same as (cons x1 (cons x2 ... (cons xn-1 xn)))

; (endp x)              same as (not (consp x))

; (atom x)              same as (not (consp x))

; (symbolp x)           t or nil indicating whether x is a symbol

; (keywordp x)          t or nil indicating whether x is a keyword symbol

; (natp x)              t or nil indicating whether x is a natural number
;                       (nonnegative integer)
 
; (if x y z)            if x is t, then y, else z;

; [Note: The description is more complicated if x is not Boolean.]

; (equal x y)           t or nil indicating whether x and y are the same

; (zp x)                t or nil indicating whether x is 0 or not a natural
;                       number.  Thus, (zp -3) ==> t.

; (+ x1 ... xn)         sum of the xi

; (* x1 ... xn)         product of the xi

; (- x1 x2)             difference of x1 take away x2

; (/ x1 x2)             rational quotient of x1 divided by x2

; (mod x1 x2)           x1 mod x2, e.g., (mod 23 3) ==> 2

; (expt x1 x2)          x1 raised to the power x2

; (< x1 x2)             t or nil indicating whether x1 is less than x2

; (<= x1 x2)            t or nil indicating whether x1 is less than or
;                       equal to x2

; (> x1 x2)             t or nil indicating whether x1 is greater than x2

; (>= x1 x2)            t or nil indicating whether x1 is greater than or
;                       equal to x2

; [Note:  In the arithmetic functions, if an xi is not a number then it
; is defaulted to 0.  Thus (+ T 5) ==> 5.]

; The way we will eventually implement this restriction to certain symbols is
; to define the \ptt{"M1"} package to import the symbols above but not to
; import certain other symbols -- namely the ones I'm asking you to define.

; Recall from the lecture:

(defun push (x y) (cons x y))

;      |           |
;      |           cons in the ACL2 package
;      |
;      push in the M1 package

; Thus,                 (push 3 nil)   ==> (3)
;               (push 2 (push 3 nil))  ==> (2 3)
;       (push 1 (push 2 (push 3 nil))) ==> (1 2 3)

; If we define top and pop like this:

(defun top (stack) (car stack))
(defun pop (stack) (cdr stack))

; then (top (push 1 (push 2 (push 3 nil)))) ==> 1
;      (pop (push 1 (push 2 (push 3 nil)))) ==> (2 3)

; A recursive definition:

(defun nth (n list)
  (if (zp n)
      (car list)
    (nth (- n 1) (cdr list))))

; Here is another handy definition:

(defun make-state (pc locals stack program)
     (cons pc
           (cons locals
                 (cons stack
                       (cons program
                             nil)))))

; Note:  The cons nest above is the same thing as
; (list pc locals stack program).

(defun pc (s) (nth 0 s))
(defun locals (s) (nth 1 s))
(defun stack (s) (nth 2 s))
(defun program (s) (nth 3 s))

; -----------------------------------------------------------------

; Problem 1-1.  ACL2 has various predicates for recognizing different kinds of Lisp
; objects.  Among them are:
; a. NATP
; b. STRINGP
; c. CONSP
; d. SYMBOLP
; e. ENDP
; f. KEYWORDP

; Beside each object, indicate which of the above predicates it satisfies.

;  1. 123                      ((A - NATP) (E - ENDP))
;  2. ILOAD                    ((D - SYMBOLP) (E - ENDP))
;  3. INVOKEVIRTUAL            ((D - SYMBOLP) (E - ENDP))
;  4. "Hello World!"           ((B - STRINGP) (E - ENDP))
;  5. NIL                      ((D - SYMBOLP) (E - ENDP))
;  6. :NAME                    ((D - SYMBOLP) (E - ENDP) (F - KEYWORDP)) 
;  7. (ILOAD 0)                ((C - CONSP))
;  8. ("Beta" "position")      ((C - CONSP))
;  9. ((ILOAD 0) (IFNE 237))   ((C - CONSP))
; 10. ILOAD_0                  ((D - SYMBOLP) (E - ENDP))

; ---

; Problem 1-2.  For each list x below, write down (CAR x), (CAR (CDR x)), and (CDR (CDR x)).

; 1. (ILOAD 0)
;    Answers:                        ILOAD              0                   NIL

; 2. (GETFIELD ("Beta" "position"))  
;    Answers:                        GETFIELD           ("Beta" "position") NIL

; 3. (IINC 3 -1)          
;    Answers:                        IINC               3                   (-1)

; 4. (IADD)
;    Answers:                        IADD               NIL                 NIL

; 5. ((ILOAD 0) (IFNE 237) (ICONST_1))
;    Answers:                        (ILOAD 0)          (IFNE 237)          ((ICONST_1))

; 6. (THREAD (:ID 3) (:CT NIL) (:STAT ACTIVE) (:REF (REF 27)))
;    Answers:                        THREAD             (:ID 3)             ((:CT NIL) (:STAT ACTIVE) (:REF (REF 27)))

; 7. (:CT NIL)
;    Answers:                        :CT                NIL                 NIL

; ---

; Problem 1-3.  For each object below, write the CONS expression that constructs
; it.  Each answer will be a call of CONS, applied to numbers, quoted symbols,
; strings, and/or NIL. 

; 0.  (ILOAD 2)  Answer: (cons 'ILOAD (cons 2 NIL))

; 1.  (IADD)     Answer: (cons 'IADD NIL)
; 2.  ((:ID 3) (:CT NIL)) 
;     Answer: (cons (cons :ID (cons 3 nil))
;                   (cons (cons :CT (cons NIL nil))
;                          nil))
; 3.  (NIL) Answer: (cons NIL nil)
; 4.  (GETFIELD ("Beta" "position"))
;     Answer: (cons 'GETFIELD
;                   (cons (cons "Beta" (cons "position" nil))
;                         nil))

; ---

; Problem 1-4:  An ``instruction'' is a list of the form (op a1 ... ak), where
; k=0, 1, 2, or 3.

; Define opcode to take an instruction and return the op.  Define arg1, arg2,
; and arg3 to take an instruction and return the corresponding operand of the
; instruction, or nil if it is not present.

; Answer 1-4:

(defun op-code (inst) (car inst))
(defun arg1 (inst) (nth 1 inst))
(defun arg2 (inst) (nth 2 inst))
(defun arg3 (inst) (nth 3 inst))

; ---

; Problem 1-5:  Fill in the blank:
; (top (pop (push x (push y (push z nil))))) = ______________

; Answer 1-5:
; (top (pop (push x (push y (push z nil))))) = y

; ---

; Problem 1-6:  Can you PROVE your answer to Problem 1-5 is correct?

; Answer 1-6:  One way to prove this is to replace top, pop, and push by
; their definitions and get

; (car (cdr (cons x (cons y (cons z nil))))) = y

; and then use the axioms for car-cons and cdr-cons.

; A ``better'' way to prove it is to prove two lemmas (by following the scheme above
; of replacing the stack functions by their definitions):

; Lemma 1:  top-push
; (top (push x y)) = x

; Lemma 2:  pop-push
; (pop (push x y)) = y

; and then to apply those lemmas as follows:

; Proof:
; (top (pop (push x (push y (push z nil)))))
; =  {by Lemma 2 and replacement of equals by equals}
; (top (push y (push z nil)))
; =  {by Lemma 1 and replacement of equals by equals}
; y
; Q.E.D.

; ---

; Problem 1-7:  (stack (make-state a b c d)) = _____________

; Answer 1-7:   (stack (make-state a b c d)) = c

; ---

; Problem 1-8:  Prove Problem 1-7. 

; Answer 1-8:
; Proof that (stack (make-state a b c d)) = c

; (stack (make-state a b c d))
; = {def of stack}
; (nth 2 (make-state a b c d))
; = {def nth and the facts (zp 2) = nil and (- 2 1) = 1 and basic axioms}
; (nth 1 (cdr (make-state a b c d)))
; = {def nth and the facts (zp 1) = nil and (- 1 1) = 0 and basic axioms}
; (nth 0 (cdr (cdr (make-state a b c d))))
; = {defn nth and (zp 0) = t and basic axioms}
; (car (cdr (cdr (make-state a b c d))))
; = {def make-state}
; (car (cdr (cdr (cons a (cons b (cons c (cons d nil)))))))
; = {basic axiom about cdr-cons}
; (car (cdr (cons b (cons c (cons d nil)))))
; = {basic axiom about cdr-cons}
; (car (cons c (cons d nil)))
; = {basic axiom about car-cons}
; c
; Q.E.D.

; ---

; Problem 1-9: 
; Define (len x) to return the number of elements of list x.
; Thus, (len '(a b c)) ==> 3.  (``==>'' means ``evaluates to'')

; Answer 1-9:
(defun len (x)
  (if (endp x)
      0
    (+ 1 (len (cdr x)))))

; ---

; Problem 1-10:
; Define (app x y) to concatenate two lists.
; Thus, (app '(a b c) '(d e f)) ==> (A B C D E F).

; Answer 1-10:
(defun app (x y)
  (if (endp x)
      y
    (cons (car x)
          (app (cdr x) y))))

; ---

; Problem 1-11:
; Define (rev x) to reverse a list x.
; Thus, (rev '(a b c)) ==> (C B A).

; Answer 1-11:
(defun rev (x)
  (if (endp x)
      nil
    (app (rev (cdr x))
         (cons (car x) nil))))

; An alternative answer is the definition of frev below.

(defun rev1 (x a)
  (if (endp x)
      a
    (rev1 (cdr x)
          (cons (car x) a))))

(defun frev (x) (rev1 x nil))

; ---

; Problem 1-12:
; Define (repeat x n) to return a list consisting of n
; copies of x.  Thus, (repeat 'a 5) ==> (A A A A A).

; Answer 1-12:
(defun repeat (th n)
     (if (zp n)
         nil
       (cons th (repeat th (- n 1)))))

; ---

; Problem 1-13:
; Define (popn n stk) to return the result of popping stk
; n times.  Thus,
; (popn 2 (push 1 (push 2 (push 3 nil)))) ==> (3).

; Answer 1-13:
(defun popn (n stk)
  (if (zp n)
      stk
    (popn (- n 1) (pop stk))))

; ---

; Problem 1-14:
; Define (update-nth n v x) so that the following is a
; theorem
; (implies (and (natp i)    ; i is an integer and 0 <= i
;               (natp j))
;          (equal (nth i (update-nth j v x))
;                 (if (equal i j)
;                     v
;                     (nth i x))))

; Answer 1-14:
(defun update-nth (n v list)
  (if (zp n)
      (cons v (cdr list))
    (cons (car list)
          (update-nth (- n 1) v (cdr list)))))

; ---

; Problem 1-15:
; Define (member e lst) to return t or nil indicating
; whether e is an element of list lst.
; (member 3 '(1 2 3 4)) ==> T
; (member 6 '(1 2 3 4)) ==> NIL

; Answer 1-15:
(defun member (e list)
  (if (endp list)
      nil
    (if (equal e (car list))
        t
      (member e (cdr list)))))

; ---

; Problem 1-16:
; Define (index e x) so that the following is a theorem:
; (implies (member e x)
;          (equal (nth (index e x) x) e))

; Answer 1-16:
(defun index (e lst)
  (if (endp lst)
      0
    (if (equal e (car lst))
        0
      (+ 1 (index e (cdr lst))))))

; ---

; Problem 1-17:
; A ``keyword argument list'' is a list of even length whose even elements
; (i.e., elements in the even positions, 0, 2, 4, ...) are keywords.  Thus,
; (:A 1 :B 2 :C 3) is a keyword argument list.  So is (:A :B :B 2 :C 3).  
; We say that a value for keyword key is ``supplied'' by x if key appears
; as an even element of x.  Define (suppliedp key x) to return t or nil
; to indicate whether key is supplied by x.

; Answer 1-17:
(defun suppliedp (key args)
  (if (endp args)
      nil
    (if (equal key (car args))
        t
      (suppliedp key (cdr (cdr args))))))

; ---

; Problem 1-18:
; If key is supplied by x, then its ``value'' is the element of x appearing
; immediately after the first even occurrence of key in x.  Define
; (actual key x) to return the value of key in x, assuming key is supplied.

; Answer 1-18:
(defun actual (key args)
  (if (endp args)
      nil
    (if (equal key (car args))
        (car (cdr args))
      (actual key (cdr (cdr args))))))

; ---

; Problem 1-19:
; A ``binding environment'' is a list of lists of the form
; ((x1 y1) (x2 y2) ...).  The xi are said to be the ``variables''
; and the yi are said to be their ``values.''  We say that a binding
; environment ``binds'' x if x occurs as one of the xi.  In that case,
; x is said to ``bound'' and it is bound to the ``value'' y, where y is
; (x y) is the first element in the environment binding x.

; Define (boundp x env) to return T or NIL indicating whether x is bound
; by binding environment env.

; Answer 1-19:
(defun boundp (var alist)
  (if (endp alist)
      nil
    (if (equal var (car (car alist)))
        t
      (boundp var (cdr alist)))))

; ---

; Problem 1-20:
; Define (binding x env) to return the value to which x is bound in binding
; environment env, assuming x is bound.

; Answer 1-20:
(defun binding (var alist)
  (if (endp alist)
      nil
    (if (equal var (car (car alist)))
        (car (cdr (car alist)))
      (binding var (cdr alist)))))

; ---

; Problem 1-21:
; Define (bind x y env) so that the following is a theorem
; (equal (binding v1 (bind v2 y env))
;        (if (equal v1 v2)
;            y
;          (binding v1 env)))

; Answer 1-21:
(defun bind (var val alist)
  (if (endp alist)
      (cons (cons var (cons val nil)) nil)
    (if (equal var (car (car alist)))
        (cons (cons var (cons val nil)) (cdr alist))
      (cons (car alist)
            (bind var val (cdr alist))))))

; Note:  Here's another definition that works perfectly well.

; (defun bind (var val alist)
;   (cons (cons var (cons val nil)) alist))

; ---

; Problem 1-22: The ``unsigned n-bit interpretation'' of a natural number x is
; the natural number denoted by the low order n bits of the binary
; representation of k.  Define (u-fix x n) to return the unsigned n-bit
; interpretation of x.  (The name ``u-fix'' stands for ``unsigned fix'' and
; suggests the idea of converting (or ``fixing'') an arbitrary natural into a
; particular format.)

; Answer 1-22:
(defun u-fix (x n)
  (mod x (expt 2 n)))

; ---

; Problem 1-23: The ``signed n-bit interpretation'' of a natural number x is the
; integer twos complement intepretation of the low order n bits of the binary
; representation of k.  The table below illustrates the signed 3-bit
; interpretation of a range of naturals numbers x.

; nat      binary       twos-complement
; x                       integer

; 0         000             0
; 1         001             1
; 2         010             2
; 3         011             3
; 4         100            -4
; 5         101            -3
; 6         110            -2
; 7         111            -1
; 8        1000             0
; 9        1001             1
;10        1010             2
;11        1011             3
;12        1100            -4
;13        1101            -3
;...        ...            ...

; Define (s-fix x n) to return the signed n-bit interpretation of the natural
; number x.

; Answer 1-23:
(defun s-fix (x n)
  (let ((temp (mod x (expt 2 n))))
    (if (< temp (expt 2 (- n 1)))
        temp
      (- temp (expt 2 n)))))

; ---

; Problem 1-24: A ``byte'' is an integer b that can be represented in 8-bits,
; e.g., (and (natp b) (< b 256)).  A list of bytes can be thought of as an
; unsighed base 256 ``big number'' in conventional ``big endian'' notation,
; e.g., where the car of the list is the most significant ``digit.''  Thus,
; (192 168 0 123) denotes the natural 3232235643, which is

; (+ (* 192 (expt 256 3))
;    (* 168 (expt 256 2))
;    (*   0 (expt 256 1))
;    (* 123 (expt 256 0)))

; Define (u-big lst) to return the unsigned base 256 big endian interpretation
; of the list of bytes lst.

; Answer 1-24:
(defun u-big1 (lst acc)
  (if (endp lst)
      acc
    (u-big1 (cdr lst)
           (+ (u-fix (car lst) 8)
              (* (expt 2 8) acc)))))

(defun u-big (lst) (u-big1 lst 0))

; ---

; Problem 1-25: The ``signed base 256 big endian interpretation'' of a list of k
; bytes is the 8*k twos-complement interpretation of the unsigned base 256 big
; endian interpretation.  Define (s-big lst) to return the signed base 256 big
; endian interpretation of the list of bytes lst.

; Answer 1-25:
(defun s-big (lst)
  (s-fix (u-big lst) (* 8 (len lst))))

; ---

; Problem 1-26:  Define (nextn n lst) to return the first n elements of the list
; lst.  You may assume that lst has at least n elements.  Thus
; (nextn 3 '(a b c d e)) ==> (A B C)

; Answer 1-26:
(defun nextn (n lst)
  (if (zp n)
      nil
    (cons (car lst)
          (nextn (- n 1) (cdr lst)))))

; ---

; Problem 1-27: Define (skipn n lst) to return the result of removing the first n
; elements from lst.  You may assume that lst has at least n elements.  Thus,
; (skipn 3 '(a b c d e)) ==> (D E).

; Answer 1-27:
(defun skipn (n lst)
  (if (zp n)
      lst
    (skipn (- n 1) (cdr lst))))

; --- the end ---

