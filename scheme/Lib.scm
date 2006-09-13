(module Lib mzscheme
  
  (require "Feedback.scm"
           "records.scm"
           "PreKernelRecords.scm")
  
  (require (only (lib "list.ss")
                 mergesort
                 filter)
           (lib "plt-match.ss")
           (only (lib "list.ss" "srfi" "1")
                 list-index
                 fold
                 fold-right
                 reduce
                 zip
                 unzip1
                 lset-union
                 lset-difference
                 lset-intersection
                 lset=))
  
  (provide (all-defined))
  (provide filter
           zip
           (rename unzip1 unzip))
  
  (define (ERR s2 s3)
    (mk_HOL_ERR "Lib" s2 s3))
  
  (define (curry f x y)
    (f (vector x y)))
  (define (uncurry f t)
    (let ((x (vector-ref t 0))
          (y (vector-ref t 1)))
      (f x y)))
  
  (define (|##| f g)
    (lambda (t)
      (let ((x (vector-ref t 0))
            (y (vector-ref t 1)))
        (vector (f x) (g y)))))
  
  (define (A f x)
    (f x))
  (define (B f g x)
    (f (g x)))
  (define (C f x y)
    (f y x))
  (define (I x)
    x)
  (define (K x y)
    x)
  (define (S f g x)
    (f x (g x)))
  (define (W f x)
    (f x x))
  
  (define (pair x y)
    (vector x y))
  (define fst
    (match-lambda
      ((vector x _)
       x)))
  (define snd
    (match-lambda
      ((vector _ y)
       y)))
  
  (define (can f x)
    (with-handlers ((exn:break? raise)
                    ((lambda (x) #t) (lambda (x) #f)))
      (f x)
      #t))
  
  (define (total f x)
    (with-handlers ((exn:break? raise)
                    ((lambda (x) #t) (lambda (x) 'NONE)))
      (make-SOME (f x))))
  
  (define (partial e f x)
    (let ((t (f x)))
      (cond ((eq? t 'NONE)
             (raise e))
            (else
             (SOME-x t)))))
  
  (define trye
    (let ((default_exn
           (ERR "trye" "original exn. not a HOL_ERR")))
      (lambda (f x)
        (with-handlers ((error_record? raise)
                        (exn:break? raise)
                        ((lambda (x) #t)
                         (lambda (x) (raise default_exn))))
          (f x)))))
  
  (define (try f x)
    (with-handlers (((lambda (x) #t)
                     Raise))
      (f x)))
  
  (define (assert_exn P x e)
    (if (P x)
        x
        (raise e)))
  
  (define (tryfind f t)
    (if (null? t)
        (raise (ERR "tryfind" "all applications failed"))
        (with-handlers ((exn:break? raise)
                        ((lambda (x) #t)
                         (f (cdr t))))
          (f (car t)))))
  
  (define el list-ref)
  
  (define index list-index)
  
  (define (map2 f L1 L2)
    (map f L1 L2))
  
  (define all andmap)
  (define all2 andmap)
  (define exists ormap)
  
  (define (first P l)
    (cond ((null? l)
           (raise (ERR "first" "unsatisfied predicate")))
          ((P (car l))
           (car l))
          (else
           (first P (cdr l)))))
  
  (define (split_after n alist)
    (if (> n 0)
        (letrec ((spa
                  (lambda (n L R)
                    (cond ((= n 0)
                           (vector (reverse L) R))
                          ((not (null? R))
                           (spa (sub1 n) (cons (car R) L) (cdr R)))
                          (else
                           (raise (ERR "split_after" "index too big")))))))
          (spa n '() alist))
        (raise (ERR "split_after" "negative index"))))
  
  (define (itlist f L base_value)
    (fold-right f base_value L))
  (define (itlist2 f L1 L2 base_value)
    (fold-right f base_value L1 L2))
  
  (define (rev_itlist f L base_value)
    (fold f base_value L))
  (define (rev_itlist2 f L1 L2 base_value)
    (fold f base_value L1 L2))
  
  (define (end_itlist f L)
    (cond ((null? L)
           (raise (ERR "end_itlist" "list too short")))
          ((null? (cdr L))
           (car L))
          (else
           (f (car L) (end_itlist f (cdr L))))))
  
  (define gather filter)
  
  (define (combine t)
    (let ((l1 (vector-ref t 0))
          (l2 (vector-ref t 1)))
      (zip l1 l2)))
  
  (define split unzip1)
  
  (define (mapfilter f lst)
    (itlist (lambda (i L)
              (with-handlers ((exn:break? raise)
                              ((lambda (x) #t) (lambda (x) L)))
                (f (cons i L))))
            lst
            '()))
  
  ;strange
  (define (flatten lst)
    (cond ((null? lst)
           '())
          ((null? (car lst))
           (flatten (cdr lst)))
          (else
           (cons (caar lst)
                 (flatten (cons (cdar lst)
                                (cddr lst)))))))
  
  (define front_last
    (letrec ((fl
              (lambda (acc lst)
                (cond ((null? lst)
                       (raise (ERR "front_last" "empty list")))
                      ((null? (cdr lst))
                       (vector (reverse acc) (car lst)))
                      (else
                       (fl (cons (car lst) acc)
                           (cdr lst)))))))
      (lambda (l)
        (fl '() l)))) 
  
  (define (butlast l)
    (with-handlers ((error_record?
                     (lambda (x) (raise (ERR "butlast" "empty list")))))
      (fst (front_last l))))
  
  ;last
  
  (define pluck
    (letrec ((pl
              (lambda (P A lst)
                (cond ((null? lst)
                       (raise (ERR "pluck" "predicate not satisfied")))
                      ((P (car lst))
                       (vector (car lst) (rev_itlist cons A (cdr lst))))
                      (else
                       (pl P (cons (car lst) A) (cdr lst)))))))
      (lambda (P t)
        (pl P '() t))))
  
  (define funpow
    (letrec ((iter
              (lambda (n f res)
                (if (= n 0)
                    res
                    (iter (sub1 n) f (f res))))))
      (lambda (n f x)
        (if (< n 0)
            x
            (iter n f x)))))
  
  ;record
  (define-struct LAST (a))
  
  (define repeat
    (letrec ((loop
              (lambda (f x)
                (loop f
                      (with-handlers
                          ((exn:break? raise)
                           ((lambda (x) #t) (raise (make-LAST x))))
                        (f x))))))
      (lambda (f x)
        (with-handlers ((LAST? LAST-a))
          (loop f x)))))
  
  (define (enumerate i lst)
    (if (null? lst)
        lst
        (cons (vector i (car lst))
              (enumerate (add1 i) (cdr lst)))))
  
  (define upto
    (letrec ((up
              (lambda (t i A)
                (if (> i t)
                    A
                    (up t (add1 i) (cons i A))))))
      (lambda (b t)
        (reverse (up t b '())))))
  
  (define list_compare
    (match-lambda*
      ((list cfn (vector (list) (list)))
       'EQUAL)
      ((list cfn (vector (list) _))
       'LESS)
      ((list cfn (vector _ (list)))
       'GREATER)
      ((list cfn (vector (list-rest h1 t1) (list-rest h2 t2)))
       (let ((t (cfn (vector h1 h2))))
         (if (eq? t 'EQUAL)
             (list_compare cfn t1 t2)
             t)))))
  
  (define pair_compare
    (match-lambda*
      ((list (vector acmp bcmp)
             (vector (vector a1 b1)
                     (vector a2 b2)))
       (let ((t (acmp (vector a1 a2))))
         (if (eq? t 'EQUAL)
             (bcmp (vector b1 b2))
             (t))))))
  
  (define (measure_cmp f t)
    (let ((x (vector-ref t 0))
          (y (vector-ref t 1)))
      (let ((a (f x))
            (b (f y)))
        (cond ((> a b)
               'GREATER)
              ((< a b)
               'LESS)
              (else ;(= a b)
               'EQUAL)))))
  
  (define (inv_img_cmp f c t)
    (let ((x (vector-ref t 0))
          (y (vector-ref t 1)))
      (c (vector (f x) (f y)))))
  
  (define (for base top f)
    (if (> base top)
        '()
        (f (cons base (for (add1 base) top f)))))
  
  (define (for_se base top f)
    (unless (> base top)
      (begin (f base)
             (for (add1 base) top f))))
  
  ;assoc is a Scheme prim, renamed as assec
  (define (assec item lst)
    (cond ((null? lst)
           (raise (ERR "assoc" "not found")))
          ((equal? item (vector-ref (car lst) 0))
           (vector-ref (car lst) 1))
          (else
           (assec item (cdr lst)))))
  (define (rev_assoc item lst)
    (cond ((null? lst)
           (raise (ERR "assoc" "not found")))
          ((equal? item (vector-ref (car lst) 1))
           (vector-ref (car lst) 0))
          (else
           (rev_assoc item (cdr lst)))))
  ;assoc1 already imported
  (define (assoc2 item lst)
    (cond ((null? lst)
           'NONE)
          ((equal? item (vector-ref (car lst) 1))
           (make-SOME (car lst)))
          (else
           (assoc1 item (cdr lst)))))
  
  ;sort
  (define (int_sort lst)
    (mergesort lst <=))
  
  (define-struct subst (redex residue) #f)
  
  (define subst_assoc
    (match-lambda*
      ((list test (list))
       'NONE)
      ((list test (list-rest (struct subst (redex residue)) rst))
       (if (test redex)
           (make-SOME residue)
           (subst_assoc test rst)))))
  
  (define ||-> make-subst)
  
  (define mem member)
  
  (define (insert i L)
    (if (mem i L)
        L
        (cons i L)))
  
  (define (mk_set lst)
    (if (null? lst)
        lst
        (insert (car lst) (mk_set (cdr lst)))))
  
  (define (union S1 S2)
    (lset-union equal? S1 S2))
  
  (define (U set_o_sets)
    (apply lset-union (cons = set_o_sets)))
  
  (define (set_diff a b)
    (lset-difference equal? a b))
  (define subtract set_diff)
  
  (define (intersect S1 S2)
    (lset-intersection equal? S1 S2))
  
  (define (null_intersection s1 s2)
    (cond ((null? s1)
           #t)
          ((null? s2)
           #t)
          ((mem (car s1) s2)
           #f)
          (else
           (null_intersection (cdr s1) s2))))
  
  (define (set_eq S1 S2)
    (lset= equal? S1 S2))
  
  (define (op_mem eq_func i lst)
    (if (null? lst)
        #f
        (or (eq_func i (car lst))
            (op_mem eq_func i (cdr lst)))))
  
  (define (op_insert eq_func i L)
    (if (op_mem eq_func i L)
        L
        (cons i L)))
  
  (define (op_mk_set eqf lst)
    (if (null? lst)
        lst
        (op_insert eqf (car lst) (mk_set (cdr lst)))))
  
  (define op_union lset-union)
  (define op_intersect lset-intersection)
  (define op_set_diff lset-difference)
  
  (define int_to_string number->string)
  (define string_to_int string->number)
  
  (define say display)
  
  ;no mlquote available in PLT
  (define (stringquote s)
    (string-append "\"" s "\""))
  (define mlquote stringquote)
  
  (define (is_substring s1 s2)
    (and (regexp-match s1 s2)
         #t))
  
  (define (prime s)
    (string-append s "'"))
  (define (unprime s)
    (let ((n (sub1 (string-length s))))
      (if (and (<= 0 n)
               (char=? (string-ref s n) #\'))
          (substring s 0 n)
          (raise (ERR "unprime" "string doesn't end with a prime")))))
  
  (define (commafy lst)
    (if (or (null? lst)
            (null? (cdr lst)))
        lst
        (cons (car lst)
              (cons ", " (commafy (cdr lst))))))
  
  (define (words2 sep string)
    (snd (itlist (lambda (ch temp)
                   (let ((chs (vector-ref temp 0))
                         (tokl (vector-ref temp 1)))
                     (if (equal? ch sep)
                         (if (null? chs)
                             (vector '() tokl)
                             (vector '() (cons (apply string-append chs)
                                               tokl)))
                         (vector (cons ch chs) tokl))))
                 (vector (cons sep list) string)
                 (vector '() '()))))
  
  (define (hash size)
    (lambda (x)
      (modulo (equal-hash-code x) size)))
  
  (define (end_time)
    (printf "process: ~a ms~ngc: ~a ms~n"
            (current-process-milliseconds)
            (current-gc-milliseconds)))
  
  ;time is a mzscheme primitve, although a little different in interface
  
  (define (with_flag temp f x)
    (let* ((flag (vector-ref temp 0))
           (b (vector-ref temp 1))
           (fval (unbox flag)))
      (set-box! flag b)
      (begin0 (with-handlers (((lambda (x) #t)
                               (lambda (e)
                                 (set-box! flag fval)
                                 (raise e))))
                (f x))
              (set-box! flag fval))))
  
  (define-struct STRM (mutator project state init))
  
  (define (mk_istream f i g)
    (make-STRM f g (box i) i))
  (define (next strm)
    (let ((mutator (STRM-mutator strm))
          (state (STRM-state strm)))
      (set-box! state
                (mutator (unbox state)))
      strm))
  (define (state strm)
    (let ((project (STRM-project strm))
          (state (STRM-state strm)))
      (project (unbox state))))
  (define (reset strm)
    (let ((init (STRM-init strm))
          (state (STRM-state strm)))
      (set-box! state init)
      strm))
  
  (define-struct DIFF (a))
  
  (define (delta_apply f x)
    (match (f x)
      ('SAME
        x)
      ((struct DIFF (y))
       y)))
  
  (define delta_map
    (match-lambda*
      ((list f (list))
       'SAME)
      ((list f (list-rest h t))
       (match (vector (f h) (delta_map f t))
         ((vector 'SAME 'SAME)
          'SAME)
         ((vector 'SAME (struct DIFF (t1)))
          (make-DIFF (cons h t1)))
         ((vector (struct DIFF (h1)) 'SAME)
          (make-DIFF (cons h1 t)))
         ((vector (struct DIFF (h1)) (struct DIFF (t1)))
          (make-DIFF (cons h1 t1)))))))
  
  (define delta_pair
    (match-lambda*
      ((list f g (vector x y))
       (match (vector (f x) (g y))
         ((vector 'SAME 'SAME)
          'SAME)
         ((vector 'SAME (struct DIFF (y1)))
          (make-DIFF (vector x y1)))
         ((vector (struct DIFF (x1)) 'SAME)
          (make-DIFF (vector x1 y)))
         ((vector (struct DIFF (x1)) (struct DIFF (y1)))
          (make-DIFF (vector x1 y1)))))))
  
  ;Scheme read automatically handles comments  
  )
