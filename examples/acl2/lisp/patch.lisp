(in-package "ACL2")

(set-compile-fns t)

(defconst *synp-trans-err-string*
  "A synp term must take three quoted arguments, unlike ~x0.  Normally, a call ~
   to synp is the result of the macroexpansion of a call to syntaxp or ~
   bind-free, but this does not seem to be the case here.  If you believe this ~
   error message is itself in error please contact the maintainers of ACL2.")

(defun translate11 (x stobjs-out bindings inclp known-stobjs ctx w state)

; Bindings is an alist binding symbols either to their corresponding
; STOBJS-OUT or to symbols.  The only symbols used are (about-to-be
; introduced) function symbols or the keyword :STOBJS-OUT.  When fn is
; bound to gn it means we have determined that the STOBJS-OUT of fn is
; that of gn.  We allow fn to be bound to itself -- indeed, it is
; required initially!  (This allows bindings to double as a recording
; of all the names currently being introduced.)

; Stobjs-out is one of:

; t              - meaning we do not care about multiple-value or stobj 
;                  restrictions (as when translating proposed theorems).
; (s1 s2 ... sk) - a list of 1 or more stobj flags indicating where stobjs
;                  are returned in the translation of x
; fn             - a function name, indicating that we are trying to deduce 
;                  the stobjs-out setting for fn from some output branch, x,
;                  of its body, as we translate.  We also enforce prohibitions
;                  against the use of DEFUN, IN-PACKAGE, etc inside bodies.
; :stobjs-out    - like a function name, except we know we are NOT in a defun
;                  body and allow DEFUN, IN-PACKAGE, etc.

; See the essay on STOBJS-IN and STOBJS-OUT, above.

; When stobjs-out is a symbol, it must be dereferenced through bindings
; before using it.  [One might think that we follow the convention of keeping
; it dereferenced, e.g., by using the new value whenever we bind it.
; But that is hard since the binding may come deep in some recursive
; call of translate.]

; T always deferences to t and nothing else dereferences to t.  So you
; can check (eq stobjs-out t) without dereferencing to know whether we
; care about the stobjs-out conditions.

; Inclp is t or nil and changes the precise meaning of a non-nil stobj
; flag, $s.  If inclp is nil, then $s means that the given stobj MUST
; appear in the corresponding slot.  If inclp is t, then $s means that
; the given stobj MAY appear in the corresponding slot.  At the
; moment, inclp is always set to nil initially and is set to t only
; when this function, in some recursive call, has determined that it
; is safe to allow non-live stobjs into stobj positions.

; Known-stobjs is a subset of the list of all stobjs known in world w,
; or else known-stobjs is T and denotes all the stobjs in w.  A name
; is considered a stobj iff it is in known-stobjs.  This allows us to
; implement the :STOBJS declaration in defuns, by which the user can
; declare the stobjs in a function.

; Keep this in sync with oneify.

  (cond
   ((f-big-clock-negative-p state)
    (trans-er soft ctx
              "Translate ran out of time!  This is almost certainly ~
               caused by a loop in macro expansion."))

; We handle both the (quote x) and atom case together because both
; have the same effects on calculating the stobjs-out.

   ((or (atom x) (eq (car x) 'quote))
    (let* ((stobjs-out (translate-deref stobjs-out bindings))
           (vc (legal-variable-or-constant-namep x))
           (const (and (eq vc 'constant)
                       (defined-constant x w))))
      (cond
       ((and (symbolp x)
             (not (keywordp x))
             (not vc))
        (trans-er soft ctx
                  "The symbol ~x0 is being used as a variable, ~
                   or constant symbol but does not have the proper ~
                   syntax.  Such names must ~@1.  See :DOC name."
                  x
                  (tilde-@-illegal-variable-or-constant-name-phrase x)))
       ((and (eq vc 'constant)
             (not const))
        (trans-er soft ctx
                  "The symbol ~x0 (in package ~x1) has the syntax of ~
                   a constant, but has not been defined."
                  x
                  (symbol-package-name x)))

       ((and (not (atom x)) (not (termp x w)))
        (trans-er soft ctx
                  "The proper form of a quoted constant is (quote x), ~
                   but ~x0 is not of this form."
                  x))

; We now know that x denotes a term.  Let transx be that term.

       (t (let ((transx (cond ((keywordp x) (kwote x))
                              ((symbolp x)
                               (cond ((eq vc 'constant) const)
                                     (t x)))
                              ((atom x) (kwote x))
                              (t x))))

; Now consider the specified stobjs-out.  It is fully dereferenced.
; So there are three cases: (1) we don't care about stobjs-out, (2)
; stobjs-out tells us exactly what kind of output is legal here and we
; must check, or (3) stobjs-out is an unknown but we now know its
; value and can bind it.

            (cond
             ((eq stobjs-out t)              ;;; (1)
              (trans-value transx))
             ((consp stobjs-out)             ;;; (2)
              (cond
               ((cdr stobjs-out)
                (trans-er soft ctx
                          "One value, ~x0, is being returned where ~
                           ~x1 values were expected."
                          x (length stobjs-out)))
               ((and (null (car stobjs-out))
                     (stobjp transx known-stobjs w))

; Warning: We ignore the inclp flag in this case.  Even if inclp = t,
; which permits non-stobjs into stobj slots, we still prohibit stobjs
; from going into non-stobj slots.  Why?  Because the stobj in
; question might be a live one and might be treated ``surprisingly''
; by non-stobj functions, e.g., we might take the car of
; *the-live-state*.

                (trans-er soft ctx
                          "A single-threaded object, namely ~x0, is ~
                           being used where an ordinary object is ~
                           expected."
                          transx))
               ((and (car stobjs-out)
                     (not (or inclp
                              (eq (car stobjs-out) transx))))
                (cond
                 ((stobjp transx known-stobjs w)
                  (trans-er soft ctx
                            "The single-threaded object ~x0 is being ~
                             used where the single-threaded ~
                             object ~x1 was expected."
                            transx (car stobjs-out)))
                 (t
                  (trans-er soft ctx
                            "The ordinary object ~x0 is being ~
                             used where the single-threaded ~
                             object ~x1 was expected."
                            transx (car stobjs-out)))))
               (t (trans-value transx))))
             (t                              ;;; (3)
              (let ((bindings
                     (translate-bind
                      stobjs-out
                      (list (if (stobjp transx known-stobjs w) transx nil))
                      bindings)))
                (trans-value transx)))))))))
   ((not (true-listp (cdr x)))
    (trans-er soft ctx
              "Function applications in ACL2 must end in NIL.  ~x0 is ~
               not of this form."
              x))
   ((not (symbolp (car x)))
    (cond ((or (not (consp (car x)))
               (not (eq (caar x) 'lambda)))
           (trans-er soft ctx
                     "Function applications in ACL2 must begin with a ~
                      symbol or LAMBDA expression.  ~x0 is not of ~
                      this form."
                     x))
          ((or (not (true-listp (car x)))
               (not (>= (length (car x)) 3))
               (not (true-listp (cadr (car x)))))
           (trans-er soft ctx
                     "Illegal LAMBDA expression: ~x0." x))
          ((not (= (length (cadr (car x))) (length (cdr x))))
           (trans-er soft ctx
                     "The LAMBDA expression ~x0 takes ~#1~[no ~
                      arguments~/1 argument~/~x2 arguments~] and is ~
                      being passed ~#3~[no arguments~/1 argument~/~x4 ~
                      arguments~]."
                     (car x)
                     (zero-one-or-more (length (cadr (car x))))
                     (length (cadr (car x)))
                     (zero-one-or-more (length (cdr x)))
                     (length (cdr x))))
          (t (translate11
              (list* 'let
                     (listlis (cadr (car x)) (cdr x))
                     (cddr (car x)))
              stobjs-out bindings inclp known-stobjs ctx w state))))
   ((and (not (eq stobjs-out t)) (eq (car x) 'mv))

; If stobjs-out is t we let normal macroexpansion handle mv.

    (let ((stobjs-out (translate-deref stobjs-out bindings)))
      (cond
       ((let ((len (length (cdr x))))
          (or (< len 2)
              (> len

; Keep the number below (which also occurs in the string) equal to the value of
; raw Lisp constant *number-of-return-values*.

                 32)))
        (cond ((< (length (cdr x)) 2)
               (trans-er soft ctx
                         "MV must be given at least two arguments, but ~x0 has ~
                          fewer than two arguments."
                         x))
              (t
               (trans-er soft ctx
                         "MV must be given no more than 32 arguments; thus ~x0 ~
                          has too many arguments."
                         x))))
       ((consp stobjs-out)
        (cond
         ((not (int= (length stobjs-out) (length (cdr x))))
          (trans-er soft ctx
                    "The expected number of return values is ~x0 but ~
                     the actual number of return values is ~x1."
                    (length stobjs-out)
                    (length (cdr x))))
         (t
          (trans-er-let*
           ((args (translate11-lst (cdr x) stobjs-out bindings
                                   inclp known-stobjs 'mv ctx w state)))
           (trans-value (listify args))))))
       (t (let* ((new-stobjs-out (compute-stobj-flags (cdr x)
                                                      known-stobjs
                                                      w))
                 (bindings
                  (translate-bind stobjs-out new-stobjs-out bindings)))

; When we compute new-stobjs-out, above, we do with untranslated
; terms.  The stobj slots of an mv must be occupied by stobj variable
; names!  If a slot is occupied by anything else, the occupant must be
; a single non-stobj.

            (cond
             ((not (no-duplicatesp (collect-non-x nil new-stobjs-out)))
              (trans-er soft ctx
                        "It is illegal to return more than one ~
                         reference to a given single-threaded object ~
                         in an MV form.  The form ~x0 is thus illegal."
                        x))
             (t
              (trans-er-let*
               ((args
                 (translate11-lst (cdr x) new-stobjs-out
                                  bindings inclp known-stobjs
                                  'mv ctx w state)))
               (trans-value (listify args))))))))))

   ((and (not (eq stobjs-out t)) (eq (car x) 'mv-let))

; If stobjs-out is t, we let normal macroexpansion handle mv-let.

    (translate11-mv-let x stobjs-out bindings inclp known-stobjs
                        nil nil ; stobj info
                        ctx w state))
   ((and bindings
         (not (eq (caar bindings) :stobjs-out))
         (member (car x) '(defun defmacro in-package progn include-book
                            certify-book)))
    (trans-er soft ctx
              "We do not permit the use of ~x0 inside of code to be ~
               executed by Common Lisp because its Common Lisp ~
               meaning differs from its ACL2 meaning."
              (car x)))
   ((and bindings
         (not (eq (caar bindings) :stobjs-out))
         (member (car x) '(defpkg defconst defstobj defthm defaxiom
                            deflabel defdoc deftheory
                            verify-termination verify-guards
                            in-theory in-arithmetic-theory
                            push-untouchable table certify-book value-triple)))
    (trans-er soft ctx
              "We do not permit the use of ~x0 inside of code to be ~
               executed by Common Lisp because its Common Lisp ~
               runtime value and effect differs from its ACL2 meaning."
              (car x)))
   ((eq (car x) 'translate-and-test)
    (cond ((not (equal (length x) 3))
           (trans-er soft ctx
                     "TRANSLATE-AND-TEST requires exactly two ~
                      arguments: ~x0 ."
                     x))
          (t (trans-er-let*
              ((ans (translate11 (caddr x) stobjs-out bindings inclp
                                 known-stobjs ctx w state)))

; The next mv-let is spiritually just a continuation of the trans-er-let*
; above, as though to say "and let  test-term be (translate11 (list ...)...)"
; except that we do not want to touch the current setting of bindings nor
; do we wish to permit the current bindings to play a role in the translation
; of the test.

              (mv-let
               (test-erp test-term test-bindings state)
               (translate11 (list (cadr x) 'form)
                           '(nil) nil inclp known-stobjs ctx w state)
               (declare (ignore test-bindings))
               (cond
                (test-erp (mv test-erp test-term bindings state))
                (t
                 (mv-let (erp msg latches)
                         (ev test-term (list (cons 'form ans)) state nil nil)
                         (declare (ignore latches))
                         (cond
                          (erp
                           (trans-er soft ctx
                                     "The attempt to evaluate the ~
                                      TRANSLATE-AND-TEST test, ~X01, ~
                                      when FORM is ~X21, failed with ~
                                      the evaluation error:~%~%``~@3''"
                                     (cadr x) nil ans msg))
                          ((or (consp msg)
                               (stringp msg))
                           (trans-er soft ctx "~@0" msg))
                          (t (trans-value ans)))))))))))
   ((eq (car x) 'with-local-stobj)

; Even if stobjs-out is t, we do not let normal macroexpansion handle
; with-local-stobj, because we want to make sure that we are dealing with a
; stobj.  Otherwise, the raw lisp code will bind a bogus live stobj variable;
; although not particularly harmful, that will give rise to an inappropriate
; compiler warning about not declaring the variable unused.

    (mv-let (erp st mv-let-form creator)
            (parse-with-local-stobj (cdr x))
            (cond
             (erp
              (trans-er soft ctx
                        "Ill-formed with-local-stobj form, ~x0.  ~
                         See :DOC with-local-stobj."
                        x))
             ((not (and st
                        (eq st (stobj-creatorp creator w))))
              (trans-er soft ctx
                        "Illegal with-local-stobj form, ~x0.  The first ~
                         argument must be the name of a stobj other than ~
                         STATE and the third, if supplied, must be its ~
                         creator function.  See :DOC with-local-stobj."
                        x))
             ((eq stobjs-out :stobjs-out)
              (trans-er soft ctx
                        "Calls of with-local-stobj, such as ~x0, cannot be ~
                         evaluated directly in the top-level loop.  ~
                         See :DOC with-local-stobj."
                        x))
             (t
              (translate11-mv-let mv-let-form stobjs-out bindings inclp
                                  known-stobjs st creator ctx w state)))))
   ((getprop (car x) 'macro-body nil 'current-acl2-world w)
    (cond
     ((member (car x) (global-val 'untouchables w))

; If this error burns you during system maintenance, you can subvert our security
; by setting untouchables to nil.  This must be done in raw Lisp.  But then
; you must install the world in which you've done the set, which means you must
; call set-w.  But you can't call set-w outside of our loop.  So you have to
; (a) provoke a read error in the ACL2 loop by typing (a , b).
; (b) (set-w 'extension (global-set 'untouchables nil (w state)) state)
; (c) :q
      
      (trans-er soft ctx
                "It is illegal to call ~x0 because it has been placed ~
                 on untouchables."
                (car x)))
     (t
      (mv-let (erp expansion state)
              (macroexpand1 x ctx state)
              (cond (erp (mv t nil bindings state))
                    (t (translate11 expansion stobjs-out bindings inclp
                                    known-stobjs ctx w
                                    (f-decrement-big-clock state))))))))
   ((eq (car x) 'let)

; Warning:  If the final form of a translated let is changed,
; be sure to reconsider translated-acl2-unwind-protectp.

; In translating LET and MV-LET we generate "open lambdas" as function
; symbols.  The main reason we did this was to prevent translate from
; exploding in our faces when presented with typical DEFUNs (e.g., our
; own code).  Note that such LAMBDAs can be expanded away.  However,
; expansion affects the guards.  Consider (let ((x (car 3))) t), which
; expands to ((lambda (x) t) (car 3)).

    (cond
     ((not (and (>= (length x) 3)
                (doubleton-list-p (cadr x))))
      (trans-er soft ctx
                "The proper form of a let is (let bindings dcl ... ~
                 dcl body), where bindings has the form ((v1 term) ~
                 ... (vn term)) and the vi are distinct variables, ~
                 not constants, and do not begin with an asterisk, ~
                 but ~x0 does not have this form." x))
     ((not (arglistp (strip-cars (cadr x))))
      (mv-let (culprit explan)
              (find-first-bad-arg (strip-cars (cadr x)))
              (trans-er soft ctx
                        "The form ~x0 is an improper let expression ~
                         because it attempts to bind ~x1, which ~@2."
                        x culprit explan)))
     ((and (not (eq stobjs-out t))
           (not (equal 1 (length (cadr x))))
           (not (all-nils (compute-stobj-flags (strip-cars (cadr x))
                                               known-stobjs
                                               w))))
      (trans-er soft ctx
                "A single-threaded object name, such as ~x0, may be ~
                 LET-bound only when it is the only binding in the ~
                 LET, but ~x1 binds more than one variable."
                (car
                 (collect-non-x nil
                  (compute-stobj-flags (strip-cars (cadr x))
                                       known-stobjs
                                       w)))
                x))
     (t (let* ((bound-vars (strip-cars (cadr x)))
               (stobjs-bound
                (collect-non-x nil (compute-stobj-flags bound-vars
                                                       known-stobjs
                                                       w)))
               (body (car (last x))))
          (mv-let
           (erp edcls state)
           (collect-declarations (butlast (cddr x) 1)
                                 bound-vars 'let state ctx)
           (cond
            (erp (mv t nil bindings state))
            (t
             (trans-er-let*
              ((value-forms
                (cond ((and (not (eq stobjs-out t))
                            stobjs-bound)

; In this case, we know that the only variable of the LET is a stobj name.
; Note that (list (car bound-vars)) is thus a stobjs-out specifying
; a single result consisting of that stobj.

                       (trans-er-let*
                        ((val (translate11 (cadr (car (cadr x)))
                                           (list (car bound-vars))
                                           bindings

; One might be tempted to allow the stobj name to be bound to anything
; (i.e., inclp = t) if no stobjs come out.  But we have a rule that
; says if a stobj name is bound it must come out.  (See the big error
; messages below, for example.)  So I don't implement the inclusive
; treatment of LET bindings.

                                           inclp known-stobjs ctx w state)))
                        (trans-value (list val))))
                      (t (translate11-lst (strip-cadrs (cadr x))
                                          (if (eq stobjs-out t)
                                              t
                                            nil)       ;;; '(nil ... nil)
                                          bindings inclp known-stobjs
                                          "in a LET binding (or ~
                                           LAMBDA application)"
                                          ctx w state))))
               (tbody
                (translate11 body stobjs-out bindings inclp known-stobjs
                             ctx w state))
               (tdcls (translate11-lst
                       (translate-dcl-lst edcls)
                       (if (eq stobjs-out t)
                           t
                         nil)         ;;; '(nil ... nil)
                       bindings inclp known-stobjs
                       "in a DECLARE form in a LET (or LAMBDA)"
                       ctx w state)))
              (let ((used-vars (union-eq (all-vars tbody)
                                         (all-vars1-lst tdcls nil)))
                    (ignore-vars (ignore-vars edcls))
                    (stobjs-out (translate-deref stobjs-out bindings)))
                (cond 
                 ((and (not (eq stobjs-out t))
                       stobjs-bound
                       (not (consp stobjs-out)))
                  (trans-er soft ctx
                            "The single-threaded object~#0~[ ~&0 ~
                             has~/s ~&0 have~] been bound in a LET.  ~
                             It is a requirement that ~#0~[this ~
                             object~/these objects~] be among the ~
                             outputs of the LET.  But, at the time at ~
                             which we process the LET, we are unable ~
                             to determine what the outputs are and so ~
                             cannot allow it.  This situation arises ~
                             when the output of the LET is a ~
                             recursive call of the function being ~
                             admitted and the call is encountered ~
                             before we have encountered the first ~
                             base case of the function (which would ~
                             tell us what single-threaded objects are ~
                             being returned). In the case of the ~
                             admission of a clique of ~
                             mutually-recursive functions, the ~
                             situation can additionally arise when ~
                             the output of the LET is a call of a ~
                             function in the clique and that function ~
                             appears in the clique after the ~
                             definition in question.  This situation ~
                             can be eliminated by rearranging the ~
                             order of the branches of an IF and/or ~
                             rearranging the order of the ~
                             presentation of a clique of mutually ~
                             recursive functions."
                            stobjs-bound))
                 ((and (not (eq stobjs-out t))
                       stobjs-bound
                       (not (subsetp stobjs-bound
                                     (collect-non-x nil stobjs-out))))
                  (let ((stobjs-returned (collect-non-x nil stobjs-out)))
                    (trans-er soft ctx
                              "The single-threaded object~#0~[ ~&0 ~
                               has~/s ~&0 have~] been bound in a ~
                               LET.  It is a requirement that ~
                               ~#0~[this object~/these objects~] be ~
                               among the outputs of the LET, but ~
                               ~#0~[it is~/they are~] not.  The LET ~
                               returns ~#1~[no single-threaded ~
                               objects~/the single-threaded object ~
                               ~&2~/the single-threaded objects ~&2~]."
                              (set-difference-eq stobjs-bound stobjs-returned)
                              (zero-one-or-more stobjs-returned)
                              stobjs-returned)))
                 ((intersectp-eq used-vars ignore-vars)
                  (trans-er soft ctx
                            "Contrary to the declaration that ~#0~[it is~/they ~
                             are~] IGNOREd, the variable~#0~[ ~&0 is~/s ~&0 ~
                             are~] used in the body of the LET expression that ~
                             binds ~&1."
                            (intersection-eq used-vars ignore-vars)
                            bound-vars))
                 (t
                  (let* ((diff (set-difference-eq
                                bound-vars
                                (union-eq used-vars ignore-vars)))
                         (ignore-ok
                          (if (null diff)
                              t
                            (cdr (assoc-eq
                                  :ignore-ok
                                  (table-alist 'acl2-defaults-table w))))))
                    (cond
                     ((null ignore-ok)
                      (trans-er soft ctx
                                "The variable~#0~[ ~&0 is~/s ~&0 are~] not ~
                                 used in the body of the LET expression that ~
                                 binds ~&1.  But ~&0 ~#0~[is~/are~] not ~
                                 declared IGNOREd.  See :DOC set-ignore-ok."
                                diff
                                bound-vars))
                     (t
                      (pprogn
                       (cond
                        ((eq ignore-ok :warn)
                         (warning$ ctx "Ignored-variables"
                                   "The variable~#0~[ ~&0 is~/s ~&0 are~] not ~
                                    used in the body of the LET expression ~
                                    that binds ~&1.  But ~&0 ~#0~[is~/are~] ~
                                    not declared IGNOREd.  See :DOC ~
                                    set-ignore-ok."
                                   (set-difference-eq
                                    bound-vars
                                    (union-eq used-vars ignore-vars))
                                   bound-vars))
                        (t state))
                       (let* ((tbody
                               (cond
                                (tdcls
                                 (fcons-term* 'prog2$
                                              (dcl-guardian tdcls)
                                              tbody))
                                (t tbody)))
                              (body-vars (all-vars tbody))
                              (extra-body-vars (set-difference-eq
                                                body-vars
                                                bound-vars)))
                         (trans-value
                          (cons (make-lambda
                                 (append bound-vars extra-body-vars)
                                 tbody)

; See the analogous line in the handling of MV-LET for an explanation
; of hide-ignored-actuals.

                                (append
                                 (hide-ignored-actuals
                                  ignore-vars bound-vars value-forms)
                                 extra-body-vars)))))))))))))))))))
   ((and (not (eq stobjs-out t))
         (null (cdr x)) ; optimization
         (stobj-creatorp (car x) w))
    (trans-er soft ctx
              "It is illegal to call ~x0 in this context because it is a stobj ~
               creator.  Stobj creators cannot be called directly except in ~
               theorems.  If you did not explicitly call a stobj creator, then ~
               this error is probably due to an attempt to evaluate a ~
               with-local-stobj form directly in the top-level loop.  Such ~
               forms are only allowed in the bodies of functions and in ~
               theorems.  Also see :DOC with-local-stobj."
              (car x)))
   ((equal (arity (car x) w) (length (cdr x)))
    (cond ((member (car x) (global-val 'untouchables w))
           (trans-er soft ctx
                     "It is illegal to call ~x0 because it has been ~
                      placed on untouchables."
                     (car x)))
          ((eq (car x) 'if)
           (cond ((stobjp (cadr x) known-stobjs w)
                  (trans-er soft ctx
                            "It is illegal to test on a ~
                             single-threaded object such as ~x0."
                            (cadr x)))

; Because (cadr x) has not yet been translated, we do not really know
; it is not a stobj!  It could be a macro call that expands to a
; stobj.'  The error message above is just to be helpful.  An accurate
; check is made below.

                 (t (trans-er-let*
                     ((arg1 (translate11 (cadr x)
                                         (if (eq stobjs-out t)
                                             t
                                           '(nil))
                                         bindings inclp known-stobjs
                                         ctx w state))
                      (arg2 (translate11 (caddr x)
                                         stobjs-out bindings inclp known-stobjs
                                         ctx w state))
                      (arg3 (translate11 (cadddr x)
                                         stobjs-out bindings inclp known-stobjs
                                         ctx w state)))
                     (trans-value (fcons-term* 'if arg1 arg2 arg3))))))
          ((eq (car x) 'synp)

; Synp is a bit odd.  We store the quotation of the term to be evaluated in the
; third arg of the synp form.  We store the quotation so that ACL2 will not see
; the term as a potential induction candidate.  (Eric Smith first pointed out
; this issue.)  This, however forces us to treat synp specially here in order
; to translate the term to be evaluated and thereby get a proper ACL2 term.
; Without this special treatment (cadr x), for instance, would be left alone
; whereas it needs to be translated into (car (cdr x)).

; This mangling of the third arg of synp is sound because synp always returns
; t.

; Robert Krug has mentioned the possibility that the known-stobjs below could
; perhaps be t.  This would allow a function called by synp to use, although
; not change, stobjs.  If this is changed, change the referances to stobjs in
; the documentation for syntaxp and bind-free as appropriate.  But before
; making such a change, consider this: no live user-defined stobj will ever
; appear in the unifying substitution that binds variables in the evg of
; (cadddr x).  So it seems that such a relaxation would not be of much value.

           (cond ((not (eq stobjs-out t))
                  (trans-er soft ctx
                            "A call to synp is not allowed here.  This ~
                             call may have come from the use of syntaxp ~
                             or bind-free within a function definition ~
                             since these two macros expand into calls to ~
                             synp.  The form we were translating when we ~
                             encountered this problem is ~x0.  If you ~
                             believe this error message is itself in error ~
                             or that we have been too restrictive, please ~
                             contact the maintainers of ACL2."
                            x))
                 ((eql (length x) 4)
                  (trans-er-let*
                   ((quoted-vars (translate11 (cadr x)
                                              '(nil) ; stobjs-out
                                              bindings
                                              inclp
                                              '(state) ; known-stobjs
                                              ctx w state))
                    (quoted-user-form (translate11 (caddr x)
                                                   '(nil) ; stobjs-out
                                                   bindings
                                                   inclp
                                                   '(state) ; known-stobjs
                                                   ctx w state))
                    (quoted-term (translate11 (cadddr x)
                                              '(nil) ; stobjs-out
                                              bindings
                                              inclp
                                              '(state) ; known-stobjs
                                              ctx w state)))
                   (let ((quoted-term (if (quotep quoted-term)
                                          quoted-term
                                        (sublis-var nil quoted-term))))
                     (cond ((quotep quoted-term)
                            (trans-er-let*
                             ((term-to-be-evaluated
                               (translate11 (cadr quoted-term)
                                            '(nil) ; stobjs-out
                                            bindings
                                            inclp
                                            '(state) ; known-stobjs
                                            ctx w state)))
                             (let ((quoted-vars (if (quotep quoted-vars)
                                                    quoted-vars
                                                  (sublis-var nil quoted-vars)))
                                   (quoted-user-form (if (quotep quoted-user-form)
                                                         quoted-user-form
                                                       (sublis-var nil
                                                                   quoted-user-form))))
                               (cond ((and (quotep quoted-vars)
                                           (quotep quoted-user-form))
                                      (trans-value 
                                       (fcons-term* 'synp quoted-vars quoted-user-form
                                                    (kwote term-to-be-evaluated))))
                                     (t (trans-er soft ctx
                                                  *synp-trans-err-string*
                                                  x))))))
                           (t
                            (trans-er soft ctx
                                      *synp-trans-err-string*
                                      x))))))
                 (t
                  (trans-er soft ctx
                            *synp-trans-err-string*
                            x))))
          ((eq (car x) 'prog2$)
           (trans-er-let*
            ((arg1 (translate11 (cadr x)
                                (if (eq stobjs-out t)
                                    t
                                  '(nil))
                                bindings inclp known-stobjs ctx w state))
             (arg2 (translate11 (caddr x)
                                stobjs-out bindings inclp known-stobjs
                                ctx w state)))
            (trans-value (fcons-term* 'prog2$ arg1 arg2))))
          ((eq (car x) 'must-be-equal)

; We need to know that the first argument of must-be-equal has the same
; signature as the second argument.  If for example we have (mv-let (x y)
; (must-be-equal <logic-form> <exec-form>)), but <exec-form> had signature *,
; then Common Lisp would get confused during evaluation.

           (trans-er-let*
            ((arg1 (translate11 (cadr x)
                                stobjs-out bindings inclp known-stobjs
                                ctx w state)) 
             (arg2 (translate11 (caddr x)
                                stobjs-out bindings inclp known-stobjs
                                ctx w state)))
            (cond ((ffnnamep 'must-be-equal arg2)
                   (trans-er soft ctx
                             "The second argument of a must-be-equal call ~
                              (i.e.,the :exec argument of an mbe call) must ~
                              not contain any calls of must-be-equal (or, ~
                              hence, of mbe)."))
                  (t (trans-value (fcons-term* 'must-be-equal arg1 arg2))))))
          ((eq (car x) 'time$)
           (trans-er-let*
            ((arg1 (translate11 (cadr x)
                                stobjs-out bindings inclp known-stobjs
                                ctx w state)))
            (trans-value (fcons-term* 'time$ arg1))))
          ((eq stobjs-out t)
           (trans-er-let*
            ((args (translate11-lst (cdr x) t bindings inclp known-stobjs
                                    nil ctx w state)))
            (trans-value (fcons-term (car x) args))))
          ((and (member (car x) '(makunbound-global put-global))
                (or (not (consp (cadr x)))
                    (not (eq (car (cadr x)) 'quote))
                    (not (null (cddr (cadr x))))
                    (not (symbolp (cadr (cadr x))))))
           (trans-er soft ctx
                     "The first arg of ~x0 must be a quoted symbol, ~
                      unlike ~x1.  We make this requirement in ~
                      support of untouchables."
                     (car x) (cadr x)))
          ((and (member (car x) '(makunbound-global put-global))
                (member (cadr (cadr x))
                        (global-val 'untouchables w)))
           (trans-er soft ctx
                     "~x0 has been rendered untouchable and thus may ~
                      not be directly altered, as in ~x1."
                     (cadr (cadr x)) x))
          (t
           (let ((stobjs-out (translate-deref stobjs-out bindings))
                 (stobjs-out2 (let ((temp (translate-deref (car x) bindings)))
                                (cond (temp temp)
                                      (t (stobjs-out (car x) w))))))
             (cond
              ((consp stobjs-out)
               (cond
                ((consp stobjs-out2)
                 (cond
                  ((not (equal stobjs-out stobjs-out2))
                   (trans-er soft ctx
                             "It is illegal to invoke ~x0 here ~
                              because of a signature mismatch.  ~x0 ~
                              returns a result of shape ~x1 where a ~
                              result of shape ~x2 is required."
                             (car x)
                             (prettyify-stobjs-out stobjs-out2)
                             (prettyify-stobjs-out stobjs-out)))
                  (t (trans-er-let*
                      ((args (translate11-lst (cdr x)
                                              (stobjs-in (car x) w)
                                              bindings
                                              (compute-inclp-lst
                                               (stobjs-in (car x) w)
                                               stobjs-out)
                                              known-stobjs
                                              (car x)
                                              ctx w state)))
                      (trans-value (fcons-term (car x) args))))))
                (t
                 (let ((bindings
                        (translate-bind stobjs-out2 stobjs-out bindings)))
                   (trans-er-let*
                    ((args (translate11-lst (cdr x)
                                            (stobjs-in (car x) w)
                                            bindings inclp known-stobjs
                                            (car x)
                                            ctx w state)))
                    (trans-value (fcons-term (car x) args)))))))
              ((consp stobjs-out2)
               (let ((bindings
                      (translate-bind stobjs-out stobjs-out2 bindings)))
                 (trans-er-let*
                  ((args (translate11-lst (cdr x)
                                          (stobjs-in (car x) w)
                                          bindings inclp known-stobjs
                                          (car x)
                                          ctx w state)))
                  (trans-value (fcons-term (car x) args)))))
              (t (let ((bindings
                        (translate-bind stobjs-out2 stobjs-out bindings)))
                   (trans-er-let*
                    ((args (translate11-lst (cdr x)
                                            (stobjs-in (car x) w)
                                            bindings inclp known-stobjs
                                            (car x)
                                            ctx w state)))
                    (trans-value (fcons-term (car x) args))))))))))
   ((arity (car x) w)
    (trans-er soft ctx
              "~x0 takes ~#1~[no arguments~/1 argument~/~x2 ~
               arguments~] but in the call ~x3 it is given ~#4~[no ~
               arguments~/1 argument~/~x5 arguments~].   The formal ~
               parameters list for ~x0 is ~X67."
              (car x)
              (zero-one-or-more (arity (car x) w))
              (arity (car x) w)
              x
              (zero-one-or-more (length (cdr x)))
              (length (cdr x))
              (formals (car x) w)
              nil))
   ((eq (car x) 'declare)
    (trans-er soft ctx
              "It is illegal to use DECLARE as a function symbol, as ~
               in ~x0.  DECLARE forms are permitted only in very ~
               special places, e.g., before the bodies of function ~
               definitions, LETs, and MV-LETs.  DECLARE forms are ~
               never permitted in places in which their ``values'' ~
               are relevant.  If you already knew this, it is likely ~
               you have made a typographical mistake, e.g., including ~
               the body in the DECLARE form or closing the superior ~
               form before typing the body."
              x))
   (t (trans-er soft ctx
                "The symbol ~x0 (in package ~x1) has neither a ~
                 function nor macro definition in ACL2.  Please ~
                 define it."
                (car x)
                (symbol-package-name (car x))))))
