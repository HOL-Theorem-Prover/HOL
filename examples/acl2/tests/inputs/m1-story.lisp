; This file tells the whole m1 story from scratch in a minimalist
; setting.  Then, that story is redeveloped in the books

;  m1.lisp
;  m1-lemmas.lisp
;  m1-compiler.lisp
;  m1-ifact.lisp

#|
(include-book "problem-set-1-answers")

(begin-book t :ttags :all)
|#

(in-package "M1")

; Here is the semantics of the M1 machine.  In addition to the ACL2 primitive
; functions in the "M1" package, we take advantage of the following
; functions defined in "problem-set-1-answers.lisp":

; push, top, pop,     - intro material of Problem Set 1
; nth                 - intro material of Problem Set 1
; update-nth          - Problem 1-14
; make-state, pc, etc - intro material of Problem Set 1
; opcode, arg1, arg2  - Problem 1-4

(defun next-inst (s)
  (nth (pc s) (program s)))

; Now we define the semantics of each instruction.  These
; functions are called ``semantic functions.''

(defun execute-ICONST (inst s)
  (make-state (+ 1 (pc s))
              (locals s)
              (push (arg1 inst) (stack s))
              (program s)))

(defun execute-ILOAD (inst s)
  (make-state (+ 1 (pc s))
              (locals s)
              (push (nth (arg1 inst)
                         (locals s))
                    (stack s))
              (program s)))

(defun execute-IADD (inst s)
  (declare (ignore inst))
  (make-state (+ 1 (pc s))
              (locals s)
              (push (+ (top (pop (stack s)))
                       (top (stack s)))
                    (pop (pop (stack s))))
              (program s)))

(defun execute-ISTORE (inst s)
  (make-state (+ 1 (pc s))
              (update-nth (arg1 inst) (top (stack s)) (locals s))
              (pop (stack s))
              (program s)))

(defun execute-ISUB (inst s)
  (declare (ignore inst))
  (make-state (+ 1 (pc s))
              (locals s)
              (push (- (top (pop (stack s)))
                       (top (stack s)))
                    (pop (pop (stack s))))
              (program s)))

(defun execute-IMUL (inst s)
  (declare (ignore inst))
  (make-state (+ 1 (pc s))
              (locals s)
              (push (* (top (pop (stack s)))
                       (top (stack s)))
                    (pop (pop (stack s))))
              (program s)))

(defun execute-GOTO (inst s)
  (make-state (+ (arg1 inst) (pc s))
              (locals s)
              (stack s)
              (program s)))

(defun execute-IFLE (inst s)
  (make-state (if (<= (top (stack s)) 0)
                  (+ (arg1 inst) (pc s))
                (+ 1 (pc s)))
              (locals s)
              (pop (stack s))
              (program s)))

(defun do-inst (inst s)
  (if (equal (op-code inst) 'ICONST)
      (execute-ICONST  inst s)
    (if (equal (op-code inst) 'ILOAD)
        (execute-ILOAD  inst s)
      (if (equal (op-code inst) 'ISTORE)
          (execute-ISTORE  inst s)
        (if (equal (op-code inst) 'IADD)
            (execute-IADD   inst s)
          (if (equal (op-code inst) 'ISUB)
              (execute-ISUB   inst s)
            (if (equal (op-code inst) 'IMUL)
                (execute-IMUL   inst s)
              (if (equal (op-code inst) 'GOTO)
                  (execute-GOTO   inst s)
                (if (equal (op-code inst) 'IFLE)
                    (execute-IFLE   inst s)
                  s)))))))))


(defun step (s)
     (do-inst (next-inst s) s))

(defun run (sched s)
     (if (endp sched)
         s
       (run (cdr sched) (step s))))

; ===========================================================================
; Now I present an example of an M1 program and its execution.

(defconst *ifact-program*
  ; Imagine compiling:
  ;  a = 1;
  ;  while (n > 0)
  ;    { a = n * a;
  ;      n = n-1;};
  ;  return a;

  '((ICONST 1)     ;;;  0
    (ISTORE 1)     ;;;  1 a = 1;
    (ILOAD 0)      ;;;  2 while         ; loop: pc=2
    (IFLE 10)      ;;;  3   (n > 0)
    (ILOAD 0)      ;;;  4   {
    (ILOAD 1)      ;;;  5
    (IMUL)         ;;;  6
    (ISTORE 1)     ;;;  7   a = n * a;
    (ILOAD 0)      ;;;  8
    (ICONST 1)     ;;;  9
    (ISUB)         ;;; 10
    (ISTORE 0)     ;;; 11   n = n-1;
    (GOTO -10)     ;;; 12   }            ; jump to loop
    (ILOAD 1)      ;;; 13
    (HALT)         ;;; 14  return a;
    ))

; You can just evaluate this test and get the answer shown.

#|
(run
 '(0 0 0 0 0 0 0 0 0 0 ; 100 clock ticks
   0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0
   0 0 0 0 0 0 0 0 0 0)
 (make-state
  0                    ; pc
  '(5 0)               ; locals: n=5, a=0
  nil                  ; stack
  *ifact-program*      ; our program, above
  ))

; answer:
(14                    ; final pc
 (0 120)               ; final locals: n=0, a=120
 (120)                 ; final stack
 ((ICONST 1)           ; our program, again
  (ISTORE 1)
  (ILOAD 0)
  (IFLE 10)
  (ILOAD 0)
  (ILOAD 1)
  (IMUL)
  (ISTORE 1)
  (ILOAD 0)
  (ICONST 1)
  (ISUB)
  (ISTORE 0)
  (GOTO -10)
  (ILOAD 1)
  (HALT)))
|#

; We can record this in a certified book as a theorem by just
; equating the expression and its computed value:

(defthm factorial-example-0
  (equal (run
          '(0 0 0 0 0 0 0 0 0 0 ; 100 clock ticks
            0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0)
          (make-state
           0                    ; pc
           '(5 0)               ; locals: n=5, a=0
           nil                  ; stack
           *ifact-program*      ; our program, above
           ))
         '(14                   ; final pc
           (0 120)              ; final locals: n=0, a=120
           (120)                ; final stack
           ((ICONST 1)          ; our program, again
            (ISTORE 1)
            (ILOAD 0)
            (IFLE 10)
            (ILOAD 0)
            (ILOAD 1)
            (IMUL)
            (ISTORE 1)
            (ILOAD 0)
            (ICONST 1)
            (ISUB)
            (ISTORE 0)
            (GOTO -10)
            (ILOAD 1)
            (HALT))))
  :rule-classes nil)

; ===========================================================================
; Now I make it easier to write schedules and write a schedule for ifact.

; Here we use
; app                 - Problem 1-10
; repeat              - Problem 1-12

(defun ifact-loop-sched (n)
  (if (zp n)
      (repeat 0 4)
    (app (repeat 0 11)
         (ifact-loop-sched (- n 1)))))

; This can be explained: to schedule the ifact program on n starting
; at the loop pc = 2: If n is 0, schedule 4 steps, namely the
; instructions at pcs 2, 3, 13, and 14, ending at the HALT.
; Otherwise, if n is not 0, schedule the 11 instructions at pcs 2
; through 12, ending back at pc = 2, and then schedule ifact for n-1.

; We then use this to say how to schedule a complete ifact computation,
; starting at pc = 0.

(defun ifact-sched (n)
  (app (repeat 0 2)
       (ifact-loop-sched n)))

; ===========================================================================
; Now I write our example above in a slightly more precise and abstract
; way.

(defun ! (n)
  (if (zp n)
      1
    (* n (! (- n 1)))))

; And here is a function that computes factorial by running M1:

(defun test-ifact (n)
   (top
    (stack
     (run (ifact-sched n)
          (make-state 0
                      (cons n (cons 0 nil))
                      nil
                      *ifact-program*)))))

(acl2::comp t) ; added by Matt K. for GCL

(defthm factorial-example-1
  (equal (test-ifact 5)
         (! 5))
  :rule-classes nil)

(defthm factorial-example-2
  (equal (test-ifact 1000)
         (! 1000))
  :rule-classes nil)
; ===========================================================================

; Problem 2a-1: Define the constant *even-program* as an M1 program that takes
; a natural number, i, as local variable 0 and halts with 1 on the stack if i
; is even and with 0 on the stack if i is odd.  For example, if the program is
; started with locals (18) then it pushes 1, but if started with (19) it pushes
; 0.

; My Answer:

(defconst *even-program*
  '((iload 0)
    (ifle 12)
    (iload 0)
    (iconst 1)
    (isub)
    (ifle 6)
    (iload 0)
    (iconst 2)
    (isub)
    (istore 0)
    (goto -10)
    (iconst 0)
    (halt)
    (iconst 1)
    (halt)))

(defun even-sched (i)
  (if (zp i)
      (repeat 0 4)
    (if (equal i 1)
        (repeat 0 8)
      (app (repeat 0 11)
           (even-sched (- i 2))))))

(defun test-even (i)
  (top
   (stack
    (run (even-sched i)
         (make-state 0
                     (list i)
                     nil
                     *even-program*)))))

(defthm test-even-theorem
  (and (equal (test-even 18) 1)
       (equal (test-even 19) 0)
       (equal (test-even 235) 0)
       (equal (test-even 234) 1))
  :rule-classes nil)

; ===========================================================================

; Now I develop a compiler for a simple language of arithmetic,
; assignment, and while statements.

; Here we'll use
; member              - Problem 1-15
; index               - Problem 1-16
; len                 - Problem 1-9

; The syntax of our language is

; <expr>         := <var>|<int-constant>|( <expr> <op> <expr> )

; <op>           := + | - | *

; <test>         := ( <expr> > <expr>)

; <stmt>         := ( <var> = <expr> ) |
;                   ( while <test> <stmt*>) |
;                   ( return <expr> )

; <stmt*>        := <stmt> | <stmt> <stmt*>

; <program>      := ( <stmt*> )

; <var>          := any ACL2 symbol

; <int-constant> := any ACL2 integer

; Thus, an example program is:

; ((a = 1)
;  (while (n > 0)
;    (a = (n * a))
;    (n = (n - 1)))
;  (return a))

; For the purposes of this exercise, we will assume that every
; program we wish to compile is syntactically well-formed.

; We first define a function, collect-vars-in-stmt*, that sweeps over
; a list of statements and collects all the variables it finds.  It
; adds the variables to the end of a running accumulator.  That
; accumulator will be initiallized to the list of formals of the
; method we're compiling.  The new variables accumulated onto it will
; be the temporary variables of the method.  The order of the
; collected list will determine where the variables are allocated in
; the locals.  The first formal will be given index 0, the next index
; 1, etc.

(defun collect-at-end (list e)    ;;; Add e to the end of list
  (if (member e list)             ;;; unless it is already in list.
      list
    (app list (cons e nil))))

; These two theorems are necessary for the proof of termination of
; collect-vars-in-expr, below.

(defthm nth-nil
  (equal (nth n nil) nil))

(defthm acl2-count-nth
  (implies (consp list)
           (< (acl2-count (nth n list))
              (acl2-count list)))
  :rule-classes :linear)

(defun collect-vars-in-expr (vars expr)       ;;; Sweep expr and collect
  (if (atom expr)                             ;;; all variable names into
      (if (symbolp expr)                      ;;; vars.
          (collect-at-end vars expr)
        vars)
    (collect-vars-in-expr
     (collect-vars-in-expr vars
                           (nth 0 expr))
     (nth 2 expr))))

; Note that if expr is not an atom, it is of the form
; ( <expr> + <expr> ) or
; ( <expr> - <expr> ) or
; ( <expr> * <expr> ).  

; Hence, (nth 0 expr) is the first subexpression and (nth 2 expr) is
; the second.

; Now we collect the vars in a statement.  This is defined mutually
; recursively with the vars in a list of statements.

(mutual-recursion

(defun collect-vars-in-stmt* (vars stmt-list)
  (if (endp stmt-list)
      vars
    (collect-vars-in-stmt*
     (collect-vars-in-stmt vars (car stmt-list))
     (cdr stmt-list))))

(defun collect-vars-in-stmt (vars stmt)
  (if (equal (nth 1 stmt) '=)
      (collect-vars-in-expr
       (collect-at-end vars (nth 0 stmt))
       (nth 2 stmt))
    (if (equal (nth 0 stmt) 'WHILE)
        (collect-vars-in-stmt*
         (collect-vars-in-expr vars (nth 1 stmt))
         (cdr (cdr stmt)))
      (if (equal (nth 0 stmt) 'RETURN)
          (collect-vars-in-expr vars (nth 1 stmt))
        vars))))
)

; We will use the function index to determine the position of a
; variable in the list of variables.

; Now we begin the code generation.  To compile an expression
; like (<expr> op <expr>), we'll generate code that leaves the
; values of the two subexpressions on the stack and then we'll
; execute the bytecode that pops those two values and pushes the
; result of executing op.

; The bytecode program to execute op (assuming its arguments are
; on the stack):

(defun OP! (op)
  (if (equal op '+)
      '((IADD))
    (if (equal op '-)
        '((ISUB))
      (if (equal op '*)
          '((IMUL))
        '((ILLEGAL))))))

; Note that the output above is a bytecode program, i.e., a list of
; instructions (in this case, always a trivial list of length 1).  All
; our functions for generating code generate bytecode programs so we
; can combine them with concatentation.

; The bytecode program to put the value of a variable on the stack:

(defun ILOAD! (vars var)
  (cons (cons 'ILOAD (cons (index var vars) nil))
        nil))

; The bytecode program to put the value of a constant on the stack:

(defun ICONST! (n)
  (cons (cons 'ICONST (cons n nil))
        nil))

; The bytecode program to put the value of an expression on the stack:

(defun expr! (vars expr)
  (if (atom expr)
      (if (symbolp expr)
          (ILOAD! vars expr)
        (ICONST! expr))
    (app (expr! vars (nth 0 expr))
         (app (expr! vars (nth 2 expr))
              (OP! (nth 1 expr))))))

; The bytecode program to test the top of the stack and branch by offset
; if it is less than or equal to 0:

(defun IFLE! (offset)
  (cons (cons 'IFLE (cons offset nil))
        nil))

; The bytecode program to jump by offset:

(defun GOTO! (offset)
  (cons (cons 'GOTO (cons offset nil))
        nil))

; The bytecode program to evaluate a while statement (given the
; bytecode programs for the test and body):

(defun while! (test-code body-code)

; To compile (while test stmt1...stmtn) we first compile code that
; leaves a positive on the stack if test is true and a non-positive on
; the stack if test is false.  Call that code test1, ... testk.  Then
; we compile the statements in the body.  Call that code body1, ...,
; bodyn.  Note that the length of the test code is k and the length of
; the body code is n.  We return:

; (test1            ; top of WHILE
;  ...
;  testk            ; value of test is on the stack
;  (IFLE 2+n)       ; if test false, jump past body code
;  body1
;  ...
;  bodyn
;  (GOTO -(n+1+k))  ; go back to top of WHILE
;  )                ; we're done with the WHILE

  (app test-code
       (app (IFLE! (+ 2 (len body-code)))
            (app body-code
                 (GOTO! (- (+ (len test-code)
                              1
                              (len body-code))))))))

; The bytecode program to leave a positive on the stack if test is
; true and a non-positive otherwise:

(defun test! (vars test)

; Test has to be of the form (x > y), where x and y are expressions.
; If y is 0, then we can just leave the value of x on the stack, that
; is, the test is true or false exactly according to whether the value
; of x is positive or not positive.  If y is not 0, we act like we saw
; (x-y > 0), which is equivalent and which statisfies the first
; condition.

  (if (equal (nth 1 test) '>)
      (if (equal (nth 2 test) 0)
          (expr! vars (nth 0 test))
        (app (expr! vars (nth 0 test))
             (app (expr! vars (nth 2 test))
                  '((ISUB)))))
    '((ILLEGAL))))

; The bytecode program to pop the stack into the local allocated for var:

(defun ISTORE! (vars var)
  (cons (cons 'ISTORE (cons (index var vars) nil))
        nil))

; The bytecode programs for a list of statements and for a single statement:

(mutual-recursion

 (defun stmt*! (vars stmt-list)
   (if (endp stmt-list)
       nil
     (app (stmt! vars (car stmt-list))
          (stmt*! vars (cdr stmt-list)))))

 (defun stmt! (vars stmt)
   (if (equal (nth 1 stmt) '=)
       (app (expr! vars (nth 2 stmt))
            (ISTORE! vars (nth 0 stmt)))
     (if (equal (nth 0 stmt) 'WHILE)
         (while!
          (test! vars (nth 1 stmt))
          (stmt*! vars (cdr (cdr stmt))))
       (if (equal (nth 0 stmt) 'RETURN)
           (app (expr! vars (nth 1 stmt))
                '((HALT)))
         '((ILLEGAL))))))
 )

; The bytecode program for stmt-list given the initial formals:

(defun compile (formals stmt-list)
  (stmt*! (collect-vars-in-stmt* formals stmt-list)
          stmt-list))

; See Demo1.java

(defthm example-compilation-1
  (equal (compile '(n)
                  '((a = 1)
                    (while (n > 0)
                      (a = (n * a))
                      (n = (n - 1)))
                    (return a)))
         '((ICONST 1)
           (ISTORE 1)
           (ILOAD 0)
           (IFLE 10)
           (ILOAD 0)
           (ILOAD 1)
           (IMUL)
           (ISTORE 1)
           (ILOAD 0)
           (ICONST 1)
           (ISUB)
           (ISTORE 0)
           (GOTO -10)
           (ILOAD 1)
           (HALT)))
  :rule-classes nil)

; See Demo2.java

(defthm example-compilation-2
  (equal (compile '(n k)
                  '((a = 0)
                    (while (n > k)
                      (a = (a + 1))
                      (n = (n - 1)))
                    (return a)))
         '((ICONST 0)
           (ISTORE 2)
           (ILOAD 0)
           (ILOAD 1)
           (ISUB)
           (IFLE 10)
           (ILOAD 2)
           (ICONST 1)
           (IADD)
           (ISTORE 2)
           (ILOAD 0)
           (ICONST 1)
           (ISUB)
           (ISTORE 0)
           (GOTO -12)
           (ILOAD 2)
           (HALT)))
  :rule-classes nil)

(defthm example-execution-1
  (equal (top
          (stack
           (run (repeat 0 1000)
                (make-state 0
                            '(5 0)
                            nil
                            (compile '(n)
                                     '((a = 1)
                                       (while (n > 0)
                                         (a = (n * a))
                                         (n = (n - 1)))
                                       (return a)))))))
         120)
  :rule-classes nil)

(defthm example-execution-2
  (equal (top
          (stack
           (run (repeat 0 1000)
                (make-state 0
                            '(10 4 0)
                            nil
                            (compile '(n k)
                                     '((a = 0)
                                       (while (n > k)
                                         (a = (a + 1))
                                         (n = (n - 1)))
                                       (return a)))))))
         6)
  :rule-classes nil)

; ===========================================================================
; Now I develop some rules that allow ACL2 to prove theorems
; about M1 programs.

; Arithmetic

(include-book "arithmetic-3/extra/top-ext" :dir :system)

; Abstract Data Type Stuff

(defthm stacks
  (and (equal (top (push x s)) x)
       (equal (pop (push x s)) s)

; These next two are needed because some push expressions evaluate to
; list constants, e.g., (push 1 (push 2 nil)) becomes '(1 2) and '(1
; 2) pattern-matches with (cons x s) but not with (push x s).

       (equal (top (cons x s)) x)
       (equal (pop (cons x s)) s)))

(in-theory (disable push top pop))

(defthm states
  (and (equal (pc (make-state pc locals stack program)) pc)
       (equal (locals (make-state pc locals stack program)) locals)
       (equal (stack (make-state pc locals stack program)) stack)
       (equal (program (make-state pc locals stack program)) program)

; And we add the rules to handle constant states:

       (equal (pc (cons pc x)) pc)
       (equal (locals (cons pc (cons locals x))) locals)
       (equal (stack (cons pc (cons locals (cons stack x)))) stack)
       (equal (program (cons pc (cons locals (cons stack (cons program x)))))
              program)))


(in-theory (disable make-state pc locals stack program))

; Step Stuff

(defthm step-opener
  (implies (consp (next-inst s))
           (equal (step s)
                  (do-inst (next-inst s) s))))

(in-theory (disable step))

; Schedules and Run

(defthm run-app
  (equal (run (app a b) s)
         (run b (run a s))))
  
(defthm run-opener
  (and (equal (run nil s) s)
       (equal (run (cons th sched) s)
              (run sched (step s)))))

(in-theory (disable run))

; Nth and update-nth

(defthm nth-add1!
  (implies (natp n)
           (equal (nth (+ 1 n) list)
                  (nth n (cdr list)))))

(defthm nth-update-nth
  (implies (and (natp i) (natp j))
           (equal (nth i (update-nth j v list))
                  (if (equal i j)
                      v
                    (nth i list)))))

(defthm update-nth-update-nth-1
  (implies (and (natp i) (natp j) (not (equal i j)))
           (equal (update-nth i v (update-nth j w list))
                  (update-nth j w (update-nth i v list))))
  :rule-classes ((:rewrite :loop-stopper ((i j update-nth)))))

(defthm update-nth-update-nth-2
  (equal (update-nth i v (update-nth i w list))
         (update-nth i v list)))


; ===========================================================================

; Proof that the factorial code computes factorial.  I lay this out as
; a series of 7 steps.  The steps are:

; [1] Specify the concepts related to what you're doing.

; [2] Write the program.

; [3] Specify how long it takes to execute (starting with the
;     loop).  In particular, define a scheduler function that
;     will run this program to completion.

; [4] Test the program and your scheduler.

; [5] Prove your program does what it does, starting with the
;     loop.

; [6] Prove what we do is what we want.

; [7] Put it all together.

; Concretely, for the  factorial code, here are the steps.

; [1] Specify the concepts related to what you're doing.
;     Typically we do it at two levels, 
;     (a) What we want.
;     (b) How we'll do it.

; (a) What we want:

(defun ! (n)
  (if (zp n)
      1
    (* n (! (- n 1)))))

; (b) How we'll do it:  We'll compute (ifact n 1), where

(defun ifact (n a)
  (if (zp n)
      a
    (ifact (- n 1) (* n a))))

; [2] Write the program.

; Below I show the bytecode program.  It is the one generated by
; our compiler.  But I will deal with the bytecode directly, not
; the source code.

(defconst *ifact-program*
  ; (compile-stmt-list
  ;  '(n)
  ;  '((a = 1)
  ;    (while (n > 0)
  ;      (a = (n * a))
  ;      (n = (n - 1)))
  ;    (return a)))

  '((ICONST 1)     ;;;  0
    (ISTORE 1)     ;;;  1 (a = 1)
    (ILOAD 0)      ;;;  2 (while         ; loop: pc=2
    (IFLE 10)      ;;;  3   (n > 0)
    (ILOAD 0)      ;;;  4
    (ILOAD 1)      ;;;  5
    (IMUL)         ;;;  6
    (ISTORE 1)     ;;;  7   (a = (n * a))
    (ILOAD 0)      ;;;  8
    (ICONST 1)     ;;;  9
    (ISUB)         ;;; 10
    (ISTORE 0)     ;;; 11   (n = (n - 1))
    (GOTO -10)     ;;; 12   )            ; jump to loop
    (ILOAD 1)      ;;; 13
    (HALT)         ;;; 14  (return a)
    ))

; [3] Specify how long it takes to execute (starting with the loop).
;     In particular, define a scheduler function that will
;     run this program to completion.  We've already done this:

(defun ifact-loop-sched (n)
  (if (zp n)
      (repeat 0 4)
    (app (repeat 0 11)
         (ifact-loop-sched (- n 1)))))

(defun ifact-sched (n)
  (app (repeat 0 2)
       (ifact-loop-sched n)))

; [4] Test the program and your scheduler.

; We define a little ``test harness'' to let us compute ifact
; on any natural, using the ifact program.

(defun test-ifact (n)
  (top
   (stack
    (run (ifact-sched n)
         (make-state 0
                     (cons n (cons 0 nil))      ; n=n, a=0
                     nil
                     *ifact-program*)))))

; Normally we would just try out a few examples, e.g.,
; (test-ifact 5) and expect to see 120 or (! 5).  But for
; posterity I will just write a trivial theorem to prove.

(defthm test-ifact-examples
  (and (equal (test-ifact 5) (! 5))
       (equal (test-ifact 10) (! 10))
       (equal (test-ifact 100) (! 100))))

; Just for the record, (! 100) is quite large; it has 158 decimal
; digits.  This shows that our little m1 machine inherents quite a lot
; of power from its Lisp description.

; [5] Prove your program does what it does, starting with the loop.

(defthm ifact-loop-lemma
  (implies (and (natp n)
                (natp a))
           (equal (run (ifact-loop-sched n)
                       (make-state 2
                                   (cons n (cons a nil))
                                   stack
                                   *ifact-program*))
                  (make-state 14
                              (cons 0 (cons (ifact n a) nil))
                              (push (ifact n a) stack)
                              *ifact-program*))))

(defthm ifact-lemma
  (implies (natp n)
           (equal (run (ifact-sched n)
                       (make-state 0
                                   (cons n (cons a nil))
                                   stack
                                   *ifact-program*))
                  (make-state 14
                              (cons 0 (cons (ifact n 1) nil))
                              (push (ifact n 1) stack)
                              *ifact-program*))))

; We can now disable sched-ifact so that we never run the bytecode
; again in proofs.

(in-theory (disable ifact-sched))

; [6] Prove what we do is what we want.

(defthm ifact-is-factorial
  (implies (and (natp n)
                (natp a))
           (equal (ifact n a)
                  (* (! n) a))))

; [7]  Put it all together.

(defthm ifact-correct
  (implies (natp n)
           (equal (run (ifact-sched n)
                       (make-state 0
                                   (cons n (cons a nil)) 
                                   stack
                                   *ifact-program*))
                  (make-state 14
                              (cons 0 (cons (! n) nil))
                              (push (! n) stack)
                              *ifact-program*))))

(defthm ifact-correct-corollary-1
  (implies (natp n)
           (equal (top
                   (stack
                    (run (ifact-sched n)
                         (make-state 0
                                     (cons n (cons a nil))
                                     stack
                                     *ifact-program*))))
                  (! n))))

; We can make this look like the verification of a high-level program,
; but of course it is not.  We verified the output of the compiler,
; not the input.

(defthm ifact-correct-corollary-2
  (implies (natp n)
           (equal (top
                   (stack
                    (run (ifact-sched n)
                         (make-state 0
                                     (cons n (cons a nil))
                                     stack
                                     (compile
                                      '(n)
                                      '((a = 1)
                                        (while (n > 0)
                                          (a = (n * a))
                                          (n = (n - 1)))
                                        (return a)))))))
                  (! n))))

; ===========================================================================

; Now we develop the macros that make all this more palatable.

; The semantic functions for each instruction return a new state
; constructed from parts of an old one, s.  Typically the new
; state is just s with one or two components changed.  The others
; are fixed, for that instruction.  

; A good example is that of ILOAD:

; (make-state (+ 1 (pc s))
;             (locals s)
;             (push (nth (arg1 inst)
;                        (locals s))
;                   (stack s))
;             (program s))

; We can write a macro that allows us to express this as
;
; (modify s
;         :stack (push (nth (arg1 inst)
;                           (locals s))
;                      (stack s)))

; The modify expression above expands EXACTLY to the make-state shown
; above it.  Modify is just an abbreviation for a make-state.  But we
; only have to write the parts that change in ``unusual'' ways.  Since
; pc is almost always incremented by one, modify will always produce
; (+ 1 (pc s)) in the pc slot of the make-state, unless we supply the
; :pc keyword to modify along with the correct new pc.

; So here is the modify macro.  It generates a make-state.  The first
; slot is the pc slot, the second is the locals, etc.  For each of the
; keys :pc, :locals, :stack, and :program, if that key is supplied
; among the args to modify, then the make-state has the corresponding
; val in that key's slot.  Otherwise, that key's slot is occupied by
; an expression that computes the value of that slot in state s.  The
; :pc slot is an exception: the default value is the old value
; incremented by one.

(defmacro modify (s &rest args)
     (list 'make-state
           (if (suppliedp :pc args)
               (actual :pc args)
             (list '+ 1 (list 'pc s)))
           (if (suppliedp :locals args)
               (actual :locals args)
             (list 'locals s))
           (if (suppliedp :stack args)
               (actual :stack args)
             (list 'stack s))
           (if (suppliedp :program args)
               (actual :program args)
             (list 'program s))))

(defthm example-modify-1
  (equal (modify s :stack (push (arg1 inst) (stack s)))
         (make-state (+ 1 (pc s))
                     (locals s)
                     (push (arg1 inst) (stack s))
                     (program s)))
  :rule-classes nil)

(defthm example-modify-2
  (equal (modify s
                 :locals (update-nth (arg1 inst)
                                     (top (stack s))
                                     (locals s))
                 :stack (pop (stack s)))
         (make-state
          (+ 1 (pc s))
          (update-nth (arg1 inst)
                      (top (stack s))
                      (locals s))
          (pop (stack s))
          (program s)))
  :rule-classes nil)

(defthm example-modify-3
  (equal (modify s :pc (+ (arg1 inst) (pc s)))
         (make-state (+ (arg1 inst) (pc s))
                     (locals s)
                     (stack s)
                     (program s)))
  :rule-classes nil)

; Because we frequently use such expressions as (arg2 inst) and (stack
; s) in the descriptions of new states, it is convenient to introduce
; some variables that are bound to those values whenever we are
; defining a semantic function.  We therefore introduce a special form
; of defun to use when defining the semantics of an instruction.

(defun pattern-bindings (vars arg-expressions)
  (if (endp vars)
      nil
    (cons (list (car vars) (car arg-expressions))
          (pattern-bindings (cdr vars) (cdr arg-expressions)))))

(defmacro semantics (pattern body)
  (list 'let (app (pattern-bindings (cdr pattern)
                                    '((arg1 inst)
                                      (arg2 inst)
                                      (arg3 inst)))
                  '((-pc- (pc s))
                    (-locals- (locals s))
                    (-stack- (stack s))
                    (-program- (program s))))
        body))

; The body might not refer to each of these bound variables.
; ACL2 normally causes an error if it sees an unused bound
; variable.  We must tell it not to worry about that.

(acl2::set-ignore-ok t)

(defthm example-semantics-1
  (equal (semantics
          (ICONST c)
          (modify s :stack (push c -stack-)))
         (make-state
          (+ 1 (pc s))
          (locals s)
          (push (arg1 inst) (stack s))
          (program s)))
  :rule-classes nil)

; So in the future, instead of writing

; (defun execute-ICONST (inst s)
;   (make-state (+ 1 (pc s))
;               (locals s)
;               (push (arg1 inst) (stack s))
;               (program s)))

; we could write 

; (defun execute-ICONST (inst s)
;   (semantics (ICONST c)
;              (modify s :stack (push c -stack-))))

; But in fact, we'll introduce yet another macro so we can just write:

; (defsem (ICONST c)
;   (modify s :stack (push c -stack-)))

; and it will
; * generate the name execute-ICONST,
; * fill in the formals, and 
; * use the semantics function to generate the body.

; So now we define defsem...

; The next function is easily understood by example.
; (concat-symbols 'EXECUTE- 'ICONST) will return the
; symbol EXECUTE-ICONST.

; I have not told you how to create symbols because we don't need it -- except
; for this one use of going from an instruction opcode to the semantic function
; name.  Just trust me that this function generates a symbol in the M1 package
; whose name is the concatenation of the names of the two parts.

(defun concat-symbols (part1 part2)
  (intern-in-package-of-symbol
   (coerce
    (app (coerce (symbol-name part1) 'list)
         (coerce (symbol-name part2) 'list))
    'string)
   'run))

; This function creates a defun form, with an optional declaration.

(defun make-defun (name args dcl body)
  (if dcl
      (list 'defun name args dcl body)
    (list 'defun name args body)))

; Thus, (make-defun 'foo '(x) nil '(+ 1 x)) returns

; (defun foo (x) (+ 1 x))

; But, (make-defun 'foo '(x y) '(declare (ignore y)) '(+ 1 x))
; returns

; (defun foo (x y) (declare (ignore y)) (+ 1 x))

(defmacro defsem (pattern body)
  (make-defun (concat-symbols 'execute- (car pattern))
              '(inst s)
              (if (equal (len pattern) 1)
                  '(declare (ignore inst))
                nil)
              (list 'semantics pattern body)))

