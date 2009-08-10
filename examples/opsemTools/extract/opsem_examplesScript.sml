
open HolKernel Parse boolLib bossLib; val _ = new_theory "opsem_examples";

open opsem_translatorLib integerTheory intLib arithmeticTheory;


(* ====================================================================================== *)
(*  VERIFICATION EXAMPLE                                                                  *)
(* ====================================================================================== *)

val (th,d_def) = time (DERIVE_SEP_TOTAL_SPEC "d") ``
       (Seq (Assign "a" (Const 0))
            (While (Not (Equal (Var "n") (Const 0)))
                   (Seq (Assign "a" (Plus (Var "a") (Const 1)))
                        (Assign "n" (Sub (Var "n") (Const 2))))))``;

val d1_lemma = prove(
  ``!n:num a. d1_pre (a, 2 * (& n)) /\ (d1 (a, 2 * (& n)) = ((& n) + a, 0))``,
  Induct_on `n` THEN ONCE_REWRITE_TAC [d_def]
  THEN1 ASM_SIMP_TAC int_ss [LET_DEF]
  THEN ASM_SIMP_TAC std_ss [LET_DEF,INT,COOPER_PROVE ``(~(2 * & n + 2 = 0)) /\ (2*1 = 2)``,INT_LDISTRIB,
    ONCE_REWRITE_RULE [INT_ADD_COMM] INT_ADD_SUB] THEN COOPER_TAC);

val d = prove(
  ``!n a. EVEN n ==> d_pre(a,&n) /\ (d(a,&n) = (&(n DIV 2), 0))``,
  SIMP_TAC std_ss [EVEN_EXISTS,d_def,LET_DEF] THEN REPEAT STRIP_TAC
  THEN ASM_SIMP_TAC std_ss [d1_lemma,ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
  THEN SIMP_TAC intLib.int_ss [SIMP_RULE (intLib.int_ss) [] d1_lemma]);


(* ====================================================================================== *)
(*  EXAMPLES WITH INTEGERS                                                                *)
(* ====================================================================================== *)

val (th,rw) = time (DERIVE_SEP_SPEC "AbsMinus") ``
       (Seq (Assign "result" (Const 0))
          (Seq (Assign "k" (Const 0))
             (Seq
                (Cond
                   (Or (Less (Var "i") (Var "j"))
                      (Equal (Var "i") (Var "j")))
                   (Assign "k" (Plus (Var "k") (Const 1))) Skip)
                (Seq
                   (Cond
                      (And (Equal (Var "k") (Const 1))
                         (Not (Equal (Var "i") (Var "j"))))
                      (Assign "result" (Sub (Var "j") (Var "i")))
                      (Assign "result" (Sub (Var "i") (Var "j"))))
                   (Assign "Result" (Var "result"))))))``;

val (th,rw) = time (DERIVE_SEP_SPEC "Tritype") ``
       (Seq (Assign "trityp" (Const 0))
          (Seq
             (Cond
                (Or
                   (Or (Equal (Var "i") (Const 0))
                      (Equal (Var "j") (Const 0)))
                   (Equal (Var "k") (Const 0))) (Assign "trityp" (Const 4))
                (Seq (Assign "trityp" (Const 0))
                   (Seq
                      (Cond (Equal (Var "i") (Var "j"))
                         (Assign "trityp" (Plus (Var "trityp") (Const 1)))
                         Skip)
                      (Seq
                         (Cond (Equal (Var "i") (Var "k"))
                            (Assign "trityp"
                               (Plus (Var "trityp") (Const 2))) Skip)
                         (Seq
                            (Cond (Equal (Var "j") (Var "k"))
                               (Assign "trityp"
                                  (Plus (Var "trityp") (Const 3))) Skip)
                            (Cond (Equal (Var "trityp") (Const 0))
                               (Cond
                                  (Or
                                     (Or
                                        (Or
                                           (Less (Plus (Var "i") (Var "j"))
                                              (Var "k"))
                                           (Equal
                                              (Plus (Var "i") (Var "j"))
                                              (Var "k")))
                                        (Or
                                           (Less (Plus (Var "j") (Var "k"))
                                              (Var "i"))
                                           (Equal
                                              (Plus (Var "j") (Var "k"))
                                              (Var "i"))))
                                     (Or
                                        (Less (Plus (Var "i") (Var "k"))
                                           (Var "j"))
                                        (Equal (Plus (Var "i") (Var "k"))
                                           (Var "j"))))
                                  (Assign "trityp" (Const 4))
                                  (Assign "trityp" (Const 1)))
                               (Cond (Less (Const 3) (Var "trityp"))
                                  (Assign "trityp" (Const 3))
                                  (Cond
                                     (And (Equal (Var "trityp") (Const 1))
                                        (Less (Var "k")
                                           (Plus (Var "i") (Var "j"))))
                                     (Assign "trityp" (Const 2))
                                     (Cond
                                        (And
                                           (Equal (Var "trityp") (Const 2))
                                           (Less (Var "j")
                                              (Plus (Var "i") (Var "k"))))
                                        (Assign "trityp" (Const 2))
                                        (Cond
                                           (And
                                              (Equal (Var "trityp")
                                                 (Const 3))
                                              (Less (Var "i")
                                                 (Plus (Var "j")
                                                    (Var "k"))))
                                           (Assign "trityp" (Const 2))
                                           (Assign "trityp"
                                              (Const 4))))))))))))
             (Assign "Result" (Var "trityp"))))``;

val (th,rw) = time (DERIVE_SEP_SPEC "Foo") ``
       (Assign "Result" (Sub (Var "i") (Var "j")))``;

val (th,rw) = time (DERIVE_SEP_SPEC "Ex1") ``
       (Seq (Assign "result" (Const 0))
          (Seq (Assign "k" (Const 0))
             (Seq (Assign "result" (Plus (Var "k") (Var "j")))
                (Seq (Assign "k" (Plus (Const 12) (Const 8)))
                   (Seq (Assign "k" (Plus (Var "k") (Const 3)))
                      (Seq
                         (Cond (Equal (Var "i") (Var "j"))
                            (Assign "result" (Var "k")) Skip)
                         (Seq
                            (Cond (Less (Var "j") (Var "i"))
                               (Assign "result" (Plus (Var "k") (Const 1)))
                               Skip)
                            (Cond
                               (Or (Less (Var "i") (Var "j"))
                                  (Equal (Var "i") (Var "j")))
                               (Seq (Assign "i" (Const 3))
                                  (Assign "result"
                                     (Plus (Var "result") (Var "i"))))
                               (Assign "result" (Var "k"))))))))))``;


(* ====================================================================================== *)
(*  EXAMPLES WITH LOOPS                                                                   *)
(* ====================================================================================== *)

val (th,rw) = time (DERIVE_SEP_SPEC "ConditionnalSum") ``
       (Seq (Assign "s" (Const 0))
          (Seq
             (Cond (Not (Less (Var "n") (Var "k")))
                (Assign "s" (Plus (Var "n") (Var "k")))
                (Seq (Assign "i" (Const 0))
                   (While
                      (Or (Less (Var "i") (Var "n"))
                         (Equal (Var "i") (Var "n")))
                      (Seq (Assign "s" (Plus (Var "s") (Var "i")))
                         (Assign "i" (Plus (Var "i") (Const 1)))))))
             (Assign "Result" (Var "s"))))``;

val (th,rw) = time (DERIVE_SEP_SPEC "NestedLoop") ``
       (Seq (Assign "s" (Const 0))
          (Seq (Assign "i" (Const 1))
             (Seq
                (While
                   (Or (Less (Var "i") (Var "n"))
                      (Equal (Var "i") (Var "n")))
                   (Seq (Assign "j" (Const 1))
                      (Seq
                         (While
                            (Or (Less (Var "j") (Var "n"))
                               (Equal (Var "j") (Var "n")))
                            (Seq (Assign "s" (Plus (Var "s") (Const 1)))
                               (Assign "j" (Plus (Var "j") (Const 1)))))
                         (Assign "i" (Plus (Var "i") (Const 1))))))
                (Assign "Result" (Var "s")))))``

val (th,rw) = time (DERIVE_SEP_SPEC "NestedLoopKO1") ``
       (Seq (Assign "s" (Const 0))
          (Seq (Assign "i" (Const 0))
             (Seq
                (While
                   (Or (Less (Var "i") (Var "n"))
                      (Equal (Var "i") (Var "n")))
                   (Seq (Assign "j" (Const 0))
                      (Seq
                         (While
                            (Or (Less (Var "j") (Var "n"))
                               (Equal (Var "j") (Var "n")))
                            (Seq (Assign "s" (Plus (Var "s") (Const 1)))
                               (Assign "j" (Plus (Var "j") (Const 1)))))
                         (Assign "i" (Plus (Var "i") (Const 1))))))
                (Assign "Result" (Var "s")))))``;

val (th,rw) = time (DERIVE_SEP_SPEC "Sum") ``
       (Seq (Assign "s" (Const 0))
          (Seq
             (Cond (Not (Less (Var "n") (Var "k")))
                (Assign "s" (Plus (Var "n") (Var "k")))
                (Seq (Assign "i" (Const 0))
                   (While
                      (Or (Less (Var "i") (Var "n"))
                         (Equal (Var "i") (Var "n")))
                      (Seq (Assign "s" (Plus (Var "s") (Var "i")))
                         (Assign "i" (Plus (Var "i") (Const 1)))))))
             (Assign "Result" (Var "s"))))``;

val (th,SquareSum_def) = time (DERIVE_SEP_SPEC "SquareSum") ``
       (Seq (Assign "i" (Const 0))
          (Seq (Assign "s" (Const 0))
             (Seq
                (While
                   (Or (Less (Var "i") (Var "n"))
                      (Equal (Var "i") (Var "n")))
                   (Seq
                      (Assign "s"
                         (Plus (Var "s") (Times (Var "i") (Var "i"))))
                      (Assign "i" (Plus (Var "i") (Const 1)))))
                (Assign "Result" (Var "s")))))``;

val th2 = SEP_SPEC_SEMANTICS th;


(* ====================================================================================== *)
(*  EXAMPLES WITH ARRAYS (AND LOOPS)                                                      *)
(* ====================================================================================== *)

val (th,Swap_def) = time (DERIVE_SEP_SPEC "Swap") ``
       (Seq (Assign "temp" (Arr "a" (Var "i")))
          (Seq (ArrayAssign "a" (Var "i") (Var "j"))
               (ArrayAssign "a" (Var "j") (Var "temp"))))``;

val (th,FindMin_def) = time (DERIVE_SEP_SPEC "FindMin") ``
       (Seq (Assign "min" (Arr "a" (Var "j")))
          (While (Less (Var "i") (Var "j"))
             (Seq (Assign "j" (Sub (Var "j") (Const 1)))
                  (Cond (Less (Arr "a" (Var "j")) (Var "min"))
                        (Assign "min" (Arr "a" (Var "j"))) Skip))))``;


val _ = export_theory();
