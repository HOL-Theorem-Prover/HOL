Theory lambdaStateDecompilerTest
Ancestors
  itreeTau lambdaState
Libs
  lambdaStateDecompilerLib


(* Unicode operator overloads *)
val _ = temp_set_fixity "≈" (Infixl 500);
Overload "≈" = “itree_wbisim”;
val _ = temp_set_fixity ">>=" (Infixl 500);
Overload ">>=" = “itree_bind”;

Overload "case" = “itree_CASE”;

(* An example environment of

   fun 0 {
     if Math.random() then
       call 1
     else skip
   }

   fun 1 {
     if Math.random() then
       skip
     else
       call 1
   }
*)
val test1_env =
“λ(x:num).
   if x = 0 then
     FlipCoin (Call 1) Skip
   else if x = 1 then
     FlipCoin Skip (Call 1)
   else
     Skip
”

(* deep embedding *)
val test1_sem = “itree_semantics ^test1_env (Call 1)”


(* shallow embedding *)
(* fun1 should present as if it was defined like below:*)
Definition fun1:
  fun1 = itree_semantics ^test1_env (Call 1)
End

(* with manual proof *)
Theorem fun1_eqns':
  fun1 = Tau (Vis () (λx. if x then Ret () else fun1))
Proof
  rw[fun1, itree_semantics] >>
  rw[Once itree_unfold, itree_step] >>
  rw[Once itree_unfold, itree_step] >>
  rw[FUN_EQ_THM] >>
  BasicProvers.FULL_CASE_TAC >>
  rw[Once itree_unfold, itree_step]
QED

(* decompiler in action *)
val fun1_thms = proof_dec "fun1" “itree_semantics ^test1_env (Call 1)”

val fun0_thms = proof_dec "fun0" “itree_semantics ^test1_env (Call 0)”


(* trivial spin call environment *)
val call_only_env =
 “λ(x:num).
    Call 0
 ”
(* manual proofs *)
Definition call0_only:
  call0_only = itree_semantics ^call_only_env (Call 0)
End

Theorem call0_only_funs':
  call0_only = Tau (call0_only)
Proof
  rw[call0_only, itree_semantics] >>
  rw[Once itree_unfold, itree_step]
QED

(* make use of the decompiler *)
val call0_only_thms = proof_dec "call0_only" “itree_semantics ^call_only_env (Call 0)”


(* some sequencing example *)
val prog_seq_env =
 “λ(x:num).
    if x = 0 then
      FlipCoin (Call 1) (Seq Skip (Call 0))
    else if x = 1 then
      FlipCoin Skip (Seq (Call 1) (Call 0))
    else
      Skip
 ”

val prog_seq0_thms = proof_dec "prog_seq0" “itree_semantics ^prog_seq_env (Call 0)”

val prog_seq1_thms = proof_dec "prog_seq1" “itree_semantics ^prog_seq_env (Call 1)”

val prog_seq10_thms = proof_dec "prog_seq10" “itree_semantics ^prog_seq_env (Seq (Call 1) (Call 0))”


(* some arbitrary long program *)
val test_tree = “itree_semantics ^test1_env
                 (Seq (While (Seq (FlipCoin Skip (Call 1)) (FlipCoin (Call 0) Skip)))
                      (Seq (Skip)
                           ((Seq
                             (While (Seq (Call 1) (FlipCoin (Call 1) (Call 0))))
                             (Seq (While (FlipCoin (Call 0) (Call 1))) (Call 1))))))”

val test_tree_thms = proof_dec "test_tree" “^test_tree”
