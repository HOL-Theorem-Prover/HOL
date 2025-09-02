Theory lambdaState
Ancestors
  itreeTau

(* Extension of itreeTauTheory *)
val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.declare_monad("itree", {unit = “Ret”, bind = “itree_bind”,
                                  ignorebind = NONE,
                                  choice = NONE,
                                  fail = NONE,
                                  guard = NONE});
val _ = monadsyntax.enable_monad "itree";

(* Unicode operator overloads *)
val _ = temp_set_fixity "≈" (Infixl 500);
Overload "≈" = “itree_wbisim”;
val _ = temp_set_fixity ">>=" (Infixl 500);
Overload ">>=" = “itree_bind”;

Overload "case" = “itree_CASE”;

(* Defining a simple imperative language syntax *)
Datatype:
  prog = Seq prog prog
       | Skip
       | FlipCoin prog prog
         (* if Math.random() then p1 else p2 *)
       | While prog (* while true *)
       | Call num (* function call, no arguments *)
End

(* The following functions define an itree semantics of the language.
   In this language, the program state is a immutatble function
   num -> prog.
*)

Definition itree_step:
  itree_step state Skip = Ret' () ∧
  itree_step state (FlipCoin p1 p2) =
    Vis' () (λb. if b then p1 else p2) ∧
  itree_step state (Call n) =
    Tau' $ state n ∧
  itree_step state (While p) =
    Tau' $ Seq p (While p) ∧
  itree_step state (Seq p q) =
  (case itree_step state p of
     Ret' () => Tau' q
   | Tau' p' => Tau' $ Seq p' q
   | Vis' _ k =>
     Vis' () (λb. Seq (k b) q))
End

Definition itree_semantics:
  itree_semantics state prog =
  itree_unfold (itree_step state) prog
End

(* Some useful properties of the language itree semantics *)
Theorem seq_bind_funs:
  itree_semantics env (Seq p q) = (itree_semantics env p) >>= (λx. Tau (itree_semantics env q))
Proof
  rw[Once itree_strong_bisimulation] >>
  qexists ‘CURRY {(itree_semantics env (Seq p' q), (itree_semantics env p'') >>= (λx. Tau (itree_semantics env q))) | p' = p''}’ >>
  rw[]
  >- (qexists ‘(p, p)’ >>
      rw[]
     )
  >- (Cases_on ‘x’ >> gvs[] >>
      gvs[itree_semantics, Once itree_unfold, itree_step] >>
      BasicProvers.FULL_CASE_TAC >> gvs[]
     )
  >- (Cases_on ‘x’ >> gvs[] >>
      gvs[itree_semantics, Once itree_unfold, itree_step] >>
      BasicProvers.FULL_CASE_TAC >> gvs[]
      >- rw[itree_semantics, Once itree_unfold, itree_step] >>
      rw[itree_semantics, Once itree_unfold, itree_step] >>
      disj1_tac >>
      qexists ‘(s, s)’ >>
      rw[]
     ) >>
  Cases_on ‘x’ >> gvs[] >>
  gvs[itree_semantics, Once itree_unfold, itree_step] >>
  BasicProvers.FULL_CASE_TAC >> gvs[] >>
  rw[itree_semantics, Once itree_unfold, itree_step] >>
  disj1_tac >>
  qexists ‘((f' s), (f' s))’ >>
  rw[]
QED

Theorem seq_bind_unfold_funs:
  itree_unfold (itree_step env) (Seq p q) =
  itree_unfold (itree_step env) p >>=
               (λx. Tau (itree_unfold (itree_step env) q))
Proof
  assume_tac seq_bind_funs >>
  gvs[itree_semantics]
QED

Theorem ret_seq_tree:
  Ret () >>= (λx. a) = a
Proof
  rw[]
QED

Theorem if_seq_tree:
  (if x then a else b) >>= c = (if x then a >>= c else b >>= c)
Proof
  rw[]
QED

Theorem tau_seq_tree:
  Tau p >>= q = Tau (p >>= q)
Proof
  rw[]
QED

Theorem vis_seq_tree:
  Vis f (λx. p) >>= q = Vis f (λx. p >>= q)
Proof
  rw[]
QED
