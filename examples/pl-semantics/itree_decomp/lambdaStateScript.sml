Theory lambdaState
Ancestors
  itreeTau

(* Extension of itreeTauTheory *)
val _ = monadsyntax.enable_monadsyntax();
val _ = declare_monad("itree", {unit = “Ret”, bind = “itree_bind”,
            ignorebind = NONE,
            choice = NONE,
            fail = NONE,
            guard = NONE});
val _ = enable_monad "itree";

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

(* The following function defines an itree semantics of the language.
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

