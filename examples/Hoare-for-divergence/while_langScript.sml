open preamble lprefix_lubTheory

val _ = new_theory "while_lang";

Type nat[pp] = “:num”;

(* -- AST and other types -- *)

Type name  = “: string         ”
Type value = “: nat            ”
Type store = “: name -> value  ”
Type exp   = “: store -> value ”

Datatype:
  prog = Skip
       | Assign name exp
       | Print exp
       | Seq prog prog
       | If exp prog prog
       | While exp prog
End


(* -- small-step semantics -- *)

Type output    = “: value list     ”
Type state[pp] = “: store # output ”

Definition output_of_def:
  output_of ((s,out):state) = out
End

Definition subst_def:
  subst n e (s,out) = ((n =+ e s) s,out:value list)
End

Definition print_def:
  print e ((s,out):state) = (s,out ++ [e s])
End

Definition guard_def:
  guard x ((s,out):state) = (x s ≠ 0)
End

Inductive step:
  (∀s:state.
    step (Skip,s) (Skip,s))
  ∧
  (∀s n x.
     step (Assign n x,s) (Skip, subst n x s))
  ∧
  (∀s x.
     step (Print x,s) (Skip, print x s))
  ∧
  (∀s q.
     step (Seq Skip q,s) (q,s))
  ∧
  (∀p0 p1 q s0 s1.
     step (p0,s0) (p1,s1) ∧ p0 ≠ Skip ⇒
     step (Seq p0 q,s0) (Seq p1 q,s1))
  ∧
  (∀x p q s.
     step (If x p q, s) ((if guard x s then p else q), s))
  ∧
  (∀x p s.
     step (While x p, s) (If x (Seq p (While x p)) Skip, s))
End

Inductive terminates:
  ∀s p t. RTC step (p,s) (Skip,t) ⇒ terminates s p t
End

Inductive diverges:
  ∀s p output.
    (∀t. ~(terminates s p t)) ∧
    output = LUB { fromList out | ∃q t. RTC step (p,s) (q,t,out) }
    ⇒
    diverges s p output
End

val _ = export_theory();
