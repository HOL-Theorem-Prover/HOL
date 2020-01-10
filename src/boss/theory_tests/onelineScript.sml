open HolKernel Parse boolLib bossLib;

val _ = new_theory "oneline";

Definition ZIP2:
  (ZIP2 ([],[]) z = []) /\
  (ZIP2 (x::xs,y::ys) z = (x,y) :: ZIP2 (xs, ys) (5:num))
Termination
  WF_REL_TAC ‘measure (\p. LENGTH (FST (FST p)) + LENGTH (SND (FST p)))’ >>
  simp[]
End

val oneline_zip2 = DefnBase.one_line_ify NONE ZIP2

Definition AEVERY_AUX_def:
  (AEVERY_AUX aux P [] <=> T) /\
  (AEVERY_AUX aux P ((x:'a,y:'b)::xs) <=>
     if MEM x aux then AEVERY_AUX aux P xs
     else
       P (x,y) /\ AEVERY_AUX (x::aux) P xs)
End

val oneline_aevery_aux = DefnBase.one_line_ify NONE AEVERY_AUX_def
val _ = assert (null o hyp) oneline_aevery_aux

Definition incomplete_literal:
  incomplete_literal 1 = 10 /\
  incomplete_literal 2 = 11 /\
  incomplete_literal 3 = 30
End

val oneline_incomplete = DefnBase.one_line_ify NONE incomplete_literal
val (theta, _) = match_term
  “incomplete_literal svar =
     case svar of 1 => 10 | 2 => 11 | 3 => 30 | _ => ARB”
  (concl oneline_incomplete)
val _ = length (hyp oneline_incomplete) = 1 andalso
        aconv (hd (hyp oneline_incomplete))
              (subst theta “svar = 1 \/ svar = 2 \/ svar = 3”) orelse
        raise Fail "incomplete_literal test fails"

Definition complete_literal0:
  complete_literal0 1 = 10 /\
  complete_literal0 2 = 12 /\
  complete_literal0 _ = 15
End

Theorem oneline_complete0[local] = DefnBase.one_line_ify NONE complete_literal0

Definition complete_literal1:
  complete_literal1 [] 1 = 10 /\
  complete_literal1 (3::t) 2 = 16 /\
  complete_literal1 (h::t) 2 = 12 + h /\
  complete_literal1 _ _ = 15
End

Theorem oneline_complete1[local] = DefnBase.one_line_ify NONE complete_literal1

Definition complete_literal2:
  complete_literal2 (3, [], 2) = 10 /\
  complete_literal2 (5, h::t, x) = 12 + h + x /\
  complete_literal2 _ = 15
End

Theorem oneline_complete2[local] = DefnBase.one_line_ify NONE complete_literal2

val _ = export_theory();
