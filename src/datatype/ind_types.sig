signature ind_types =
sig
 include Abbrev
 type constructor  = string * hol_type list
 type tyspec       = hol_type * constructor list

 val define_type  : tyspec list -> {induction:thm, recursion:thm}

 (* An induction principle as the rest of HOL expects to read one: the
    variables an argument is quantified over pushed past the hypothesis
    that mentions them, and the bound variables named for their types —
    `!P. P [] /\ (!t. P t ==> !h. P (h::t)) ==> !l. P l` rather than
    `!P. P [] /\ (!a0 a1. P a1 ==> P (a0::a1)) ==> !l. P l`.  INDUCT_THEN
    wants the first, and so do developments that name the variables an
    induction leaves them. *)
 val munge_ind_thm : thm -> thm

end
