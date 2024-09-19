
open HolKernel Parse boolLib bossLib;
open stringLib integerTheory;
open listTheory;
open arithmeticTheory;
open impTheory;
val ect = BasicProvers.EVERY_CASE_TAC;

val _ = new_theory "imp2";


val _ = temp_type_abbrev("vname",``:string``);

Datatype:
    com = Assign vname imp$aexp
        | If imp$bexp (com list) (com list)
        | While imp$bexp (com list)
End

val com_size_def = fetch "-" "com_size_def";

Definition cval_def:
    (cval 0 _ _ = NONE) /\
    (cval (t:num) (Assign v a) s = SOME ((v =+ aval a s) s)) /\
    (cval t (If b cs1 cs2) s = pval t (if bval b s then cs1 else cs2) s) /\
    (cval t (While b cs) s = if bval b s then pval (t-1) (cs ++ [(While b cs)]) s else SOME s) /\

    (pval 0 _ _ = NONE) /\
    (pval (t:num) [] s = SOME s) /\
    (pval t (c::cs) s = case cval t c s of
        | NONE => NONE
        | SOME s' => pval t cs s')
Termination
    WF_REL_TAC `inv_image (measure I LEX measure I) (\r. case r of
        | INR (t, cs, _) => (t, com1_size cs)
        | INL (t, c, _) => (t, com_size c))` >>
    rw[]
End

val _ = export_theory();
