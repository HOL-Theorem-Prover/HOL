
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

Definition imp2imp2_def:
    (imp2imp2 (SKIP:imp$com) = []) /\
    (imp2imp2 (Assign v a) = [((Assign v a):com)]) /\
    (imp2imp2 (Seq c1 c2) = (imp2imp2 c1) ++ (imp2imp2 c2)) /\
    (imp2imp2 (If b c1 c2) = [(If b (imp2imp2 c1) (imp2imp2 c2))]) /\
    (imp2imp2 (While b c) = [(While b (imp2imp2 c))])
End

Definition p2imp_def:
    (p2imp [] = SKIP) /\
    (p2imp (x::xs) = Seq (imp2imp x) (p2imp xs)) /\
    (imp2imp ((Assign v a):com) = ((Assign v a):imp$com)) /\
    (imp2imp (If b c1s c2s) = (If b (p2imp c1s) (p2imp c2s))) /\
    (imp2imp (While b cs) = (While b (p2imp cs)))
Termination
    WF_REL_TAC `inv_image (measure I) (\r. case r of
        | INR c => com_size c
        | INL cs => com1_size cs)`
End
(* wow terminationa actually worked...I thought it had to be stricly decreasing but I don't think this is *)


Theorem com_lt:
    !c h t. MEM c t ==> com_size c < com1_size (h::t)
Proof
    rw[] >>
    simp[com_size_def] >>
    Induct_on `t` >>
    rw[] >>
    simp[com_size_def] >>
    fs[]
QED

Theorem com_ineq:
    !c cs. MEM c cs ==> com_size c <= com1_size cs
Proof
    rw[] >>
    simp[LESS_OR_EQ] >>
    Cases_on `cs` >>
    fs[MEM]
        >- simp[com_size_def]
        >- simp[com_lt]
QED


(* Theorem pval_NONE[simp]:
    pval 0 cs s = NONE
Proof
    rw[cval_def]
QED *)

Theorem cval_mono:
    (!t1 c s t2. t1 <= t2 /\ cval t1 c s <> NONE ==> cval t1 c s = cval t2 c s) /\
    (!t1 cs s t2. t1 <= t2 /\ pval t1 cs s <> NONE ==> pval t1 cs s = pval t2 cs s)
Proof
    ho_match_mp_tac cval_ind >>
    rw[] >>
    Cases_on `t2`
        >- fs[cval_def]
        >- fs[cval_def]
        >- fs[]
        >- simp[cval_def]
        >- fs[]
        >- (simp[cval_def] >>
            first_x_assum $ qspec_then `SUC n` assume_tac >>
            gvs[cval_def]
        )
        >- fs[]
        >- (simp[cval_def] >>
            first_x_assum $ qspec_then `SUC n` assume_tac >>
            gvs[cval_def]
        )
        >- fs[]
        >- (Cases_on `bval b s` >>
            fs[]
                >- (simp[cval_def] >>
                    first_x_assum $ qspec_then `n` assume_tac >>
                    gvs[cval_def]
                )
                >- simp[cval_def]
        )
        >- simp[]
        >- fs[cval_def]
        >- fs[]
        >- simp[cval_def]
        >- fs[]
        >- (simp[cval_def] >>
            first_x_assum $ qspec_then `SUC n` assume_tac >>
            Cases_on `cval (SUC v26) c s`
                >- gvs[cval_def] (* got lazy trying to do granularly but seems straight forward *)
                >- (gvs[] >>
                    last_x_assum $ qspec_then `SUC n` assume_tac >>
                    Cases_on `cval (SUC n) c s` (* why do I have to do this to force rewrite *)
                        >- fs[]
                        >- (gvs[] >>
                            Cases_on `pval (SUC v26) cs x`
                                >- gvs[cval_def]
                                >- gvs[]
                        )
                )
        )
QED

Theorem pval_concat:
    ! t l1 l2 s. pval t (l1 ++ l2) s = OPTION_BIND (pval t l1 s) (pval t l2)
Proof
    Cases_on `t`
        >- simp[cval_def]
        >- (Induct_on `l1`
            >- simp[cval_def]
            >- (simp[cval_def] >>
                rpt strip_tac >>
                Cases_on `cval (SUC n) h s`
                    >- simp[]
                    >- fs[cval_def]
            )
        )
QED

(* is an equality theorem more useful than an inequality theorem??? *)
Theorem seq_none:
    cval (Seq c c') s t <> NONE ==> cval c s t <> NONE
Proof
    rw[] >>
    fs[impTheory.cval_def] >>
    Cases_on `cval c s t` >>
    fs[]
QED

val _ = export_theory();
