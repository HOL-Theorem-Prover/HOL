structure labelLib :> labelLib =
struct

open HolKernel boolLib labelTheory

val ERR = mk_HOL_ERR "labelLib";

(* following makes label_tm independent of name chosen in labelTheory;
   requires defining theorem of form !v1..vn. lab x1 .. xn = ..
*)
val label_tm = #1 (strip_comb (lhs (#2 (strip_forall (concl label_def)))))

val label_ty = fst(dom_rng(type_of label_tm))

fun mk_label (s, t) =
    if type_of t <> bool then
      raise ERR "mk_label" "First argument not boolean"
    else
      list_mk_comb(label_tm, [mk_var(s, label_ty), t]);

fun dest_label tm = 
 ((fst o dest_var)##I) 
 (dest_binop label_tm (ERR "" "") tm)
 handle HOL_ERR _ => raise ERR "dest_label" "" ;

val is_label = can dest_label;

val DEST_LABEL_CONV = REWR_CONV label_def

val DEST_LABELS_CONV = PURE_REWRITE_CONV [label_def]

val DEST_LABEL = CONV_RULE DEST_LABEL_CONV
val DEST_LABELS = CONV_RULE DEST_LABELS_CONV

val DEST_LABELS_TAC = CONV_TAC DEST_LABELS_CONV THEN
                      RULE_ASSUM_TAC DEST_LABELS

fun lb s = mk_var(s, label_ty);
fun LB s = REFL (lb s)

fun MK_LABEL(s, th) = EQ_MP (SYM (SPECL [lb s, concl th] label_def)) th

fun ASSUME_NAMED_TAC s bth : tactic = ASSUME_TAC (MK_LABEL(s, bth))

fun dest_label_ref th = let
  val p as (l,r) = dest_eq (concl th)
  val _ =
      is_var l andalso is_var r andalso Term.compare p = EQUAL andalso
      Type.compare(type_of l, label_ty) = EQUAL orelse
      raise ERR "dest_label_ref" "Theorem not a label reference"
in
  #1 (dest_var l)
end

val is_label_ref = can dest_label_ref

(*---------------------------------------------------------------------------*)
(* Given an LB encoded label reference, finds a corresponding term in the    *)
(*   assumption list.                                                        *)
(*---------------------------------------------------------------------------*)

fun find_labelled_assumption labelth asl = let
  val labname = dest_label_ref labelth
  fun matching_asm t =
      (#1 (dest_label t) = labname) handle HOL_ERR _ => false
in
  case List.find matching_asm asl of
    SOME t => DEST_LABEL (ASSUME t)
  | NONE => raise ERR "find_labelled_assumption"
                      ("No assumption with label \""^labname^"\"")
end;

fun LABEL_ASSUM s ttac (asl, w) =
   ttac (find_labelled_assumption (LB s) asl) (asl, w)

(*---------------------------------------------------------------------------*)
(* LABEL_X_ASSUM is almost identical to LABEL_ASSUM. But it is not applied   *)
(* to the goal, but to a goal with the labelled assumption removed.          *)
(*---------------------------------------------------------------------------*)

fun name_assoc s [] = NONE
  | name_assoc s (tm::rst) =
     case total dest_label tm
      of NONE => name_assoc s rst
       | SOME (n,tm') => if s=n then SOME(tm,(n,tm'))
                          else name_assoc s rst;

fun LABEL_X_ASSUM s ttac : tactic =
 fn (asl,w) =>
   case name_assoc s asl
    of NONE => raise ERR "LABEL_X_ASSUM"
                ("Can't find term named by "^Lib.quote s^" in assumptions")
     | SOME(named_tm,_)
         => ttac (DEST_LABEL(ASSUME named_tm))
                 (op_set_diff aconv asl [named_tm],w);

(*---------------------------------------------------------------------------*)
(* Given a list of theorems thl and a list of assumptions asl, return a list *)
(* consisting of (a) the elements of thl that are not just tags signifying   *)
(* which elements of asl to assume; (b) the non-labelled elements of asl     *)
(* (just ASSUME'd); (c) the elements of asl having labels obtained by        *)
(* looking at the dummy theorems in thl of the form |- label = label. This   *)
(* means that some labelled elements of asl might be excluded.               *)
(*---------------------------------------------------------------------------*)

fun LLABEL_RESOLVE thl asl = let
  val (labelled_asms, other_asms) = List.partition is_label asl
  val (labelrefs, realths) = List.partition is_label_ref thl
  val wanted_lab_assums =
      map (fn lb => find_labelled_assumption lb labelled_asms) labelrefs
in
  map ASSUME other_asms @ wanted_lab_assums @ realths
end

fun LABEL_RESOLVE th (asl, w) = hd (LLABEL_RESOLVE [th] asl)

end; (* struct *)
