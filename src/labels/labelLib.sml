structure labelLib :> labelLib =
struct

open HolKernel boolLib labelTheory

val ERR = mk_HOL_ERR "labelLib";

(* following makes label_tm independent of name chosen in labelTheory;
   requires defining theorem of form !v1..vn. lab x1 .. xn = ..
*)
val label_tm = #1 (strip_comb (lhs (#2 (strip_forall (concl label_def)))))

(* assume first argument to label_tm is of label_type *)
val label_ty = hd (#1 (strip_fun (type_of label_tm)))

fun lb s = mk_var(s, label_ty);

fun LB s = REFL (lb s)

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

val DEST_LABEL_CONV = REWR_CONV label_def
val DEST_LABELS_CONV = PURE_REWRITE_CONV [label_def]

val DEST_LABEL = CONV_RULE DEST_LABEL_CONV
val DEST_LABELS = CONV_RULE DEST_LABELS_CONV

val DEST_LABELS_TAC = CONV_TAC DEST_LABELS_CONV THEN
                      RULE_ASSUM_TAC DEST_LABELS

fun MK_LABEL(s, th) = EQ_MP (SYM (SPECL [lb s, concl th] label_def)) th

fun dest_label tm = let
  val (f, args) = strip_comb tm
in
  if same_const f label_tm andalso length args = 2 then
    (#1 (dest_var (hd args)), hd (tl args))
  else
    raise ERR "dest_label" "Term not labelled"
end

val is_label = can dest_label
fun mk_label (s, t) =
    if type_of t <> bool then
      raise ERR "mk_label" "First argument not boolean"
    else
      list_mk_comb(label_tm, [mk_var(s, label_ty), t])

(* given an LB encoded label reference, finds a corresponding term in the
   assumption list *)
fun find_labelled_assumption labelth asl = let
  val labname = dest_label_ref labelth
  fun matching_asm t =
      (#1 (dest_label t) = labname) handle HOL_ERR _ => false
in
  case List.find matching_asm asl of
    SOME t => CONV_RULE (REWR_CONV label_def) (ASSUME t)
  | NONE => raise ERR "find_labelled_assumption"
                      ("No assumption with label \""^labname^"\"")
end;

(* from Konrad's notes: *)

fun name_assoc s [] = NONE
  | name_assoc s (tm::rst) =
     case total dest_label tm
      of NONE => name_assoc s rst
       | SOME (n, tm') => if s=n then SOME(tm,(n,tm'))
                          else name_assoc s rst;

fun ASSUME_NAMED_TAC s bth : tactic = ASSUME_TAC (MK_LABEL(s, bth))

fun LABEL_ASSUM s ttac (asl, w) =
   ttac (find_labelled_assumption (LB s) asl) (asl, w)

fun LABEL_X_ASSUM s ttac : tactic =
 fn (asl,w) =>
   case name_assoc s asl
    of NONE => raise ERR "LABEL_X_ASSUM"
                ("Can't find term named by "^Lib.quote s^" in assumptions")
     | SOME(named_tm,(_,core))
         => ttac (DEST_LABEL(ASSUME named_tm))
                 (op_set_diff aconv asl [named_tm],w);

fun LLABEL_RESOLVE thlist asl = let
  val (labelled_asms, other_asms) = List.partition is_label asl
  val (labelrefs, realths) = List.partition is_label_ref thlist
  val wanted_lab_assums =
      map (fn lb => find_labelled_assumption lb labelled_asms) labelrefs
in
  map ASSUME other_asms @ wanted_lab_assums @ realths
end

fun LABEL_RESOLVE th (asl, w) = hd (LLABEL_RESOLVE [th] asl)

end; (* struct *)
