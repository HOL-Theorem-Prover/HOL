structure markerLib :> markerLib =
struct

open HolKernel boolLib markerTheory markerSyntax;

val ERR = mk_HOL_ERR "markerLib" ;

(*---------------------------------------------------------------------------*)
(* Support for "short-term markers".                                         *)
(*---------------------------------------------------------------------------*)

val stmark_term = REWR_CONV (GSYM stmarker_def)

fun stmark_conjunct P tm = let
in
  if is_conj tm then
    LAND_CONV (stmark_conjunct P) ORELSEC RAND_CONV (stmark_conjunct P)
  else if P tm then stmark_term
  else NO_CONV
end tm

fun stmark_disjunct P tm = let
in
  if is_disj tm then
    LAND_CONV (stmark_disjunct P) ORELSEC RAND_CONV (stmark_disjunct P)
  else if P tm then stmark_term
  else NO_CONV
end tm

fun is_stmarked t = same_const stmarker_tm (rator t) handle HOL_ERR _ => false

val [comm, assoc, commassoc] = CONJUNCTS (SPEC_ALL markerTheory.move_left_conj)

fun move_stmarked_conj_left tm = let
in
  if is_stmarked tm then ALL_CONV
  else if is_conj tm then
    (LAND_CONV move_stmarked_conj_left THENC TRY_CONV (REWR_CONV assoc))
      ORELSEC
    (RAND_CONV move_stmarked_conj_left THENC
     (REWR_CONV commassoc ORELSEC REWR_CONV comm))
  else NO_CONV
end tm

val move_stmarked_conj_left =
    move_stmarked_conj_left THENC
    (LAND_CONV (REWR_CONV stmarker_def) ORELSEC REWR_CONV stmarker_def)

val move_stmarked_conj_right =
    PURE_REWRITE_CONV [move_right_conj] THENC
    (RAND_CONV (REWR_CONV stmarker_def) ORELSEC REWR_CONV stmarker_def)
val move_stmarked_disj_left =
    PURE_REWRITE_CONV [move_left_disj] THENC
    (LAND_CONV (REWR_CONV stmarker_def) ORELSEC REWR_CONV stmarker_def)

val move_stmarked_disj_right =
    PURE_REWRITE_CONV [move_right_conj] THENC
    (RAND_CONV (REWR_CONV stmarker_def) ORELSEC REWR_CONV stmarker_def)

fun move_conj_left P = stmark_conjunct P THENC move_stmarked_conj_left
fun move_conj_right P = stmark_conjunct P THENC move_stmarked_conj_right
fun move_disj_left P = stmark_disjunct P THENC move_stmarked_disj_left
fun move_disj_right P = stmark_disjunct P THENC move_stmarked_disj_right

(*---------------------------------------------------------------------------*)
(* Dealing with simplifier directives encoded as tags on theorems.           *)
(*---------------------------------------------------------------------------*)

fun AC th1 th2 =
  EQ_MP (SYM (SPECL [concl th1, concl th2] markerTheory.AC_DEF))
        (CONJ th1 th2);

fun unAC th = let val th1 = PURE_REWRITE_RULE [AC_DEF] th
              in (CONJUNCT1 th1, CONJUNCT2 th1)
              end;

fun Cong th = EQ_MP (SYM(SPEC (concl th) markerTheory.Cong_def)) th;

fun unCong th = PURE_REWRITE_RULE [Cong_def] th;

(*---------------------------------------------------------------------------*)
(* Support for abbreviations.                                                *)
(*---------------------------------------------------------------------------*)

val DeAbbrev = CONV_RULE (REWR_CONV Abbrev_def)

fun Abbrev_wrap eqth =
    EQ_MP (SYM (Thm.SPEC (concl eqth) Abbrev_def)) eqth

fun ABB l r =
 CHOOSE_THEN (fn th => SUBST_ALL_TAC th THEN ASSUME_TAC (Abbrev_wrap(SYM th)))
             (Thm.EXISTS(mk_exists(l, mk_eq(r, l)), r) (Thm.REFL r));

fun ABBREV_TAC eq = let val (l,r) = dest_eq eq in ABB l r end;

local
   val match_var_or_const = ref true
in
   val () = Feedback.register_btrace
               ("PAT_ABBREV_TAC: match var/const", match_var_or_const)

   fun PAT_ABBREV_TAC fv_set eq (g as (asl, w)) =
      let
         open HOLset
         val (l, r) = dest_eq eq
         val rvs = FVL [r] empty_tmset
         val l' = gen_variant Parse.is_constname ""
                              (listItems(union(fv_set, rvs))) l
         fun matchr t =
           case raw_match [] fv_set r t ([],[]) of
               ((tmsub, _), (tysub, _)) => (tmsub, tysub)
         fun finder (bvs, t) =
           case List.find (fn v => HOLset.member(rvs, v)) bvs of
               SOME _ => NONE
             | NONE =>
               if (is_var t orelse is_const t) andalso not (!match_var_or_const)
               then NONE
               else
                 case Lib.total matchr t of
                     NONE => NONE
                   | SOME (tmsub, tysub) =>
                     let
                       open HOLset
                       val bv_set = addList(empty_tmset, bvs)
                       fun badt t =
                         not (isEmpty (intersection (FVL [t] empty_tmset,
                                                     bv_set)))
                     in
                       case List.find (fn {redex,residue=t} => badt t) tmsub of
                           NONE => SOME(t, tysub)
                         | SOME _ => NONE
                     end
      in
         case gen_find_term finder w of
            NONE => raise ERR "PAT_ABBREV_TAC" "No matching term found"
          | SOME (t, tysub) => ABB (Term.inst tysub l') t g
      end
end

fun fixed_tyvars ctxt pattern =
  Lib.U (map type_vars_in_term (op_intersect aconv ctxt (free_vars pattern)))

fun ABB' {redex=l,residue=r} = ABB l r

val safe_inst_cmp = let
  fun img {redex,residue} =
      (term_size residue, (residue, #1 (dest_var redex) handle HOL_ERR _ => ""))
  val cmp = pair_compare
             (flip_cmp Int.compare, pair_compare (Term.compare, String.compare))
in
  inv_img_cmp img cmp
end
val safe_inst_sort =
    List.filter
      (fn {redex,residue} => String.sub(#1 (dest_var redex),0) <> #"_") o
    Listsort.sort safe_inst_cmp

fun MATCH_ABBREV_TAC fv_set pattern (g as (asl, w)) = let
  val ctxt = HOLset.listItems fv_set
  val (tminst,_) = match_terml (fixed_tyvars ctxt pattern) fv_set pattern w
in
  MAP_EVERY ABB' (safe_inst_sort tminst) g
end

fun MATCH_ASSUM_ABBREV_TAC fv_set pattern (g as (asl, w)) = let
  val ctxt = HOLset.listItems fv_set
  val fixed = fixed_tyvars ctxt pattern
  fun find [] = raise ERR "MATCH_ASSUM_ABBREV_TAC" "No matching assumption found"
    | find (asm::tl) =
      case total (match_terml fixed fv_set pattern) asm of
        NONE => find tl
      | SOME (tminst,_) => MAP_EVERY ABB' (safe_inst_sort tminst) g
                           handle HOL_ERR e => find tl
in find asl end

fun HO_MATCH_ABBREV_TAC fv_set pattern (gl as (asl,w)) =
 let val ctxt = HOLset.listItems fv_set
     val (tminst, tyinst) = ho_match_term (fixed_tyvars ctxt pattern) fv_set pattern w
     val unbeta_goal =
        Tactical.default_prover(mk_eq(w, subst tminst (inst tyinst pattern)),
                                BETA_TAC THEN REFL_TAC)
in
  CONV_TAC (K unbeta_goal) THEN MAP_EVERY ABB' (safe_inst_sort tminst)
end gl;

fun UNABBREV_TAC s =
 FIRST_X_ASSUM(SUBST_ALL_TAC o
               assert(equal s o fst o dest_var o lhs o concl) o
               DeAbbrev);

val UNABBREV_ALL_TAC =
 let fun ttac th0 =
      let val th = DeAbbrev th0
      in SUBST_ALL_TAC th ORELSE ASSUME_TAC th
      end
 in
  REPEAT (FIRST_X_ASSUM ttac)
end

fun RM_ABBREV_TAC s =
  FIRST_X_ASSUM (K ALL_TAC o
                 assert(equal s o fst o dest_var o lhs o concl) o
                 DeAbbrev)

val RM_ALL_ABBREVS_TAC = REPEAT (FIRST_X_ASSUM (K ALL_TAC o DeAbbrev))

(*---------------------------------------------------------------------------*)
(* Given an abbreviation context, and a goal with possibly more abbrevs,     *)
(* reabbreviate the goal.                                                    *)
(*---------------------------------------------------------------------------*)

fun CNTXT_REABBREV_TAC abbrevs (gl as (asl,_)) =
 let val abbrevs' = filter is_abbrev asl
     val ordered_abbrevs = topsort compare_abbrev (abbrevs@abbrevs')
     val lrs = map (dest_eq o rand) ordered_abbrevs
 in UNABBREV_ALL_TAC THEN MAP_EVERY (uncurry ABB) lrs
 end gl;

(*---------------------------------------------------------------------------*)
(* Execute a tactic in a goal with no abbreviations, then restore the        *)
(* abbrevs, also taking account of any new abbreviations that came in from   *)
(* the application of the tactic.                                            *)
(*---------------------------------------------------------------------------*)

fun WITHOUT_ABBREVS tac (gl as (asl,_)) =
 let val abbrevs = filter is_abbrev asl
 in UNABBREV_ALL_TAC THEN tac THEN CNTXT_REABBREV_TAC abbrevs
 end gl;

(*---------------------------------------------------------------------------*)
(* REABBREV_TAC ought to be called after BasicProvers.LET_ELIM_TAC, which    *)
(* introduces an abbrev, but doesn't propagate the abbrev. to the other      *)
(* assumptions. This has been done in basicProof/BasicProvers.               *)
(*---------------------------------------------------------------------------*)

val REABBREV_TAC = WITHOUT_ABBREVS ALL_TAC;

(*---------------------------------------------------------------------------*)
(*  ABBRS_THEN: expand specified abbreviations before applying a tactic.     *)
(* Typically, the abbreviations are designated in the thm list of a          *)
(* simplification tactic thusly:                                             *)
(*                                                                           *)
(*     ASM_SIMP_TAC ss [ ..., Abbr`m`, ... ]                                 *)
(*                                                                           *)
(* which says to find and expand the abbreviation                            *)
(*                                                                           *)
(*      Abbrev (m = tm)                                                      *)
(*                                                                           *)
(* in the assumptions of the goal before proceeding with simplification.     *)
(*---------------------------------------------------------------------------*)

fun ABBRS_THEN thl_tac thl =
 let val (abbrs, rest) = List.partition is_abbr thl
 in
  MAP_EVERY (UNABBREV_TAC o dest_abbr) abbrs THEN thl_tac rest
 end

val MK_ABBREVS_OLDSTYLE =
    RULE_ASSUM_TAC (fn th => (th |> DeAbbrev |> SYM) handle HOL_ERR _ => th)



(*---------------------------------------------------------------------------*)
(* Support for user-defined labels.                                          *)
(*---------------------------------------------------------------------------*)

val DEST_LABEL_CONV = REWR_CONV label_def

val DEST_LABELS_CONV = PURE_REWRITE_CONV [label_def]

val DEST_LABEL = CONV_RULE DEST_LABEL_CONV
val DEST_LABELS = CONV_RULE DEST_LABELS_CONV

val DEST_LABELS_TAC = CONV_TAC DEST_LABELS_CONV THEN RULE_ASSUM_TAC DEST_LABELS

fun lb s = mk_var(s, label_ty);
fun LB s = REFL (lb s)

fun MK_LABEL(s, th) = EQ_MP (SYM (SPECL [lb s, concl th] label_def)) th

fun ASSUME_NAMED_TAC s bth : tactic = ASSUME_TAC (MK_LABEL(s, bth))

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

end
