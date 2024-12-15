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

fun genmktagged th nm =
    let val v = mk_var(nm, alpha)
    in
      EQT_ELIM (SPEC v th)
    end
val Excl = genmktagged markerTheory.Exclude_def
val FRAG = genmktagged markerTheory.FRAG_def
val ExclSF = genmktagged markerTheory.ExcludeFrag_def


fun mk_marker_const nm = prim_mk_const{Thy = "marker", Name = nm}
val Excl_t = mk_marker_const "Exclude"
val ExclSF_t = mk_marker_const "ExcludeFrag"
val FRAG_t = mk_marker_const "FRAG"
fun gendest_tagged t th =
    let val c = concl th
        val f = rator c
    in
      if same_const t f then SOME (#1 (dest_var (rand c)))
      else NONE
    end handle HOL_ERR _ => NONE
val destExcl = gendest_tagged Excl_t
val destFRAG = gendest_tagged FRAG_t
val destExclSF = gendest_tagged ExclSF_t

val Req0_t = mk_marker_const "Req0"
val Req0_th = EQT_ELIM markerTheory.Req0_def
val ReqD_t = mk_marker_const "ReqD"
val ReqD_th = EQT_ELIM markerTheory.ReqD_def
val mk_Req0 = ADD_ASSUM Req0_t
val mk_ReqD = ADD_ASSUM ReqD_t

fun dest_Req0 th =
    if HOLset.member(hypset th, Req0_t) then SOME (PROVE_HYP Req0_th th)
    else NONE
fun dest_ReqD th =
    if HOLset.member(hypset th, ReqD_t) then SOME (PROVE_HYP ReqD_th th)
    else NONE

fun req0_modify tac th =
    case dest_Req0 th of
        NONE => (tac,th)
      | SOME th => (Ho_Rewrite.REQUIRE0_TAC th o tac, th)
fun reqD_modify tac th =
    case dest_ReqD th of
        NONE => (tac,th)
      | SOME th => (Ho_Rewrite.REQUIRE_DECREASE_TAC th o tac, th)

fun mk_require_tac tac thl =
    let
      fun recurse (accths,acctac) ths =
          case ths of
              [] => acctac (List.rev accths)
            | th::rest =>
              let
                val (tac,th) = req0_modify tac th
                val (tac,th) = reqD_modify tac th
              in
                recurse (th::accths,tac) rest
              end
    in
      recurse ([], tac) thl
    end

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

(* ----------------------------------------------------------------------
    Abbreviation Tidying

    Abbreviations should be of the form

       Abbrev(v = e)

    with v a variable. The tidying process eliminates assumptions that
    have Abbrev present at the top with an argument that is not of the
    right shape. As simplification sees abbreviation equations as
    rewrites of the form e = v (replacing occurrences of e with the
    abbreviation), the tidying process will flip equations to keep
    this "orientation".
   ---------------------------------------------------------------------- *)

fun TIDY_ABBREV_CONV t =
    if is_malformed_abbrev t then
      (REWR_CONV markerTheory.Abbrev_def THENC TRY_CONV (REWR_CONV EQ_SYM_EQ)) t
    else ALL_CONV t
val TIDY_ABBREV_RULE = CONV_RULE TIDY_ABBREV_CONV
val TIDY_ABBREVS = RULE_ASSUM_TAC TIDY_ABBREV_RULE


(*---------------------------------------------------------------------------*)
(* Support for user-defined labels.                                          *)
(*---------------------------------------------------------------------------*)

val DEST_LABEL_CONV = REWR_CONV label_def

val DEST_LABELS_CONV = PURE_REWRITE_CONV [label_def]

val DEST_LABEL = CONV_RULE DEST_LABEL_CONV
val DEST_LABELS = CONV_RULE DEST_LABELS_CONV

val DEST_LABELS_TAC = CONV_TAC DEST_LABELS_CONV THEN RULE_ASSUM_TAC DEST_LABELS


fun MK_LABEL(s, th) = EQ_MP (SYM (SPECL [mk_label_var s, concl th] label_def)) th

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
   ttac (find_labelled_assumption (L s) asl) (asl, w)

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

fun matching_asm th t =
    let
      val labname = dest_label_ref th
    in
      #1 (dest_label t) = labname
    end handle HOL_ERR _ => false

fun has_label_from lrefs t =
    List.exists (C matching_asm t) lrefs

fun LLABEL_RES_THEN thltac thl (g as (asl,w)) =
    let
      val (labelrefs, realths) = List.partition is_label_ref thl
      val (wanted_labelled_asms, rest) =
           List.partition (has_label_from labelrefs) asl
    in
      thltac (map (DEST_LABEL o ASSUME) wanted_labelled_asms @ realths) g
    end


fun LABEL_RESOLVE th (asl, w) = hd (LLABEL_RESOLVE [th] asl)

(* ----------------------------------------------------------------------
    using : tactic * thm -> tactic

    using th tac stashes theorem th in the goal so that tactic tac can
    use it if desired. If the tactic terminates, the stashed theorem
    is removed.

    Stashing is done by adding an assumption encoding the name of the
    theorem to the assumption list. This will cause mess-ups if you
    attempt something like

       pop_assum foo using bar

    so, don't do that.

    This can be nested, with multiple theorems stashed at once; the
    cleanup looks for the exact using theorem that it stashed when it
    removes it and does so with UNDISCH_THEN. So, if there are
    multiples of the same name, the most recent will be taken.

   ---------------------------------------------------------------------- *)

fun tac using th =
    let
      val uth = MK_USING th
    in
      ASSUME_TAC uth >>
      tac >>
      UNDISCH_THEN (concl uth) (K ALL_TAC)
    end

fun usingA tac th = tac using th

fun loc2thm loc =
    case loc of
        DB.Local s => (valOf (DB.local_thm s)
                       handle Option => raise ERR "loc2thm" "No such theorem")
      | DB.Stored {Name,Thy} =>
        DB.fetch Thy Name
        handle HOL_ERR _ => raise ERR "loc2thm" "No such theorem"


fun maybe_using gen ttac (g as (asl,w)) =
    case asl of
        h::_ => if is_using h then ttac (DEST_USING (ASSUME h)) g
                else MAP_FIRST ttac (gen()) g
      | _ => MAP_FIRST ttac (gen()) g

(* ----------------------------------------------------------------------
    hiding assumptions
   ---------------------------------------------------------------------- *)

val hidec = prim_mk_const{Thy = "marker", Name = "hide"}
val sv = mk_var("s", bool)
val tv = mk_var("t", bool)

fun hide_pp (tyg,tmg) backend printer ppfns gravs depth t =
    let
      open term_pp_types term_pp_utils smpp
      val (f,xs) = strip_comb t
      val _ = same_const f hidec andalso length xs = 2 orelse
              raise UserPP_Failed
      val (vname,_) = dest_var (hd xs) handle HOL_ERR _ => raise UserPP_Failed
      val {add_string, ublock, add_break, ...} = ppfns:ppstream_funs
      fun syspr t =
          printer { gravs = gravs, depth = decdepth depth, binderp = false } t
    in
      ublock PP.CONSISTENT 2 (
        add_string "HIDDEN:" >> add_break(1, 0) >>
        add_string vname
      )
    end

fun install_hidepp() =
    Parse.temp_add_user_printer ("hide-printer", list_mk_comb(hidec, [sv,tv]),
                                 hide_pp)
val _ = install_hidepp()
fun remove_hidepp() =
    ignore (Parse.temp_remove_user_printer "hide-printer")

fun mk_hide s t = list_mk_comb(hidec, [mk_var(s,bool), t])
fun MK_HIDE s th =
    EQ_MP (SYM (SPECL [mk_var(s,bool), concl th] hide_def)) th
val UNHIDE = CONV_RULE (REWR_CONV hide_def)

fun hide_tac s th (asl,w) =
    ([(asl @ [mk_hide s (concl th)], w)],
     fn ths => PROVE_HYP (MK_HIDE s th) (hd ths))

fun dest_hide t =
    let val (f,xs) = strip_comb t
        val _ = same_const f hidec andalso length xs = 2 orelse
                raise mk_HOL_ERR "hide" "dest_hide" "Not a hide term"
        val (s,_) = dest_var (hd xs)
                    handle HOL_ERR _ => raise mk_HOL_ERR "hide"
                                              "dest_hide"
                                              "First argument not a variable"
    in
      (s,hd (tl xs))
    end

val is_hide = can dest_hide

fun unignoring_hide f x = unignoringc hidec f x

fun unhide_tac s =
    let fun do1 th =
            case total dest_hide (concl th) of
                NONE => th
              | SOME (s',_) => if s' = s then CONV_RULE (REWR_CONV hide_def) th
                               else th
    in
      unignoring_hide (RULE_ASSUM_TAC do1)
    end

fun hide_assum s ttac =
    first_x_assum (fn th => ttac th THEN hide_tac s th)

fun unhide_assum0 extractor k s ttac =
    let
      fun find th0 =
          case total dest_hide (concl th0) of
              NONE => NO_TAC
            | SOME (s', _) => if s = s' then
                                let val th = UNHIDE th0
                                in
                                  ttac th THEN k th
                                end
                              else NO_TAC
    in
      extractor find
    end

val unhide_assum = unhide_assum0 first_x_assum assume_tac
val unhide_x_assum = unhide_assum0 first_x_assum (K all_tac)
val use_hidden_assum = unhide_assum0 first_assum (K all_tac)

val NoAsms = EQT_ELIM markerTheory.NoAsms
val NoAsms_t = concl NoAsms

fun q2str [] = ""
  | q2str (QUOTE s :: rest) = s ^ q2str rest
  | q2str (ANTIQUOTE t :: rest) =
        raise ERR "IgnAsm"
              "Pattern quotation must not include antiquotes"
val IgnAsm_t = mk_thy_const {Thy = "marker", Name = "IgnAsm",
                             Ty = alpha --> bool}
fun IgnAsm qpat =
    let val s = q2str qpat
        val s_t = mk_var(s, alpha)
    in
      EQT_ELIM (SPEC s_t IgnAsm_def)
    end

fun print_ignasm (tyg,tmg) backend printer ppfns (pgr,lgr,rgr) depth tm =
    let
      open term_pp_types smpp
      val (f, x) = dest_comb tm
      val {add_string, ...} = ppfns:ppstream_funs
      val _ = same_const IgnAsm_t f andalso is_var x andalso type_of x = alpha
              orelse raise UserPP_Failed
    in
      add_string ("IgnAsm" ^ UnicodeChars.lsquo ^ #1 (dest_var x) ^
                  UnicodeChars.rsquo)
    end

val _ = Parse.temp_add_user_printer("markerLib.IgnAsm",
                                    mk_comb(IgnAsm_t, mk_var("x", alpha)),
                                    print_ignasm)

val abbrev_vartype = mk_vartype "'abbrev"
datatype tacoptions = TO_NoAsms | TO_IgnAsm of string |
                      TO_Abbr of string | TO_Label of string |
                      TO_thm of thm
datatype aslP = AP_NoAsms | AP_Ign of string

fun dest_tacmarked th =
    let val c = concl th
        val (f, args) = strip_comb c
    in
      (* asm control *)
      if same_const c NoAsms_t then TO_NoAsms
      else if same_const f IgnAsm_t then TO_IgnAsm (#1 (dest_var (hd args)))
      else if same_const equality f then
        let val arg1 = hd args
            val arg1ty = type_of (hd args)
        in
          if arg1ty = abbrev_vartype then
            TO_Abbr (#1 (dest_var arg1))
          else
            TO_Label (dest_label_ref th)
        end
      else TO_thm th
    end handle HOL_ERR _ => TO_thm th

fun optcons NONE l = l
  | optcons (SOME x) xs = x::xs

fun matching_asm lnm t =
    (#1 (dest_label t) = lnm) handle HOL_ERR _ => false

fun process_tacoption to asl =
    case to of
        TO_thm th => (NONE, NONE, SOME th)
      | TO_NoAsms => (NONE, SOME AP_NoAsms, NONE)
      | TO_IgnAsm s => (NONE, SOME (AP_Ign s), NONE)
      | TO_Abbr s => (SOME (UNABBREV_TAC s), NONE, NONE)
      | TO_Label s => (NONE, NONE,
                       case List.find (matching_asm s) asl of
                           NONE => raise ERR "process_taclist"
                                         ("No assumption with label "^s)
                         | SOME t => SOME (DEST_LABEL (ASSUME t)))

fun asl_match ctxt s =
    let
      val q0 = [QUOTE s]
      val (q, comment_opt) = apsnd (Option.map Portable.remove_wspace)
                                   (HOLquotation.dest_last_comment q0)
      val pat = Parse.parse_in_context ctxt q
      val ctxt_s = HOLset.fromList Term.compare ctxt
      fun basematch t = Term.raw_match [] ctxt_s pat t ([],[])
    in
      case comment_opt of
          NONE => can basematch
        | SOME "sa" => can (find_term (can basematch))
        | SOME s => can basematch
    end

fun apply_aslPs ctxt aps asl =
    case aps of
        [] => asl
      | (AP_NoAsms :: _) => []
      | (AP_Ign s :: rest) =>
        apply_aslPs ctxt rest (List.filter (not o asl_match ctxt s) asl)

fun process_tacoptions tos asl pretacs aslPs asms =
    case tos of
        [] => {pre = EVERY (List.rev pretacs), asms = List.rev asms,
               aslPs = aslPs}
      | to::rest =>
        let val (tac_opt, aslP_opt, asm_opt) = process_tacoption to asl
        in
          process_tacoptions rest asl
                             (optcons tac_opt pretacs)
                             (optcons aslP_opt aslPs)
                             (optcons asm_opt asms)
        end

fun filter_then asms aslPs thltac (gl as (asl0,g)) =
    let
      val asl = apply_aslPs (free_varsl (g::asl0)) aslPs
                            (filter (not o is_label) asl0)
    in
      thltac (map ASSUME asl @ asms) gl
    end

fun process_taclist_then {arg} thltac (gl as (asl,g)) =
    let val tacoptions = map dest_tacmarked arg
        val {pre,asms,aslPs} = process_tacoptions tacoptions asl [] [] []
    in
      Tactical.THEN(pre, filter_then asms aslPs (mk_require_tac thltac)) gl
    end

end
