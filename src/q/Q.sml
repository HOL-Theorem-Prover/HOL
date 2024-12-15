(*---------------------------------------------------------------------------
 * A bunch of functions that fold quotation parsing in, sometimes to good
 * effect.
 *---------------------------------------------------------------------------*)
structure Q :> Q =
struct

open HolKernel boolLib;

type tmquote = term quotation
type tyquote = hol_type quotation

val ERR = mk_HOL_ERR "Q";

val ptm = Parse.Term
val pty = Parse.Type;
val ty_antiq = Parse.ty_antiq;

fun normalise_quotation frags =
  case frags of
    [] => []
  | [x] => [x]
  | (QUOTE s1::QUOTE s2::rest) => normalise_quotation (QUOTE (s1^s2) :: rest)
  | x::xs => x :: normalise_quotation xs

fun contextTerm ctxt q = Parse.parse_in_context ctxt (normalise_quotation q);

fun ptm_with_ctxtty ctxt ty q = Parse.typed_parse_in_context ty ctxt q

fun TC_OFF f x = trace ("show_typecheck_errors", 0) f x
fun ptm_with_ctxtty' ctxt ty = TC_OFF (ptm_with_ctxtty ctxt ty)


fun ptm_with_ty q ty = ptm_with_ctxtty [] ty q;
fun btm q = ptm_with_ty q Type.bool

fun mk_term_rsubst ctxt = let
  (* rely on the fact that the ctxt will be the free variables of the term/thm
     that is going to be worked over by the subst *)
  fun f {redex,residue} = let
    val redex' = contextTerm ctxt redex
  in
    if op_mem aconv redex' ctxt then let
        val residue' = ptm_with_ctxtty ctxt (type_of redex') residue
      in
        SOME (redex' |-> residue')
      end
    else NONE

  end
in
  List.mapPartial f
end

val mk_type_rsubst = map (fn {redex,residue} => (pty redex |-> pty residue));

fun store_thm(s,q,t) = boolLib.store_thm(s,btm q,t);
fun store_thm_at loc (s,q,t) = boolLib.store_thm_at loc (s,btm q,t);
fun prove (q, t) = Tactical.prove(btm q,t);
fun new_definition_at l (s,q) = boolLib.new_definition_at l (s,btm q);
val new_definition = new_definition_at DB.Unknown
fun new_infixl_definition(s,q,f) = boolLib.new_infixl_definition(s,btm q,f);
fun new_infixr_definition(s,q,f) = boolLib.new_infixr_definition(s,btm q,f);

val ABS       = Thm.ABS o ptm;
val BETA_CONV = Thm.BETA_CONV o ptm;
val REFL      = Thm.REFL o ptm;

fun DISJ1 th = Thm.DISJ1 th o btm;
val DISJ2    = Thm.DISJ2 o btm;

fun GEN [QUOTE s] th =
     let val V = free_vars (concl th)
     in case Lib.assoc2 (Lib.deinitcomment s)
                (Lib.zip V (map (fst o Term.dest_var) V))
         of NONE => raise ERR "GEN" "variable not found"
         | SOME (v,_) => Thm.GEN v th
     end
  | GEN _ _ = raise ERR "GEN" "unexpected quote format"

fun GENL qs th = List.foldr (fn (q,th) => GEN q th) th qs

fun SPEC q =
 W(Thm.SPEC o ptm_with_ty q o (type_of o fst o dest_forall o concl));

val SPECL = rev_itlist SPEC;
val ISPEC = Drule.ISPEC o ptm;
val ISPECL = Drule.ISPECL o map ptm;
val ID_SPEC = W(Thm.SPEC o (fst o dest_forall o concl))

fun em_getState s = errormonad.Some((s,s))
fun sm_getState s = seq.result(s,s)

fun SPEC_THEN q ttac thm (g as (asl,w)) = let
  infix >>- >>~
  fun em >>- f = let open errormonad in em >- f end
  fun sm >>~ f = let open seqmonad in sm >- f end
  val a = Parse.Absyn q
  val ctxt = HOLset.listItems (hyp_frees thm) @ free_varsl(w::asl)
  val (Bvar,_) = dest_forall (concl thm)
  val bty = type_of Bvar
  val pbty0 = Pretype.fromType bty
  val fixed_tyvars = hyp_tyvars thm |> HOLset.listItems
  val pbty = Pretype.rename_typevars (List.map dest_vartype fixed_tyvars) pbty0
  val fixup_map0 =
      let open errormonad
      in
        pbty >>- (fn pty =>
        Pretype.unify pbty0 pty >>
        em_getState >>- (return o Pretype.Env.toList))
      end Pretype.Env.empty
  val fixup_map =
      case fixup_map0 of
          errormonad.Some(_, alist) =>
            List.map (fn (i,v) => (Pretype.toType (valOf v) |-> i)) alist
        | _ => raise Fail "SPEC_THEN invariant failure"
  fun parse_with_unify_check a =
      let
          val ptmm = TermParse.absyn_to_preterm (Parse.term_grammar()) a
          open Preterm seqmonad
          val printers = SOME (term_to_string, type_to_string)
      in
        fromErr pbty >>~ (fn pty =>
        fromErr ptmm >>~ (fn ptm =>
        fromErr
          (TermParse.ctxt_preterm_to_term printers NONE ctxt
                (Constrained{Locn = locn.Loc_None,Ptm = ptm, Ty = pty}))))
      end
  fun Ecompose theta0 E =
      List.mapPartial
        (fn {redex,residue} =>
            case Pretype.toTypeM (Pretype.UVar residue) E of
                errormonad.Some(_, ty) => SOME{redex=redex, residue = ty}
              | _ => NONE)
        theta0
  fun inst_spec_n_ttac t =
      let
        open seqmonad
      in
        sm_getState >>~ (fn env =>
        let val theta = Ecompose fixup_map env
        in
          case Lib.total ttac (Thm.SPEC t (INST_TYPE theta thm)) of
              NONE => fail
            | SOME tac => (case Lib.total tac g of
                              NONE => fail
                            | SOME result => return result)
        end)
      end
  val sm = parse_with_unify_check a >>~ inst_spec_n_ttac
in
  case seq.cases (sm Pretype.Env.empty) of
      NONE => raise ERR "SPEC_THEN" "No parse succeeds"
    | SOME ((_, res),_) => res
end

val SPEC_THEN : term quotation -> thm_tactic -> thm_tactic = SPEC_THEN;

fun SPECL_THEN ql =
  case ql of
      [] => ALL_THEN
    | q::qs => SPEC_THEN q THEN_TCL SPECL_THEN qs

fun ISPEC_THEN q ttac thm g = Q_TAC (fn t => ttac (Drule.ISPEC t thm)) q g

fun goal_ctxt (asl,w) = free_varsl (w::asl)

fun seq_mmap mf list =
  case list of
      [] => seq.result []
    | x::xs => seq.bind (mf x)
                        (fn x' =>
                            seq.bind (seq_mmap mf xs)
                                     (fn xs' => seq.result (x'::xs')))

fun ISPECL_THEN ql ttac thm g =
  let
    open Parse TermParse
    val ctxt = goal_ctxt g
    fun tf q = prim_ctxt_termS Absyn (term_grammar()) ctxt q
    val tl_s = seq_mmap tf ql
  in
    case seq.cases tl_s of
        NONE => raise ERR "ISPECL_THEN" "No parse for quotation list"
      | SOME _ =>
        let
          fun f tl = SOME (ttac (Drule.ISPECL tl thm) g)
                     handle HOL_ERR _ => NONE
        in
          case seq.cases (seq.mapPartial f tl_s) of
              NONE => raise ERR "ISPECL_THEN" "No parse leads to success"
            | SOME (res, _) => res
        end
  end

fun SPEC_TAC (q1,q2) (g as (asl,w)) = let
  val ctxt = free_varsl (w::asl)
  val T1 = Parse.parse_in_context ctxt q1
  val T2 = ptm_with_ctxtty' ctxt (type_of T1) q2
in
  Tactic.SPEC_TAC(T1, T2) g
end;

(* Generalizes first free variable with given name to itself. *)

fun ID_SPEC_TAC q (g as (asl,w)) =
 let val ctxt = free_varsl (w::asl)
     val tm = Parse.parse_in_context ctxt q
 in
   Tactic.SPEC_TAC (tm, tm) g
 end

fun EXISTS(q1,q2) thm =
 let val tm1 = btm q1
     val exvartype = type_of (fst (dest_exists tm1))
       handle HOL_ERR _ => raise ERR "EXISTS" "first quotation not an exists"
     val tm2 = ptm_with_ty q2 exvartype
 in
   Thm.EXISTS (tm1,tm2) thm
 end;

fun EXISTS_TAC q (g as (asl, w)) =
 let
   val exvartype = type_of (fst (dest_exists w))
           handle HOL_ERR _ => raise ERR "EXISTS_TAC" "goal not an exists"
 in
   QTY_TAC exvartype (fn t => Tactic.EXISTS_TAC t) q g
 end

fun LIST_EXISTS_TAC qL = EVERY (map EXISTS_TAC qL)

fun REFINE_EXISTS_TAC q (asl, w) = let
  val (qvar, body) = dest_exists w
  val ctxt = free_varsl (w::asl)
  val t = ptm_with_ctxtty' ctxt (type_of qvar) q
  val qvars = op_set_diff aconv (free_vars t) ctxt
  val newgoal = subst [qvar |-> t] body
  fun chl [] ttac = ttac
    | chl (h::t) ttac = X_CHOOSE_THEN h (chl t ttac)
in
  SUBGOAL_THEN
    (list_mk_exists(rev qvars, newgoal))
    (chl (rev qvars) (fn th => Tactic.EXISTS_TAC t THEN ACCEPT_TAC th))
    (asl, w)
end

fun LIST_REFINE_EXISTS_TAC qs (asl, g) = let
    fun strip_n_exists 0 acc tm = (rev acc, tm)
      | strip_n_exists n acc tm =
          let val (bv, tm) = dest_exists tm in strip_n_exists (n - 1) (bv::acc) tm end
    val (exists_vars, body) = strip_n_exists (length qs) [] g
      handle _ => raise ERR "LIST_REFINE_EXISTS_TAC" "too many quotations provided"
    val qs_bvs = zip qs exists_vars
    val ctxt = free_varsl (g::asl)
    fun is_underscore q =
      let val tm = trace ("notify type variable guesses", 0) ptm q in
      if not (is_var tm) then false else String.isPrefix "_" (fst (dest_var tm)) end
    fun process [] = ([], [], [], [])
      | process ((q,bv)::rest) =
        let val (wits, new_vars, renames, subs) = process rest in
        if is_underscore q then
          let val bv' = variant (map #redex subs) bv
          in (NONE::wits, new_vars, (bv |-> bv')::renames, subs) end
        else let
          val wit = ptm_with_ctxtty' (new_vars @ ctxt) (type_of bv) q
          val new_vars' = op_set_diff aconv (free_vars wit) (new_vars @ ctxt)
          in (SOME wit::wits, new_vars' @ new_vars, renames, (bv |-> wit)::subs) end
        end
    val (wits, new_vars, renames, subs) = process qs_bvs
    val g' =
      let val freshen = map (fn v => v |-> genvar (type_of v)) exists_vars
          val bvs = map (subst freshen) exists_vars
          val body = subst freshen body
      in list_mk_exists (bvs, body) end
    val (old_vars, body) =
      let val body = list_mk_exists (map #residue renames, subst renames body)
          val body = subst subs body
      in strip_n_exists (length renames) [] body end
    fun exists desired [] _ th = th
      | exists desired (SOME tm::tm_opts) bvs th =
          let val (var, body) = dest_exists desired
              val rest = exists (subst [var |-> tm] body) tm_opts bvs th
          in Thm.EXISTS (desired, tm) rest end
      | exists desired (NONE::tm_opts) (bv::bvs) th =
          let val (var, body) = dest_exists desired
              val rest = exists (subst [var |-> bv] body) tm_opts bvs th
          in Thm.EXISTS (desired, bv) rest end
      | exists _ _ _ _ = raise ERR "LIST_REFINE_EXISTS_TAC" "internal error"
    fun chooser [] th = th
      | chooser (v::vs) th =
          let val th = chooser vs th
              val exists_tm = mk_exists (v, hd (hyp th))
          in CHOOSE (v, ASSUME exists_tm) th end
    val th = ASSUME body |> exists g' wits old_vars |> chooser (new_vars @ old_vars)
  in
    MATCH_MP_TAC (DISCH_ALL th) (asl, g)
  end

fun X_CHOOSE_THEN q ttac thm (g as (asl,w)) =
 let val ty = type_of (fst (dest_exists (concl thm)))
       handle HOL_ERR _ =>
          raise ERR "X_CHOOSE_THEN" "provided thm not an exists"
 in
   QTY_TAC ty (fn t => Thm_cont.X_CHOOSE_THEN t ttac thm) q g
 end

val X_CHOOSE_TAC = C X_CHOOSE_THEN Tactic.ASSUME_TAC;

fun DISCH q th =
 let val (asl,c) = dest_thm th
     val V = free_varsl (c::asl)
     val tm = ptm_with_ctxtty V Type.bool q
 in Thm.DISCH tm th
 end;

fun PAT_UNDISCH_TAC q (g as (asl,w)) =
let val ctxt = free_varsl (w::asl)
    val pat = ptm_with_ctxtty' ctxt Type.bool q
    val asm =
        first (can (ho_match_term [] Term.empty_tmset pat)) asl
in Tactic.UNDISCH_TAC asm g
end;

fun PAT_ASSUM q ttac =
  Q_TAC0 {traces = [("notify type variable guesses", 0)]} (SOME bool)
         (fn t => Tactical.PAT_ASSUM t ttac)
         q
fun PAT_X_ASSUM q ttac =
  Q_TAC0 {traces = [("notify type variable guesses", 0)]} (SOME bool)
         (fn t => Tactical.PAT_X_ASSUM t ttac)
         q

fun SUBGOAL_THEN q ttac =
  QTY_TAC Type.bool (fn t => Tactical.SUBGOAL_THEN t ttac) q

val UNDISCH_TAC = QTY_TAC Type.bool Tactic.UNDISCH_TAC

fun UNDISCH_THEN q ttac =
  QTY_TAC Type.bool (fn t => Tactic.UNDISCH_TAC t THEN DISCH_THEN ttac) q

fun hdtm_assum q ttac = Q_TAC (C Tactical.hdtm_assum ttac) q
fun hdtm_x_assum q ttac = Q_TAC (C Tactical.hdtm_x_assum ttac) q

val ASSUME = ASSUME o btm

fun X_GEN_TAC q (g as (asl, w)) =
 let
   val ty = type_of (fst(dest_forall w))
 in
   QTY_TAC ty Tactic.X_GEN_TAC q g
 end

fun X_FUN_EQ_CONV q tm =
 let val ctxt = free_vars tm
     val ty = #1 (dom_rng (type_of (lhs tm)))
 in
   Conv.X_FUN_EQ_CONV (ptm_with_ctxtty' ctxt ty q) tm
 end

fun skolem_ty tm =
 let val (V,tm') = strip_forall tm
 in if not (null V)
    then list_mk_fun (map type_of V, type_of(fst(dest_exists tm')))
    else raise ERR"XSKOLEM_CONV" "no universal prefix"
  end;

fun X_SKOLEM_CONV q tm =
 let val ctxt = free_vars tm
     val ty = skolem_ty tm
 in
  Conv.X_SKOLEM_CONV (ptm_with_ctxtty ctxt ty q) tm
 end

fun AP_TERM q th =
 let val ctxt = free_vars(concl th)
     val tm = contextTerm ctxt q
     val (ty,_) = dom_rng (type_of tm)
     val (lhs,rhs) = dest_eq(concl th)
     val theta = match_type ty (type_of lhs)
 in
   Thm.AP_TERM (Term.inst theta tm) th
 end;

fun AP_THM th q =
 let val (lhs,rhs) = dest_eq(concl th)
     val ty = fst (dom_rng (type_of lhs))
     val ctxt = free_vars (concl th)
 in
   Thm.AP_THM th (ptm_with_ctxtty ctxt ty q)
 end;

val ASM_CASES_TAC = QTY_TAC bool Tactic.ASM_CASES_TAC

fun AC_CONV p = Conv.AC_CONV p o ptm;

(* Could be smarter *)

fun INST subst th = let
  val ctxt = thm_frees th
in
  Thm.INST (mk_term_rsubst ctxt subst) th
end
val INST_TYPE = Thm.INST_TYPE o mk_type_rsubst;


(*---------------------------------------------------------------------------*)
(*    Abbreviation tactics                                                   *)
(*---------------------------------------------------------------------------*)

fun ABBREV_TAC q (gl as (asl,w)) =
 let val ctxt = free_varsl(w::asl)
     val eq = Parse.parse_in_context ctxt q
 in
   markerLib.ABBREV_TAC eq
 end gl;

fun PAT_ABBREV_TAC q (gl as (asl,w)) =
 let val fv_set = FVL (w::asl) empty_tmset
     val ctxt = HOLset.listItems fv_set
     val eq = Parse.parse_in_context ctxt q
 in
   markerLib.PAT_ABBREV_TAC fv_set eq
 end gl;

fun MATCH_ABBREV_TAC q (gl as (asl,w)) =
 let val fv_set = FVL (w::asl) empty_tmset
     val ctxt = HOLset.listItems fv_set
     val pattern = ptm_with_ctxtty' ctxt bool q
 in
  markerLib.MATCH_ABBREV_TAC fv_set pattern
 end gl;

fun HO_MATCH_ABBREV_TAC q (gl as (asl,w)) =
 let val fv_set = FVL (w::asl) empty_tmset
     val ctxt = HOLset.listItems fv_set
     val pattern = ptm_with_ctxtty' ctxt bool q
in
  markerLib.HO_MATCH_ABBREV_TAC fv_set pattern
end gl;

fun UNABBREV_TAC q (gl as (asl,w)) =
 let val v = Parse.parse_in_context (free_varsl (w::asl)) q
 in
   markerLib.UNABBREV_TAC (fst(dest_var v))
 end gl;

fun RM_ABBREV_TAC q (gl as (asl,w)) =
 let val v = Parse.parse_in_context (free_varsl (w::asl)) q
 in
   markerLib.RM_ABBREV_TAC (fst(dest_var v))
 end gl;

fun MATCH_ASSUM_ABBREV_TAC q (gl as (asl,w)) =
 let val fv_set = FVL (w::asl) empty_tmset
     val ctxt = HOLset.listItems fv_set
     val pattern = ptm_with_ctxtty' ctxt bool q
 in
  markerLib.MATCH_ASSUM_ABBREV_TAC fv_set pattern
 end gl;

fun make_abbrev_tac s =
  MAP_EVERY markerLib.ABB' (markerLib.safe_inst_sort s)

(*---------------------------------------------------------------------------*)
(*    Renaming tactics                                                       *)
(*---------------------------------------------------------------------------*)

fun make_rename_tac s =
  MAP_EVERY
      (fn {redex=l,residue=r} =>
          CHOOSE_THEN SUBST_ALL_TAC
            (Thm.EXISTS(mk_exists(l, mk_eq(r, l)), r) (Thm.REFL r)))
      (Listsort.sort markerLib.safe_inst_cmp s)

fun isnt_uscore_var v = let
  val (s, _) = dest_var v
in
  size s <> 0 andalso String.sub(s, 0) <> #"_"
end
val strip_uscore_bindings = filter (fn {redex,residue} => isnt_uscore_var redex)
fun redex_map f {redex,residue} = {redex = f redex, residue = residue}

fun PQ (* parser quiet *) f =
  f |> trace ("notify type variable guesses", 0)
    |> trace ("show_typecheck_errors", 0)

(* needs to be eta-expanded so that the possible HOL_ERRs are raised
   when applied to a goal, not before, thereby letting FIRST_ASSUM catch
   the exception *)
fun wholeterm_rename_helper {pats,fvs_set,ERR,kont} tm g = let
  fun do_one_pat pat =
    let
      val ((tmtheta0, _), (tytheta, _)) =
          raw_match [] fvs_set pat tm ([],[])
          handle HOL_ERR _ => raise ERR "No match"
      val rename_tac =
          tmtheta0 |> strip_uscore_bindings |> map (redex_map (inst tytheta))
                   |> make_rename_tac
    in
      rename_tac THEN kont
    end g
  fun test_parses patseq =
    case PQ seq.cases patseq of
        NONE => raise ERR "No match"
      | SOME (pat, rest) => do_one_pat pat handle HOL_ERR _ => test_parses rest
in
  test_parses pats
end

val Absyn = Parse.Absyn
val term_grammar = Parse.term_grammar


fun kMATCH_RENAME_TAC q k (g as (_, t)) = let
  val ctxt = goal_ctxt g
  fun mkA q = Absyn.TYPED(locn.Loc_None, Absyn q, Pretype.fromType bool)
  val pat_parses = TermParse.prim_ctxt_termS mkA (term_grammar()) ctxt q
in
  wholeterm_rename_helper
    {pats=pat_parses, ERR = ERR "MATCH_RENAME_TAC", kont = k,
     fvs_set = HOLset.fromList Term.compare ctxt}
    t
end g

fun MATCH_RENAME_TAC q = kMATCH_RENAME_TAC q ALL_TAC

fun kMATCH_ASSUM_RENAME_TAC q k (g as (asl,t)) = let
  val ctxt = free_varsl(t::asl)
  val pats = TermParse.prim_ctxt_termS Absyn (term_grammar()) ctxt q
in
  FIRST_ASSUM (fn th =>
    wholeterm_rename_helper
      {pats=pats, ERR = ERR "MATCH_ASSUM_RENAME_TAC", kont = k,
       fvs_set = HOLset.fromList Term.compare ctxt}
      (concl th))
end g

fun MATCH_ASSUM_RENAME_TAC q = kMATCH_ASSUM_RENAME_TAC q ALL_TAC

(* needs to be eta-expanded so that the possible HOL_ERRs are raised
   when applied to a goal, not before, thereby letting FIRST_ASSUM catch
   the exception *)
fun subterm_helper strictp make_tac k {ERR,pats,fvs_set} t g = let
  fun test (pat, thetasz) (bvs, subt) =
      if strictp andalso aconv t subt then NONE
      else
        case Lib.total (fn t => raw_match [] fvs_set pat t ([],[])) subt of
            SOME ((theta0, _), (tytheta,_)) =>
            let
              fun filt {residue, ...} =
                  List.all (fn bv => not (free_in bv residue)) bvs
              val theta0 =
                  filter (fn s => isnt_uscore_var (#redex s) andalso filt s)
                         theta0
              val theta = map (redex_map (inst tytheta)) theta0
            in
              if length theta <> thetasz then NONE
              else Lib.total (make_tac theta THEN k) g
            end
          | NONE => NONE
  fun find_pats patseq =
    case PQ seq.cases patseq of
        NONE => raise ERR "No matching sub-term found"
      | SOME (patsz, rest) =>
        (case gen_find_term (test patsz) t of
             SOME tacresult => tacresult
           | NONE => find_pats rest)
in
  find_pats pats
end

fun prep_rename q nm (asl, t) = let
  val ERR = ERR nm
  val fvs = free_varsl (t::asl)
  val pats = TermParse.prim_ctxt_termS Absyn (term_grammar()) fvs q
  val fvs_set = HOLset.fromList Term.compare fvs
  fun mapthis pat = let
    val patfvs = free_vars pat
    val pat_binds =
        filter (fn v => not (op_mem aconv v fvs) andalso isnt_uscore_var v)
               patfvs
  in
    (pat, length pat_binds)
  end
in
  {ERR = ERR, pats = seq.map mapthis pats, fvs_set = fvs_set}
end

fun kMATCH_GOALSUB_RENAME_TAC b q k (g as (asl, t)) =
    subterm_helper b make_rename_tac k
                   (prep_rename q "MATCH_GOALSUB_RENAME_TAC" g) t g

fun MATCH_GOALSUB_RENAME_TAC q = kMATCH_GOALSUB_RENAME_TAC false q ALL_TAC

fun kMATCH_ASMSUB_RENAME_TAC b q k (g as (asl, t)) = let
  val args = prep_rename q "MATCH_ASMSUB_RENAME_TAC" g
in
  FIRST_ASSUM (subterm_helper b make_rename_tac k args o concl) g
end

fun MATCH_GOALSUB_ABBREV_TAC q (g as (asl, t)) =
    subterm_helper false make_abbrev_tac ALL_TAC
                   (prep_rename q "MATCH_GOALSUB_ABBREV_TAC" g) t g

fun MATCH_ASMSUB_ABBREV_TAC q (g as (asl, t)) = let
  val args = prep_rename q "MATCH_ASMSUB_ABBREV_TAC" g
in
  FIRST_ASSUM (subterm_helper false make_abbrev_tac ALL_TAC args o concl) g
end

fun MATCH_ASMSUB_RENAME_TAC q = kMATCH_ASMSUB_RENAME_TAC false q ALL_TAC

val seltypes = ["g", "a", "sg", "sa"]
fun is_seltype s = mem s seltypes
fun rename_by_type s =
    case s of
        "g" => kMATCH_RENAME_TAC
      | "a" => kMATCH_ASSUM_RENAME_TAC
      | "sg" => kMATCH_GOALSUB_RENAME_TAC true
      | "sa" => kMATCH_ASMSUB_RENAME_TAC true
      | _ => raise Fail "Q.rename_by_type: can't happen"
fun remove_wspace s =
    String.implode $
      CharVector.foldr (fn (c,A) => if Char.isSpace c then A else c::A) [] s


fun genrename1_with_opt q k =
    let val (_, sopt) = HOLquotation.dest_last_comment q
        val opts0 = case sopt of
                        NONE => seltypes
                      | SOME s => String.fields(equal #"|")(remove_wspace s)
        val opts = case List.filter is_seltype opts0 of
                       [] => (HOL_WARNING "Q" "RENAME"
                                   "No valid selection options; using all";
                              seltypes)
                     | ss => ss
        val _ = case List.find (not o is_seltype) opts0 of
                    NONE => ()
                  | SOME s => HOL_WARNING "Q" "RENAME"
                                          ("Bad selection option: \"" ^
                                           String.toString s ^ "\"")
        fun build_tac q k [] = raise Fail "coreRENAME_TAC: can't happen"
          | build_tac q k [opt] = rename_by_type opt q k
          | build_tac q k (opt::rest) =
            rename_by_type opt q k ORELSE build_tac q k rest
    in
      build_tac q k opts
    end

fun RENAME1_TAC q = genrename1_with_opt q ALL_TAC


fun coreRENAME_TAC qs k =
  let
    fun recurse qs =
      case qs of
          [] => k
        | q::rest => genrename1_with_opt q (recurse rest)
  in
    recurse qs
  end

fun flip_inst s = map (fn {redex,residue} => {redex=residue,residue=redex}) s

fun gvarify (goal as (asl,w)) =
  let
    fun gentheta (v, acc) = {residue = v, redex = genvar (type_of v)} :: acc
  in
    HOLset.foldl gentheta [] (FVL (w::asl) empty_tmset)
  end

fun kRENAME_TAC qs k g =
  let
    val gsig = gvarify g
    val gsig_inv = flip_inst gsig
  in
    make_rename_tac gsig THEN
    coreRENAME_TAC qs (make_rename_tac gsig_inv THEN k)
  end g

fun RENAME_TAC qs = kRENAME_TAC qs ALL_TAC

fun SELECT_GOAL_LT pats = FIRST_LT (RENAME_TAC pats)

fun (tac >~ pats) = tac THEN_LT SELECT_GOAL_LT pats

fun SELECT_GOALS_LT pats = SELECT_LT (RENAME_TAC pats)

fun SELECT_GOALS_LT_THEN pats tac = SELECT_LT (RENAME_TAC pats THEN tac)

fun (tac >>~ pats) = tac THEN_LT SELECT_GOALS_LT pats

fun SELECT_GOALS_LT_THEN1 pats tac =
  SELECT_LT_THEN (RENAME_TAC pats) (tac THEN NO_TAC)

fun (tac1 >>~- (pats, tac2)) = tac1 THEN_LT SELECT_GOALS_LT_THEN1 pats tac2

end (* Q *)
