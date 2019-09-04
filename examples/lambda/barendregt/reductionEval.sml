structure reductionEval :> reductionEval =
struct

open HolKernel Parse boolLib simpLib Traverse BasicProvers
open chap3Theory normal_orderTheory termSyntax

structure Parse = struct
val (Type,Term) = parse_from_grammars normal_orderTheory.normal_order_grammars
end

fun ERR f msg = mk_HOL_ERR "reductionEval" f msg
val betastar_t = ``(-b->*)``
val normorderstar_t = ``(-n->*)``
val beta_t = ``(-b->)``
val normorder_t = ``(-n->)``
val lameq_t = ``(==) : term -> term -> bool``

fun rtc_po t = let
  open relationTheory Travrules
  infix |> fun x |> f = f x
  fun rwt th = th |> REWRITE_RULE [reflexive_def, transitive_def]
                  |> ISPEC t
in
  mk_preorder (rwt transitive_RTC, rwt reflexive_RTC)
end

val [lameq_beta,lameq_refl,lameq_sym,lameq_trans,
     lameq_APPl, lameq_APPr, lameq_LAM] = CONJUNCTS chap2Theory.lameq_rules

val lameq_APPcong = chap2Theory.lameq_app_cong

val lameq_po = let
  open relationTheory Travrules
in
  mk_preorder (lameq_trans, lameq_refl)
end

fun dest_binop t = let
  val (fx,y) = dest_comb t
  val (f,x) = dest_comb fx
in
  (f,x,y)
end


val betastar_po = rtc_po beta_t
val normstar_po = rtc_po ``(-n->)``

val equality_po = let
  open Travrules
  val TRAVRULES {relations,...} = EQ_tr
in
  hd relations
end


(* ----------------------------------------------------------------------
    A reducer for beta-reduction.
   ---------------------------------------------------------------------- *)


val congs = [lameq_APPcong, SPEC_ALL lameq_LAM,
             chap2Theory.Yf_cong,
             REWRITE_RULE [GSYM AND_IMP_INTRO]
                          (last (CONJUNCTS chap2Theory.lemma2_12))]

val user_rewrites = ref (SSFRAG {dprocs = [], ac = [], rewrs = [],
                                 congs = [], filter = NONE,
                                 name = SOME "betasimps", convs = []})
fun add_rwts (ths : (string * thm) list) =
    user_rewrites :=
      simpLib.merge_ss [!user_rewrites, simpLib.rewrites (map #2 ths)]

open chap2Theory head_reductionTheory
val BETA_rsd = {refl = GEN_ALL lameq_refl, trans = lameq_trans,
                weakenings = [lameq_weaken_cong, lameq_has_bnf_cong,
                              lameq_bnf_of_cong],
                subsets = [ccbeta_lameq, betastar_lameq, whstar_lameq,
                           normorder_lameq, nstar_lameq],
                rewrs = [lameq_S, lameq_K, lameq_I, lameq_C,
                         lameq_B, lameq_beta]}

val BETA_CONG_ss =
  SSFRAG {dprocs = [], ac = [], rewrs = [], congs = congs, filter = NONE,
          name = NONE, convs = []}
val BETA_RWTS_ss = rewrites [termTheory.lemma14b,
                             normal_orderTheory.nstar_betastar_bnf,
                             betastar_lameq_bnf, lameq_refl]

val BETA_ss =
  simpLib.merge_ss [relsimp_ss BETA_rsd, BETA_CONG_ss, BETA_RWTS_ss]

fun betafy ss =
  simpLib.add_relsimp BETA_rsd ss ++ BETA_RWTS_ss ++
  !user_rewrites ++ BETA_CONG_ss
fun bsrw_ss() = betafy(srw_ss())

val {export = export_betarwt,...} =
    ThmSetData.new_exporter {
      settype = "betasimp",
      efns = {add = (fn {named_thms,...} => add_rwts named_thms),
              remove = (fn _ => ())}
    }
fun bstore_thm (trip as (n,t,tac)) = store_thm trip before export_betarwt n

(* ----------------------------------------------------------------------
    A reducer for weak head reduction.
   ---------------------------------------------------------------------- *)

fun whfy ss = let
  open relationTheory head_reductionTheory termTheory
  val congs = [wh_app_congL, whstar_substitutive]
in
  add_relsimp {refl = RTC_REFL
                        |> INST_TYPE [alpha |-> termSyntax.term_ty]
                        |> Q.INST [`R` |-> `(-w->)`]
                        |> Q.GEN `x`,
               trans = transitive_RTC
                         |> REWRITE_RULE [transitive_def]
                         |> Q.ISPEC `(-w->)`,
               weakenings = [wh_weaken_cong],
               subsets = [],
               rewrs = [MATCH_MP RTC_SINGLE
                                 (SPEC_ALL (CONJUNCT1 weak_head_rules))]} ss ++
  SSFRAG {dprocs = [], ac = [],
          rewrs = [(SOME "lemma14b", lemma14b), (SOME "bnf_whnf", bnf_whnf)],
          congs = congs, filter = NONE, name = NONE, convs = []}
end

(* ----------------------------------------------------------------------
    normorder_step

    Given a term t of type ``:term``, try to deduce a normal order reduction
    step, returning a thm looking like

      |- t -n-> t'

    raises a HOL_ERR if it can't do it.  This may mean t is in bnf.
   ---------------------------------------------------------------------- *)

open termSyntax
val [nbeta,nlam_cong,nleft,nright] = CONJUNCTS normorder_rules
val is_abs_t = mk_thy_const{Thy = "chap2", Name = "is_abs",
                            Ty = term_ty --> bool}
val bnf_t = mk_thy_const{Thy = "chap2", Name = "bnf",
                         Ty = term_ty --> bool}

fun normorder_step solver t = let
  val _ = Trace.trace (2, Trace.LZ_TEXT (fn () => "Attempting no1 on "^
                                                  term_to_string t))
in
  case total dest_APP t of
    NONE => let
      in
      case total dest_LAM t of
        NONE => raise ERR "normorder_step" "No visible reduction"
      | SOME (v,bdy) => let
          val subth = normorder_step solver bdy
        in
          MP (SPECL [v,bdy,rand(concl subth)] nlam_cong) subth
        end
    end
  | SOME(M1,M2) => let
    in
      case total dest_LAM M1 of
        NONE => let
          val isnt_ABS_th = solver (mk_neg(mk_comb(is_abs_t,M1)))
        in
          case total (normorder_step solver) M1 of
            NONE => let
              val bnf_th = solver (mk_comb(bnf_t,M1))
              val subth = normorder_step solver M2
            in
              MP (SPECL [M1,M2,rand (concl subth)] nright)
                 (LIST_CONJ [subth,bnf_th,isnt_ABS_th])
            end
          | SOME subth =>
            MP (SPECL [M1,rand(concl subth),M2] nleft)
               (CONJ subth isnt_ABS_th)
        end
      | SOME(v,body) => SPECL [v,body,M2] nbeta
    end
end



val [noredLAM, noredbeta, noredAPP, noredVAR] = CONJUNCTS noreduct_thm
val noreduct_t = mk_thy_const{Name = "noreduct", Thy = "normal_order",
                              Ty = term_ty --> optionSyntax.mk_option term_ty}
val (opmap_SOME,opmap_NONE) = CONJ_PAIR optionTheory.OPTION_MAP_DEF
val Mv_t = mk_var("M", term_ty)
val Nv_t = mk_var("N", term_ty)

fun noreduct_CONV solver t = let
  val (f,arg) = dest_comb t
  val _ = same_const noreduct_t f orelse
          raise ERR "noreduct_CONV" "Inapplicable"
  fun recurse t =
      case total dest_LAM t of
        SOME (v, body) => let
          val subth = recurse body
          val c = REWR_CONV noredLAM THENC
                  RAND_CONV (K subth) THENC
                  FIRST_CONV [REWR_CONV opmap_SOME, REWR_CONV opmap_NONE]
        in
          c (mk_comb(noreduct_t, t))
        end
      | NONE => let
        in
          case total dest_APP t of
            NONE => if is_VAR t then REWR_CONV noredVAR (mk_comb(noreduct_t, t))
                    else raise ERR "noreduct_CONV" "No good normorder reduct"
          | SOME (M1, M2) => let
            in
              case total dest_LAM M1 of
                SOME (v, body) => REWR_CONV noredbeta (mk_comb(noreduct_t, t))
              | NONE => let
                  val isnt_ABS = solver (mk_neg(mk_comb(is_abs_t, M1)))
                  val M1th = recurse M1
                  val eqn = MP (INST [Mv_t |-> M1, Nv_t |-> M2] noredAPP')
                               isnt_ABS
                  val c = REWRITE_CONV [optionTheory.option_case_def,
                                        M1th]
                  val eqn' = CONV_RULE (RAND_CONV c) eqn
                in
                  if is_comb (rand (concl M1th)) then
                    CONV_RULE (RAND_CONV BETA_CONV) eqn'
                  else let
                      val M2th = recurse M2
                    in
                      CONV_RULE
                          (RAND_CONV
                               (REWRITE_CONV [optionTheory.OPTION_MAP_DEF,
                                              M2th]))
                          eqn'
                    end
                end
            end
        end
in
  recurse arg
end

val nopath_t = prim_mk_const{Thy = "normal_order", Name = "nopath"}
fun nopath_CONV solver t = let
  val (f, x) = dest_comb t
  val _ = aconv f nopath_t orelse raise ERR "nopath_CONV" "Inapplicable"
  val subth = noreduct_CONV solver (mk_comb(noreduct_t, x))
in
  REWR_CONV nopath_def THENC
  REWRITE_CONV [subth, optionTheory.option_case_def] THENC
  TRY_CONV BETA_CONV
end t

val bnf_imp_noreduct = GEN_ALL (#2 (EQ_IMP_RULE noreduct_bnf))
val nstar_imp_memnopath = GEN_ALL (#1 (EQ_IMP_RULE normstar_nopath))
fun normstar_filter (th,c) =
    [(th,c), (EQT_INTRO (MATCH_MP bnf_imp_noreduct (EQT_ELIM th)),c)]
    handle HOL_ERR _ =>
           [(th,c), (EQT_INTRO (MATCH_MP nstar_imp_memnopath (EQT_ELIM th)),c)]
           handle HOL_ERR _ => [(th,c)]

fun mngcnv cnv solver stack t = cnv (solver stack) t
val NORMSTAR_ss = SSFRAG {
  ac = [], congs = [],
  convs = [{conv = mngcnv nopath_CONV, key = SOME([], mk_comb(nopath_t, Mv_t)),
            name = "nopath_CONV", trace = 2},
           {conv = mngcnv noreduct_CONV,
            key = SOME([], mk_comb(noreduct_t, Mv_t)),
            name = "noreduct_CONV", trace = 2}],
  filter = SOME normstar_filter, dprocs = [], name = SOME "NORMSTAR_ss",
  rewrs = [(SOME "normstar_nopath", normstar_nopath),
           (SOME "lemma14b", termTheory.lemma14b)]};

(* ----------------------------------------------------------------------
    unvarify_tac

    Turns a goal of the form  M -b->* N into one where free term variables
    in N have turned into lambda-variables (i.e., HOL terms of the form
    VAR s).  This may put N into bnf, allowing the betastar reduction
    congruence to fire.  If the resulting goal is provable, so too was
    the original because of substitutivity of beta-reduction.
   ---------------------------------------------------------------------- *)

fun goalnames (asl, w) = let
  val fvs = FVL (w::asl) empty_tmset
  fun foldthis(t,acc) = HOLset.add(acc, #1 (dest_var t))
in
  HOLset.listItems (HOLset.foldl foldthis (HOLset.empty String.compare) fvs)
end

fun unvarify_tac th (w as (asl,g)) = let
  val (f,x,y) = dest_binop g
  val y_fvs = free_vars y
  val y_fvs = filter (fn t => type_of t = term_ty) y_fvs
  val (strs, sets) =
      List.foldl binderLib.find_avoids (empty_tmset, empty_tmset) (g::asl)
  val finite_sets = List.mapPartial (total pred_setSyntax.dest_finite) asl
  fun filterthis t = not (is_var t) orelse tmem t finite_sets
  val sets = List.filter filterthis (HOLset.listItems sets)
  fun do_them (strs,sets) ys (w as (asl,g)) =
      case ys of
        [] => ALL_TAC w
      | y::rest => let
          val newname = Lexis.gen_variant Lexis.tmvar_vary
                                          (goalnames w)
                                          (#1 (dest_var y) ^ "s")
          val sets = List.filter (fn t => rand t !~ y) sets
          val new_tac = let
            open pred_setSyntax
          in
            if null sets then
              if HOLset.isEmpty strs then ALL_TAC
              else let
                  val avoid_t = mk_set (HOLset.listItems strs)
                in
                  binderLib.NEW_TAC newname avoid_t
                end
            else if HOLset.isEmpty strs then let
                val avoid_t = List.foldl mk_union (hd sets) (tl sets)
              in
                binderLib.NEW_TAC newname avoid_t
              end
            else let
                val base = mk_set (HOLset.listItems strs)
                val avoid_t = List.foldl mk_union base sets
              in
                binderLib.NEW_TAC newname avoid_t
              end
          end
          val newname_t = mk_var(newname, stringSyntax.string_ty)
          val inst1 = [y |-> mk_comb(VAR_t, newname_t)]
          val (_, M, N) = dest_binop g
          val x'_base = Term.subst inst1 M
          val y'_base = Term.subst inst1 N
          val x' = list_mk_comb(SUB_t, [y,newname_t,x'_base])
          val y' = list_mk_comb(SUB_t, [y,newname_t,y'_base])
          val g' = list_mk_comb(f, [x',y'])
        in
          new_tac THEN SUBGOAL_THEN (mk_eq(g,g')) SUBST1_TAC THENL [
            ASM_SIMP_TAC (srw_ss()) [termTheory.lemma14b],
            MATCH_MP_TAC th THEN
            do_them (HOLset.add(strs,newname_t), sets) rest
          ]
        end w
in
  do_them (strs,sets) y_fvs
end w


end
