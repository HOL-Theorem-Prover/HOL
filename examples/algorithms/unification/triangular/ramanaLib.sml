structure ramanaLib =
struct

open HolKernel boolLib bossLib Parse pairLib

val ERR = mk_HOL_ERR "ramanaLib"

fun store_term_thm (s,t) =
  store_thm(s,mk_comb(inst[``:'a``|->type_of t]``K:bool-> 'a -> bool T``,t),
            SIMP_TAC std_ss [])

fun store_type_thm (s,t) =
  store_thm(s,inst[``:'a``|->t]``K T (x:'a)``,SIMP_TAC std_ss [])

fun SIMP_TERM ss thms t = (* use ASSUME to get a theorem to simplify instead? *)
  t |> SIMP_CONV ss thms |> concl |> rhs
  handle UNCHANGED => t
val simp_term = SIMP_TERM

fun TermWithCase q = let
  val a = Absyn q
  open Preterm errormonad
  val M = absyn_to_preterm a >-               (fn ptm0 =>
          typecheck_phase1 NONE ptm0 >>
          overloading_resolution ptm0 >-      (fn (ptm, b) =>
          report_ovl_ambiguity b >>
          to_term ptm))
in
  smash M Pretype.Env.empty
end

fun RWstore_thm (s,q,t) = Q.store_thm(s,q,t) before export_rewrites [s]
fun RWsave_thm (s,t) = save_thm(s,t) before export_rewrites [s]
fun RWnew_specification (s,l,t) =
    new_specification (s,l,t) before export_rewrites [s]
fun RWtDefine s q t = tDefine s q t before export_rewrites [s^"_def"]

val CONJ1_TAC = conj_asm1_tac
val conj1_tac = CONJ1_TAC
val CONJ2_TAC = conj_asm2_tac
val conj2_tac = CONJ2_TAC

fun SPEC_ALL_TAC except (g as (asl,t)) = let
val fvs = free_vars t in
(MAP_EVERY ID_SPEC_TAC
 (filter
  (not o (C tmem (map (parse_in_context fvs) except)))
  fvs))
end g
val spec_all_tac = SPEC_ALL_TAC

local open pred_setTheory in
fun SetCases_on q (asl,w) =
let val t = parse_in_context(free_varsl(w::asl)) q in
if is_var t then
 FULL_STRUCT_CASES_TAC (ISPEC t SET_CASES)
 else
  STRIP_ASSUME_TAC (ISPEC t SET_CASES)
  end (asl,w)
end

fun Define_sbag rs emptyq replaceq = let
  fun [QUOTE s1] + [QUOTE s2] = [QUOTE (s1^s2)]
  val rq = [QUOTE rs]
  val rdef = Define (rq+` = <|empty := `+emptyq+`; replace := `+replaceq+`|>`)
in
  RWstore_thm(rs^"_empty",rq+`.empty = `+emptyq, SRW_TAC [][rdef]);
  RWstore_thm(rs^"_replace",rq+`.replace = `+replaceq, SRW_TAC [][rdef]);
  rdef
end

end
