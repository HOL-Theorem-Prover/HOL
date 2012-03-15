open HolKernel MiniMLTheory recfunsTheory lcsymtacs
open normal_orderTheory churchnumTheory

val _ = new_theory "mlrecfun"

val rw = srw_tac []
fun fs ls = full_simp_tac (srw_ss()) ls

(*
val bnf_of_app = store_thm(
"bnf_of_app",
``∀t1 t2. bnf_of (t1 @@ t2) =
          OPTION_BIND (bnf_of t1)
          (λt1. OPTION_BIND (bnf_of t2)
                (λt2. SOME (t1 @@ t2)))``,

val lam2ml = store_thm(
"lam2ml",
``∀t. ∃cenv env exp.
      case OPTION_MAP force_num (bnf_of t) of
      | NONE => (∃err. evaluate cenv env exp (Rerr err)) ∨ e_diverges cenv env exp
      | SOME x => evaluate cenv env exp (Rval (Lit (IntLit &x)))``,
ho_match_mp_tac termTheory.simple_induction >>
conj_tac >- (
  rw[] >>
  map_every qexists_tac [`ARB`,`[]`,`Val (Lit (IntLit 0))`] >>
  rw[Once bnf_of_thm,force_num_def,is_church_def] >>
  rw[Once evaluate_cases] ) >>
conj_tac >- (
  rw[] >>
  bnf_of_thm
  DB.match [] ``bnf_of (a @@ b)``
  bnf_of_thm
  DB.find"noreduct"
  noreduct_thm

conj_tac >- (
  rw[] >>
  rw[Once bnf_of_thm,force_num_def,is_church_def,noreduct_def,normorder_rwts]
  DB.match [] ``$-n->``

val recfun2ml = store_thm(
"recfun2ml",
``∀M. ∃cenv env exp cl. evaluate cenv env exp (Rval cl) ∧
  ∀n. ∃env exp. (do_app ARB Opapp cl (Lit (IntLit &n)) = SOME (env,exp)) ∧
      case Phi M n of
      | NONE => (∃err. evaluate cenv env exp (Rerr err)) ∨ e_diverges cenv env exp
      | SOME x => evaluate cenv env exp (Rval (Lit (IntLit &x)))``,
gen_tac >>
qho_match_abbrev_tac `P M` >>
qsuff_tac `!t. P (dBnum (fromTerm t))` >- (
  disch_then (qspec_then `toTerm (numdB M)` mp_tac) >>
  rw[] ) >>
ho_match_mp_tac termTheory.simple_induction >>
conj_tac >- (
  rw [Abbr`P`] >>
  map_every qexists_tac [`ARB`,`[]`,`Fun ARB (Val (Lit (IntLit 0)))`] >>
  rw[Once evaluate_cases,do_app_def] >>
  rw[Once evaluate_cases] >>
  rw[Phi_def] >>
  rw[Once bnf_of_thm] >>
  rw[force_num_def,is_church_def] >>
  rw[Once evaluate_cases] ) >>
reverse conj_tac >- (
  rw[Abbr`P`,Phi_def] >>
  rw[Once bnf_of_thm,noreduct_def]
  DB.match [] ``bnf_of (a @@ b)``
*)

val _ = export_theory ()
