(*****************************************************************************)
(* FILE          : tautLib.sml                                               *)
(* DESCRIPTION   : Boolean tautology checking (by SAT solver proof replay)   *)
(*                                                                           *)
(* READS FILES   : Temporary files output by SAT solver. Deleted.            *)
(* WRITES FILES  : Temporary input file to solver. Deleted.                  *)
(*****************************************************************************)

structure tautLib :> tautLib =
struct

open HolKernel Parse boolLib Abbrev boolSyntax HolSatLib

val ERR = mk_HOL_ERR "tautLib"


(*---------------------------------------------------------------------------
     Set the parsers to a fixed grammar for the duration of this file.
 ---------------------------------------------------------------------------*)

(* Fix the grammar used by this file *)
structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars boolTheory.bool_grammars
end
open Parse


(*===========================================================================*)
(* Discriminator functions for T (true) and F (false)                        *)
(*===========================================================================*)

fun is_T tm = same_const tm T
fun is_F tm = same_const tm F

(*---------------------------------------------------------------------------*)
(* TAUT_CHECK_CONV : conv                                                    *)
(*                                                                           *)
(* Given a propositional term with all variables universally quantified,     *)
(* e.g. `!x1 ... xn. f[x1,...,xn]`, this conversion proves the term to be    *)
(* either true or false, i.e. it returns one of:                             *)
(*                                                                           *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = T                                      *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = F                                      *)
(*---------------------------------------------------------------------------*)

fun TAUT_CHECK_CONV tm =
  let val (vars,tm') = strip_forall tm
  in EQT_INTRO (GENL vars (SAT_PROVE tm')) end
  handle HolSatLib.SAT_cex th =>
    let val (vars,tm') = strip_forall tm
        val g = list_mk_exists(vars,mk_neg tm')
        val cxm = List.foldl (fn (v, cxm) =>
          if is_neg v then Redblackmap.insert (cxm, dest_neg v, F)
          else Redblackmap.insert (cxm, v, T))
            (Redblackmap.mkDict Term.compare)
            (strip_conj (fst (dest_imp (concl th))))
        val cex = List.map (fn v => Redblackmap.find (cxm, v)
          handle NotFound => T) vars
        val th1 = prove(g, MAP_EVERY EXISTS_TAC cex THEN REWRITE_TAC [])
        val th2 = CONV_RULE (REPEATC (LAST_EXISTS_CONV EXISTS_NOT_CONV)) th1
    in EQF_INTRO th2 end
  handle HOL_ERR _ => raise ERR "TAUT_CHECK_CONV" ""

(*---------------------------------------------------------------------------*)
(* PTAUT_CONV : conv                                                         *)
(*                                                                           *)
(* Given a propositional term with all variables universally quantified,     *)
(* e.g. `!x1 ... xn. f[x1,...,xn]`, this conversion proves the term to be    *)
(* either true or false, i.e. it returns one of:                             *)
(*                                                                           *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = T                                      *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = F                                      *)
(*                                                                           *)
(* It accepts propositional terms that are not fully universally quantified. *)
(* However, for such a term, the conversion will fail if it is not true.     *)
(* Consider the term `!x2 ... xn. f[x1,...,xn]`. TAUT_CHECK_CONV proves      *)
(* one of:                                                                   *)
(*                                                                           *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = T                                      *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = F                                      *)
(*                                                                           *)
(* The former can be manipulated as follows:                                 *)
(*                                                                           *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = T                                      *)
(*    |- !x1 ... xn. f[x1,...,xn]                                            *)
(*    |- !x2 ... xn. f[x1,...,xn]                                            *)
(*    |- (!x2 ... xn. f[x1,...,xn]) = T                                      *)
(*                                                                           *)
(* However when the fully quantified term is false, we have:                 *)
(*                                                                           *)
(*    |- (!x1 ... xn. f[x1,...,xn]) = F                                      *)
(*    |- ~(!x1 ... xn. f[x1,...,xn])                                         *)
(*    |- ?x1. ~(!x2 ... xn. f[x1,...,xn])                                    *)
(*    |- ?x1. ((!x2 ... xn. f[x1,...,xn]) = F)                               *)
(*                                                                           *)
(* whereas we want:                                                          *)
(*                                                                           *)
(*    |- !x1. ((!x2 ... xn. f[x1,...,xn]) = F)                               *)
(*                                                                           *)
(* i.e.,                                                                     *)
(*                                                                           *)
(*    |- (!x2 ... xn. f[x1,...,xn]) = F                                      *)
(*                                                                           *)
(* The conversions given here are not capable of proving the latter theorem  *)
(* since it is not purely propositional.                                     *)
(*---------------------------------------------------------------------------*)

fun PTAUT_CONV tm =
 let val vars = free_vars tm
     val th = TAUT_CHECK_CONV (list_mk_forall (vars,tm))
 in if null vars then th else
    if is_F (rhs (concl th))
    then raise ERR "PTAUT_CONV" "false for at least one interpretation"
    else (EQT_INTRO o (SPECL vars) o EQT_ELIM) th
 end

(*---------------------------------------------------------------------------*)
(* PTAUT_TAC : tactic                                                        *)
(*                                                                           *)
(* Tactic for solving propositional terms.                                   *)
(*---------------------------------------------------------------------------*)

val PTAUT_TAC = CONV_TAC PTAUT_CONV

(*---------------------------------------------------------------------------*)
(* PTAUT_PROVE : term -> thm                                                 *)
(*                                                                           *)
(* Given a propositional term `t`, this function returns the theorem |- t if *)
(* `t` is a tautology. Otherwise it fails.                                   *)
(*---------------------------------------------------------------------------*)

fun PTAUT_PROVE tm =
   EQT_ELIM (PTAUT_CONV tm)
   handle e => raise (wrap_exn "tautLib" "PTAUT_PROVE" e)

(*===========================================================================*)
(* Tautology checking including instances of propositional tautologies       *)
(*===========================================================================*)

(* ----------------------------------------------------------------------
    non_prop_terms : term -> term set

    Computes a set of subterms of a term that are either variables or
    Boolean valued non-propositional terms.
   ---------------------------------------------------------------------- *)
local
open Rsyntax
in
fun non_prop_terms tm = let
  fun non_prop_args acc tmlist =
      case tmlist of
        [] => acc
      | tm::ts => let
          val (opp,args) = ((#Name o dest_const) ## I) (strip_comb tm)
                           handle HOL_ERR _ => ("", [])
        in
          if mem opp ["T","F","~","/\\","\\/","==>"] then
            non_prop_args acc (args @ ts)
          else if mem opp ["=","COND"] andalso
                  all (fn t => type_of t = bool) args
          then
            non_prop_args acc (args @ ts)
          else if type_of tm = bool then
            non_prop_args (HOLset.add(acc, tm)) ts
          else raise ERR "non_prop_terms" "Not a boolean term"
        end
in
  non_prop_args empty_tmset [tm]
end
end

(*---------------------------------------------------------------------------*)
(* TAUT_CONV : conv                                                          *)
(*                                                                           *)
(* Given a term, `t`, that is a valid propositional formula or valid instance*)
(* of a propositional formula, this conversion returns the theorem |- t = T. *)
(* The variables in `t` do not have to be universally quantified.            *)
(*                                                                           *)
(* Example:                                                                  *)
(*                                                                           *)
(*    TAUT_CONV `!x n y z. x \/ ~(n < 0) \/ y \/ z \/ (n < 0)`  --->         *)
(*    |- (!x n y z. x \/ ~n < 0 \/ y \/ z \/ n < 0) = T                      *)
(*---------------------------------------------------------------------------*)

fun TAUT_CONV tm =
  let val (univs,tm') = strip_forall tm
      val insts = HOLset.listItems (non_prop_terms tm')
      val vars = map (fn t => genvar bool) insts
      val theta = map2 (curry (op |->)) insts vars
      val tm'' = list_mk_forall (vars,subst theta tm')
  in EQT_INTRO (GENL univs (SPECL insts (PTAUT_PROVE tm'')))
  end
  handle e => raise (wrap_exn "tautLib" "TAUT_CONV" e)

(*---------------------------------------------------------------------------*)
(* TAUT_TAC : tactic                                                         *)
(*                                                                           *)
(* Tactic for solving propositional formulae and instances of propositional  *)
(* formulae.                                                                 *)
(*---------------------------------------------------------------------------*)

val TAUT_TAC = CONV_TAC TAUT_CONV

(*---------------------------------------------------------------------------*)
(* ASM_TAUT_TAC : tactic                                                     *)
(*                                                                           *)
(* Same as TAUT_TAC, except that it takes the assumptions of the goal into   *)
(* account.                                                                  *)
(*---------------------------------------------------------------------------*)

val ASM_TAUT_TAC = REPEAT (POP_ASSUM MP_TAC) THEN TAUT_TAC

(*---------------------------------------------------------------------------*)
(* TAUT_PROVE : term -> thm                                                  *)
(*                                                                           *)
(* Given a valid propositional formula, or a valid instance of a             *)
(* propositional formula, `t`, this function returns the theorem |- t.       *)
(*---------------------------------------------------------------------------*)

fun TAUT_PROVE tm =
 EQT_ELIM (TAUT_CONV tm) handle HOL_ERR _ => raise ERR "TAUT_PROVE" ""

fun TAUT q = TAUT_PROVE (Term q)

end (* tautLib *)
