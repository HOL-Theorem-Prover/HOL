open preamble MiniMLTheory

val _ = new_theory "evaluateEquations"

(* functional equations for evaluate *)

val evaluate_raise = Q.store_thm (
"evaluate_raise",
`!cenv env err bv.
  (evaluate cenv env (Raise err) bv = (bv = Rerr (Rraise err)))`,
rw [Once evaluate_cases]);

val evaluate_val = Q.store_thm(
"evaluate_val",
`!cenv env v r.
  (evaluate cenv env (Val v) r = (r = Rval v))`,
rw [Once evaluate_cases]);

val evaluate_con = Q.store_thm(
"evaluate_con",
`!cenv env cn es r.
  (evaluate cenv env (Con cn es) r =
   if do_con_check cenv cn (LENGTH es) then
     (∃err. evaluate_list cenv env es (Rerr err) ∧
            (r = Rerr err)) ∨
     (∃vs. evaluate_list cenv env es (Rval vs) ∧
           (r = Rval (Conv cn vs)))
   else (r = Rerr Rtype_error))`,
rw [Once evaluate_cases] >>
metis_tac []);

val _ = export_theory ()
