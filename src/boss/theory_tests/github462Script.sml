open HolKernel Parse boolLib bossLib;

val _ = new_theory "github462";

val _ = Datatype ‘exp = Lit num | Log exp exp’;

val _ = Datatype ‘exp_or_val = Exp exp | Val num’;

val do_log_def = Define ‘do_log v e = ARB’;

val eval_defn =
Defn.Hol_defn
 "eval"
 ‘(eval st [Log e1 e2] =
    case eval st [e1] of
        (st', SOME v1) => (case do_log (HD v1) e2 of
                               SOME (Exp e) => eval st' [e]
                             | SOME (Val v) => (st', SOME [v])
                             | NONE => (st', NONE))
      | res => res) /\
  (eval st other = ARB)’;

val _ = Defn.save_defn eval_defn

fun test t =
  not (can (find_term (same_const boolSyntax.select)) t)

val _ = assert (List.all test o DefnBase.all_terms) eval_defn

val _ = export_theory();
