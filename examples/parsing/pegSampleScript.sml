open HolKernel Parse boolLib bossLib

open pegexecTheory

val _ = new_theory "pegSample"

val _ = Hol_datatype`tok = Plus | Times | Number of num | LParen | RParen`

local open stringTheory in end

val _ = Hol_datatype `
  expr = XN of num
       | XPlus of expr => expr
       | XTimes of expr => expr
       | XList of expr list`;

val ty = ty_antiq ``:(tok, string, expr) pegsym``
val lift_number_def = Define`
  lift_number (Number n) = XN n
`;

val nrule = ``tok (λt. case t of Number n => T | _ => F) lift_number : ^ty``
val paren_rule =
  ``seq (tok ((=) LParen) (K (XN 0)))
        (seq (nt (INL "expr") I) (tok ((=) RParen) (K (XN 0))) K)
        (K I) : ^ty``

val termpair =
  ``(INL "term" : string inf,
     choice ^nrule ^paren_rule (\s. case s of INL e => e | INR e => e))``

val leftassoc_def = Define`
  leftassoc f (XList []) b = b ∧
  leftassoc f (XList (h::t)) b = FOLDL f h (t ++ [b])
`;

val factorpair = ``(INL "factor" : string inf,
                    seq (rpt (seq (nt (INL "term") I)
                                  (tok ((=) Times) (K ARB))
                                  K)
                             XList)
                        (nt (INL "term") I)
                        (leftassoc XTimes) : ^ty)``

val exprpair = ``(INL "expr" : string inf,
                  seq (rpt (seq (nt (INL "factor") I)
                                (tok ((=) Plus) (K ARB))
                                K)
                           XList)
                      (nt (INL "factor") I)
                      (leftassoc XPlus): ^ty)``

val rules = ``FEMPTY |+ ^exprpair |+ ^factorpair |+ ^termpair``

val G = ``<| start := nt (INL "expr") I; rules := ^rules |>``

val testexp = ``[Number 3; Plus; Number 4; Times; Number 5]``

open lcsymtacs
val _ = let
  open computeLib
in
  set_skip the_compset ``evalcase_CASE`` (SOME 1);
  set_skip the_compset ``option_CASE`` (SOME 1);
  set_skip the_compset ``COND`` (SOME 1)
end

(* with eval_def directly: 1.155s;
   with "optimised" tail-recursive form: 0.213s *)
val result1 = save_thm(
  "result1",
  time EVAL ``peg_exec ^G (nt (INL "expr") I)
                      [Number 1; Plus; Number 2; Times; Number 4] []
                      done failed``)

(* As of 5a18cdc17ff, takes 1.983s (ugh) *)
val result2 = save_thm(
  "result2",
  time EVAL ``peg_exec ^G (nt (INL "expr") I)
                      [Number 1; Plus; Number 2; Times; Number 4;
                       Times; LParen; Number 3; Plus; Number 1; RParen]
                      [] done failed``)

val G_def = zDefine`G = <| start := nt (INL "expr") I; rules := ^rules |>`

val Grules = store_thm(
  "Grules",
  ``G.rules ' (INL "expr") = ^(#2 (pairSyntax.dest_pair exprpair)) ∧
    G.rules ' (INL "factor") = ^(#2 (pairSyntax.dest_pair factorpair)) ∧
    G.rules ' (INL "term") = ^(#2 (pairSyntax.dest_pair termpair)) ∧
    INL "expr" ∈ FDOM G.rules ∧
    INL "term" ∈ FDOM G.rules ∧
    INL "factor" ∈ FDOM G.rules``,
  simp[G_def, finite_mapTheory.FAPPLY_FUPDATE_THM]);
val _ = computeLib.add_persistent_funs ["Grules"]

(* on a machine running PolyML 5.4.1, and where result2 takes 0.084s,
   the following takes 0.028s

   One further optimisation would be partially evaluate the actual
   nt values against exec theorem and put the result into the compset
*)
val result2' = save_thm(
  "result2'",
  time EVAL ``peg_exec G (nt (INL "expr") I)
                      [Number 1; Plus; Number 2; Times; Number 4;
                       Times; LParen; Number 3; Plus; Number 1; RParen]
                      [] done failed``)


val _ = export_theory()
