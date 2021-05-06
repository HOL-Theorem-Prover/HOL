open HolKernel Parse boolLib bossLib

open pegexecTheory

val _ = new_theory "pegSample"

Datatype:
  tok = Plus | Times | Number num | LParen | RParen
End

local open stringTheory in end

Datatype:
  expr = XN num
       | XPlus expr expr
       | XTimes expr expr
       | XList (expr list)
End

Type ty = “:(tok, string, expr, string) pegsym”
Definition lift_number_def:
  lift_number (Number n, _) = XN n
End

val nrule = “tok (λt. case t of Number n => T | _ => F) lift_number : ty”
val paren_rule =
  “seq (tok ((=) LParen) (K (XN 0)))
        (seq (nt (INL "expr") I) (tok ((=) RParen) (K (XN 0))) K)
        (K I) : ty”

val termpair =
  “(INL "term" : string inf,
     choice ^nrule ^paren_rule (\s. case s of INL e => e | INR e => e))”

Definition leftassoc_def:
  leftassoc f (XList []) b = b ∧
  leftassoc f (XList (h::t)) b = FOLDL f h (t ++ [b])
End

val factorpair = “(INL "factor" : string inf,
                    seq (rpt (seq (nt (INL "term") I)
                                  (tok ((=) Times) (K ARB))
                                  K)
                             XList)
                        (nt (INL "term") I)
                        (leftassoc XTimes) : ty)”

val exprpair = “(INL "expr" : string inf,
                  seq (rpt (seq (nt (INL "factor") I)
                                (tok ((=) Plus) (K ARB))
                                K)
                           XList)
                      (nt (INL "factor") I)
                      (leftassoc XPlus): ty)”

val rules = “FEMPTY |+ ^exprpair |+ ^factorpair |+ ^termpair”

Definition samplePEG_def[nocompute]:
 samplePEG = <| start := nt (INL "expr") I; rules := ^rules;
                anyEOF := "Unexpected EOF (any)";
                tokFALSE := "Failed to see expected token";
                tokEOF := "Failed to see expected token because of EOF";
                notFAIL := "Failed to fail in a not rule";
             |>
End

val testexp = “[Number 3; Plus; Number 4; Times; Number 5]”

val _ = let
  open computeLib
in
  set_skip the_compset “evalcase_CASE” (SOME 1);
  set_skip the_compset “option_CASE” (SOME 1);
  set_skip the_compset “COND” (SOME 1)
end

Theorem pegexec_nt0 =
  peg_nt_thm |> Q.GENL [‘G’, ‘n’] |> Q.ISPEC ‘samplePEG’

Theorem FDOM_samplePEGrules =
  SIMP_CONV (srw_ss()) [samplePEG_def] “FDOM samplePEG.rules”

fun mk_rule_applied q =
  finite_mapSyntax.mk_fapply(
    “samplePEG.rules”,
    typed_parse_in_context “:string +num” [] q
  ) |> SIMP_CONV (srw_ss()) [samplePEG_def, finite_mapTheory.FAPPLY_FUPDATE_THM]

val nts = [‘INL "expr"’, ‘INL "factor"’, ‘INL "term"’]
Theorem sample_rules = LIST_CONJ (map mk_rule_applied nts)

fun mk_nt q =
  pegexec_nt0
   |> Q.SPEC q
   |> SIMP_RULE (srw_ss()) [FDOM_samplePEGrules, sample_rules]

Theorem sample_nts[compute] = LIST_CONJ (map mk_nt nts)

(* with "optimised" tail-recursive form: 0.005s *)
Theorem result1 =
  time EVAL “peg_exec samplePEG (nt (INL "expr") I)
                      (map_loc [Number 1; Plus; Number 2; Times; Number 4] 0)
                      [] NONE []
                      done failed”

(* As of 879f4f4, takes 0.026s *)
Theorem result2 =
  time EVAL “peg_exec samplePEG (nt (INL "expr") I)
                      (map_loc [Number 1; Plus; Number 2; Times; Number 4;
                       Times; LParen; Number 3; Plus; Number 1; RParen] 0)
                      [] NONE [] done failed”

val _ = export_theory()
