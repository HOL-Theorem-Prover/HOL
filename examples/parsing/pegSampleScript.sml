open HolKernel Parse boolLib bossLib

open pegexecTheory

val _ = new_theory "pegSample"


val _ = overload_on("mkTok", ``mk_finite_image``)

val _ = Hol_datatype`ftok = Plus | Times | Number | LParen | RParen`

val _ = Hol_datatype`etok = EPlus | ETimes | ENumber of num | ELParen | ERParen`

val categorise_def = Define`
  categorise EPlus = mkTok Plus ∧
  categorise ETimes = mkTok Times ∧
  categorise (ENumber n) = mkTok Number ∧
  categorise ELParen = mkTok LParen ∧
  categorise ERParen = mkTok RParen
`;

local open stringTheory in end

val _ = Hol_datatype `
  expr = XN of num
       | XPlus of expr => expr
       | XTimes of expr => expr
       | XList of expr list`;

val _ = overload_on("mkTok", ``mk_finite_image``)


val ty = ty_antiq ``:(ftok, string, expr, etok) pegsym``
val lift_enumber_def = Define`
  lift_enumber (ENumber n) = XN n
`;

val nrule = ``tok (mkTok Number) lift_enumber : ^ty``
val paren_rule =
  ``seq (tok (mkTok LParen) (K (XN 0)))
        (seq (nt (INL "expr") I) (tok (mkTok RParen) (K (XN 0))) K)
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
                                  (tok (mkTok Times) (K ARB))
                                  K)
                             XList)
                        (nt (INL "term") I)
                        (leftassoc XTimes) : ^ty)``

val exprpair = ``(INL "expr" : string inf,
                  seq (rpt (seq (nt (INL "factor") I)
                                (tok (mkTok Plus) (K ARB))
                                K)
                           XList)
                      (nt (INL "factor") I)
                      (leftassoc XPlus): ^ty)``

val rules = ``FEMPTY |+ ^exprpair |+ ^factorpair |+ ^termpair``

val G = ``<| start := nt (INL "expr") I; rules := ^rules; cf := categorise |>``

val testexp = ``[ENumber 3; EPlus; ENumber 4; ETimes; ENumber 5]``

open lcsymtacs
val mkTok_inverse =
    fcpTheory.finite_image_tybij |> CONJUNCT2 |> SPEC_ALL |> EQ_IMP_RULE |> #1
                                 |> BETA_RULE
                                 |> REWRITE_RULE [ASSUME ``FINITE univ(:'a)``]
                                 |> DISCH_ALL

val univ_ftok = store_thm(
  "univ_ftok",
  ``univ(:ftok) = {LParen; RParen; Number; Plus; Times}``,
  simp[pred_setTheory.EXTENSION] >> Cases >> simp[]);

val mkTok_11 = store_thm(
  "mkTok_11",
  ``mkTok (x:ftok) = mkTok (y:ftok) ⇔ x = y``,
  simp[EQ_IMP_THM] >>
  disch_then (MP_TAC o AP_TERM ``dest_finite_image : ftok tok -> ftok``) >>
  simp[univ_ftok, mkTok_inverse]);

val _ = let
  open computeLib
in
  add_persistent_funs ["mkTok_11"];
  set_skip the_compset ``evalcase_CASE`` (SOME 1);
  set_skip the_compset ``option_CASE`` (SOME 1);
  set_skip the_compset ``COND`` (SOME 1)
end

(* with eval_def directly: 1.155s;
   with "optimised" tail-recursive form: 0.213s *)
val result1 = save_thm(
  "result1",
  time EVAL ``eval ^G (nt (INL "expr") I)
                      [ENumber 1; EPlus; ENumber 2; ETimes; ENumber 4]
                      [] done failed``)

(* As of 5a18cdc17ff, takes 1.983s (ugh) *)
val result2 = save_thm(
  "result2",
  time EVAL ``eval ^G (nt (INL "expr") I)
                      [ENumber 1; EPlus; ENumber 2; ETimes; ENumber 4;
                       ETimes; ELParen; ENumber 3; EPlus; ENumber 1; ERParen]
                      [] done failed``)


val _ = export_theory()
