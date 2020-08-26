open HolKernel Parse boolLib bossLib;

open simpleSexpTheory pegTheory pegLib

val _ = new_theory "simpleSexpPEG";

Definition tokeq_def: tokeq t = tok ((=) t) (K (SX_SYM [t]))
End
Definition grabWS_def:
  grabWS s = rpt (tok isSpace (K arb_sexp)) (K arb_sexp) ~> s
End

Theorem peg0_tokeq[simp]: peg0 G (tokeq t) = F
Proof simp[tokeq_def]
QED

Definition pnt_def: pnt ntsym = nt (mkNT ntsym) I
End

Definition replace_nil_def:
  (replace_nil (SX_SYM s) z = if s = "nil" then z else SX_SYM s) ∧
  (replace_nil (SX_CONS x y) z = SX_CONS x (replace_nil y z)) ∧
  (replace_nil x y = x)
End

(* have to use these versions of choicel and pegf below because the
   versions from pegTheory use ARB in their definitions.
   Logically, the ARBs are harmless, but they completely mess with the
   CakeML translator.
*)
Definition choicel_def:
  choicel [] = not (empty arb_sexp) arb_sexp ∧
  choicel (h::t) = choice h (choicel t) (λs. case s of INL x => x | INR y => y)
End

Definition pegf_def:
  pegf sym f = seq sym (empty arb_sexp) (λl1 l2. f l1)
End

Theorem peg_eval_choicel_NIL[simp]:
  peg_eval G (i0, choicel []) x <=> x = Failure (sloc i0) G.notFAIL
Proof simp[choicel_def, Once peg_eval_cases]
QED

Theorem peg_eval_choicel_CONS:
  ∀x. peg_eval G (i0, choicel (h::t)) x ⇔
      peg_eval G (i0, h) x ∧ isSuccess x ∨
      ∃r1 r2.
        peg_eval G (i0,h) r1 ∧ isFailure r1 ∧ peg_eval G (i0, choicel t) r2 ∧
        x = if isFailure r2 then rmax r1 r2 else r2
Proof
  simp[choicel_def, SimpLHS, Once peg_eval_cases] >>
  simp[pairTheory.FORALL_PROD, FORALL_result, EXISTS_result,
       AllCaseEqs()] >> metis_tac[]
QED

Theorem peg0_choicel[simp]:
  (peg0 G (choicel []) = F) ∧
  (peg0 G (choicel (h::t)) ⇔ peg0 G h ∨ pegfail G h ∧ peg0 G (choicel t))
Proof simp[choicel_def]
QED

Theorem peg0_pegf[simp]:
  peg0 G (pegf s f) = peg0 G s
Proof simp[pegf_def]
QED

Definition sexpPEG_def[nocompute]:
  sexpPEG : (char, sexpNT, sexp, string) peg =
  <|
    start := pnt sxnt_sexp ;
    anyEOF := "Unexpected EOF (any)";
    tokFALSE := "Failed to see expected token";
    tokEOF := "Failed to see expected token because of EOF";
    notFAIL := "Failed to fail in a not rule";
    rules :=
    FEMPTY |++
           [(mkNT sxnt_sexp,
             pnt sxnt_WSsexp <~ rpt (tok isSpace (K arb_sexp)) (K arb_sexp));
            (mkNT sxnt_sexp0,
             choicel [
                 pnt sxnt_sexpnum ;
                 tokeq #"(" ~> pnt sxnt_sexpseq ;
                 tokeq #"\"" ~> pnt sxnt_strcontents <~ tokeq #"\"" ;
                 pegf (tokeq #"'" ~> grabWS (pnt sxnt_sexp0))
                      (λs. ⟪ SX_SYM "quote"; s⟫) ;
                 pnt sxnt_sexpsym
               ]);
            (mkNT sxnt_sexpseq,
             choicel [
                 pegf (grabWS (tokeq #")")) (K (SX_SYM "nil"));
                 seq (grabWS (pnt sxnt_sexp0))
                     (seq (rpt (grabWS (pnt sxnt_sexp0))
                           (FOLDR SX_CONS (SX_SYM "nil")))
                      (choicel [
                          pegf (grabWS (tokeq #")")) (K (SX_SYM "nil"));
                          grabWS (tokeq #".") ~>
                                 grabWS (pnt sxnt_sexp0)
                                 <~ grabWS (tokeq #")")
                        ])
                      replace_nil)
                     SX_CONS
               ]);
            (mkNT sxnt_WSsexp,
             rpt (tok isSpace (K arb_sexp)) (K arb_sexp) ~> pnt sxnt_sexp0);
            (mkNT sxnt_sexpnum,
             seq (pnt sxnt_digit)
                 (rpt (pnt sxnt_digit)
                  (UNCURRY SX_CONS o (SX_NUM ## SX_NUM) o
                   FOLDL (λ(l,n) d. (10*l, 10*n + destSXNUM d)) (1,0)))
                 (λs1. (λ(l,n). SX_NUM (destSXNUM s1 * l + n))
                       o (destSXNUM ## destSXNUM) o destSXCONS)) ;
            (mkNT sxnt_digit, tok isDigit (λ(c,l). SX_NUM (ORD c - ORD #"0"))) ;
            (mkNT sxnt_sexpsym,
             seq (tok valid_first_symchar (λ(c,l). SX_SYM [c]))
                 (rpt (tok valid_symchar (λ(c,l). SX_SYM [c]))
                  (SX_SYM o FOLDR (λs a. destSXSYM s ++ a) []))
                 (λs1 s2. SX_SYM (destSXSYM s1 ++ destSXSYM s2)));
            (mkNT sxnt_strcontents,
             rpt (pnt sxnt_strchar)
                 (SX_STR o FOLDR (λs a. destSXSYM s ++ a) []));
            (mkNT sxnt_strchar,
             choicel [
                 tokeq #"\\" ~> pnt sxnt_escapedstrchar ;
                 pnt sxnt_normstrchar
               ]);
            (mkNT sxnt_escapedstrchar, choicel [tokeq #"\\"; tokeq #"\""]);
            (mkNT sxnt_normstrchar,
             tok (λc. isPrint c ∧ c ≠ #"\"" ∧ c ≠ #"\\") (λ(c,l). SX_SYM [c]))
           ]
  |>
End

Theorem sexpPEG_start[simp] = SIMP_CONV(srw_ss())[sexpPEG_def]“sexpPEG.start”
val ds = derive_compset_distincts “:sexpNT”
val {lookups,fdom_thm,applieds} =
  derive_lookup_ths {pegth = sexpPEG_def, ntty = “:sexpNT”,
                     simp = SIMP_CONV (srw_ss())}
Theorem sexpPEG_exec_thm[compute] = LIST_CONJ(sexpPEG_start::ds::lookups)
Theorem FDOM_sexpPEG = fdom_thm
Theorem sexpPEG_applied = LIST_CONJ applieds

Triviality frange_image:
  FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)
Proof
  simp[finite_mapTheory.FRANGE_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem sexpPEG_range[local] =
    SIMP_CONV (srw_ss())
              (fdom_thm :: frange_image :: applieds)
              “FRANGE sexpPEG.rules”

val wfpeg_rwts =
  wfpeg_cases
    |> ISPEC “sexpPEG”
    |> (fn th => map (fn t => Q.SPEC t th)
                     [‘seq e1 e2 f’, ‘choice e1 e2 f’, ‘tok P f’,
                      ‘any f’, ‘empty v’, ‘not e v’, ‘rpt e f’,
                      ‘choicel []’, ‘choicel (h::t)’, ‘tokeq t’,
                      ‘pegf e f’
       ])
    |> map (CONV_RULE
              (RAND_CONV (SIMP_CONV (srw_ss())
                 [choicel_def, tokeq_def, ignoreL_def,
                  ignoreR_def, pegf_def, grabWS_def])))


Theorem wfpeg_pnt[local] =
  wfpeg_cases
    |> ISPEC “sexpPEG”
    |> Q.SPEC ‘pnt n’
    |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def]))

val peg0_rwts = peg0_cases
                  |> ISPEC “sexpPEG” |> CONJUNCTS
                  |> map (fn th => map (fn t => Q.SPEC t th)
                                       [‘tok P f’, ‘choice e1 e2 f’,
                                        ‘seq e1 e2 f’, ‘tokeq t’, ‘empty l’,
                                        ‘not e v’, ‘rpt e f’])
                  |> List.concat
                  |> map (CONV_RULE
                            (RAND_CONV (SIMP_CONV (srw_ss())
                                                  [tokeq_def])))

Theorem wfpeg_grabWS[local] =
  SIMP_CONV (srw_ss()) (grabWS_def::ignoreL_def::wfpeg_rwts @ peg0_rwts)
                       “wfpeg sexpPEG (grabWS e)”


val pegfail_t = “pegfail”
val peg0_rwts = let
  fun filterthis th = let
    val c = concl th
    val (l,r) = dest_eq c
    val (f,_) = strip_comb l
  in
    not (same_const pegfail_t f) orelse is_const r
  end
in
  List.filter filterthis peg0_rwts
end

val pegnt_case_ths =
  peg0_cases
    |> ISPEC “sexpPEG” |> CONJUNCTS
    |> map (Q.SPEC ‘pnt n’)
    |> map (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def])))

fun pegnt(t,acc) = let
  val th =
      prove(“¬peg0 sexpPEG (pnt ^t)”,
            simp (fdom_thm::choicel_def::ignoreL_def::ignoreR_def::applieds @
                  pegnt_case_ths) >>
            simp(peg0_rwts @ acc))
  val nm = "peg0_" ^ term_to_string t
  val th' = save_thm(nm, SIMP_RULE bool_ss [pnt_def] th)
  val _ = export_rewrites [nm]
in
  th::acc
end

val npeg0_rwts =
    List.foldl pegnt []
   [“sxnt_symchars”, “sxnt_symchar”,
    “sxnt_strchar”, “sxnt_sexpsym”, “sxnt_sexpstr”,
    “sxnt_sexpnum”,  “sxnt_normstrchar”,
    “sxnt_grabWS”, “sxnt_first_symchar”, “sxnt_escapedstrchar”,
    “sxnt_escapablechar”, “sxnt_digit”,“sxnt_WS”]

Theorem npeg0_sexp0[local]:
  ¬peg0 sexpPEG (pnt sxnt_sexp0)
Proof
  simp pegnt_case_ths >> simp[fdom_thm] >>
  simp applieds >> simp[ignoreL_def,ignoreR_def] >>
  simp npeg0_rwts
QED

Theorem npeg0_WSsexp[local]:
  ¬peg0 sexpPEG (pnt sxnt_WSsexp)
Proof
  simp pegnt_case_ths >> simp[fdom_thm] >>
  simp applieds >> simp[ignoreL_def] >>
  simp (npeg0_sexp0::peg0_rwts)
QED

val npeg0_rwts = npeg0_WSsexp::npeg0_sexp0::npeg0_rwts

Theorem peg0_grabWS[local]:
  peg0 sexpPEG (grabWS e) = peg0 sexpPEG e
Proof simp(ignoreL_def::grabWS_def::peg0_rwts)
QED

fun wfnt(t,acc) = let
  val th =
    prove(“wfpeg sexpPEG (pnt ^t)”,
          SIMP_TAC (srw_ss())
                   (applieds @
                    [wfpeg_pnt, fdom_thm, ignoreL_def, ignoreR_def,
                     checkAhead_def]) THEN
          fs(peg0_grabWS :: wfpeg_grabWS :: wfpeg_rwts @ npeg0_rwts @
             peg0_rwts @ acc))
in
  th::acc
end;

val topo_nts =
  [“sxnt_sexpsym”,
   “sxnt_escapedstrchar”,
   “sxnt_normstrchar”,
   “sxnt_strchar”,
   “sxnt_strcontents”,
   “sxnt_digit”,
   “sxnt_sexpnum”,
   “sxnt_sexp0”,
   “sxnt_WSsexp”,
   “sxnt_sexpseq”,
   “sxnt_sexp”]

val wfpeg_thm = LIST_CONJ (List.foldl wfnt [] topo_nts)

Theorem subexprs_pnt[local]:
  subexprs (pnt n) = {pnt n}
Proof simp[subexprs_def, pnt_def]
QED

Theorem Gexprs_sexpPEG =
  “Gexprs sexpPEG”
    |> SIMP_CONV (srw_ss())
         [Gexprs_def, subexprs_def,
          subexprs_pnt, sexpPEG_start, sexpPEG_range,
          ignoreR_def, ignoreL_def,
          choicel_def, tokeq_def, pegf_def, grabWS_def,
          checkAhead_def,
          pred_setTheory.INSERT_UNION_EQ
         ]

Theorem wfG_sexpPEG:
  wfG sexpPEG
Proof
  rw[wfG_def,Gexprs_sexpPEG] >>
  srw_tac[boolSimps.DNF_ss][] >>
  simp(wfpeg_thm :: wfpeg_rwts @ npeg0_rwts)
QED

val _ = export_theory();
