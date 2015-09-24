open HolKernel Parse boolLib bossLib lcsymtacs;

open simpleSexpTheory pegTheory pegLib

val _ = new_theory "simpleSexpPEG";

(* TODO: move? *)
val pegfail_empty = store_thm(
  "pegfail_empty[simp]",
  ``pegfail G (empty r) = F``,
  simp[Once peg0_cases]);

val peg0_empty = store_thm(
  "peg0_empty[simp]",
  ``peg0 G (empty r) = T``,
  simp[Once peg0_cases]);

val peg0_not = store_thm(
  "peg0_not[simp]",
  ``peg0 G (not s r) ⇔ pegfail G s``,
  simp[Once peg0_cases, SimpLHS]);

val peg0_choice = store_thm(
  "peg0_choice[simp]",
  ``peg0 G (choice s1 s2 f) ⇔ peg0 G s1 ∨ pegfail G s1 ∧ peg0 G s2``,
  simp[Once peg0_cases, SimpLHS]);

val peg0_choicel = store_thm(
  "peg0_choicel[simp]",
  ``(peg0 G (choicel []) = F) ∧
    (peg0 G (choicel (h::t)) ⇔ peg0 G h ∨ pegfail G h ∧ peg0 G (choicel t))``,
  simp[choicel_def])

val peg0_seq = store_thm(
  "peg0_seq[simp]",
  ``peg0 G (seq s1 s2 f) ⇔ peg0 G s1 ∧ peg0 G s2``,
  simp[Once peg0_cases, SimpLHS])

val peg0_pegf = store_thm(
  "peg0_pegf[simp]",
  ``peg0 G (pegf s f) = peg0 G s``,
  simp[pegf_def])

val peg0_tok = store_thm(
  "peg0_tok[simp]",
  ``peg0 G (tok P f) = F``,
  simp[Once peg0_cases])
(*--*)

val tokeq_def = Define`tokeq t = tok ((=) t) (K (SX_SYM [t]))`
val grabWS_def = Define`
  grabWS s = rpt (tok isSpace ARB) (K ARB) ~> s
`;

val peg0_tokeq = store_thm(
  "peg0_tokeq[simp]",
  ``peg0 G (tokeq t) = F``,
  simp[tokeq_def])

val pnt_def = Define`pnt ntsym = nt (mkNT ntsym) I`

val isFirstSymChar_def = Define`
  isFirstSymChar c ⇔ isGraph c ∧ ¬isDigit c ∧ c ∉ {#"("; #"'"; #")"; #"."}
`;

val sexpPEG_def = zDefine`
  sexpPEG : (char, sexpNT, sexp) peg = <|
    start := pnt sxnt_sexp ;
    rules :=
    FEMPTY |++
    [(mkNT sxnt_sexp, pnt sxnt_WSsexp <~ rpt (tok isSpace ARB) (K ARB));
     (mkNT sxnt_sexp0,
      choicel [
        pnt sxnt_sexpnum ;
        tokeq #"(" ~> pnt sxnt_sexpseq <~ grabWS (tokeq #")") ;
        seq (tokeq #"(" ~> pnt sxnt_WSsexp)
            (grabWS (tokeq #".") ~> pnt sxnt_WSsexp <~ grabWS (tokeq #")"))
            SX_CONS ;
        tokeq #"\"" ~> pnt sxnt_strcontents <~ tokeq #"\"" ;
        pegf (tokeq #"'" ~> grabWS (pnt sxnt_sexp0))
             (λs. ⦇ SX_SYM "quote"; s⦈) ;
        pnt sxnt_sexpsym
      ]);
     (mkNT sxnt_sexpseq,
      rpt (pnt sxnt_WSsexp) (FOLDR SX_CONS (SX_SYM "nil")));
     (mkNT sxnt_WSsexp,
      rpt (tok isSpace ARB) (K ARB) ~> pnt sxnt_sexp0);
     (mkNT sxnt_sexpnum,
      checkAhead isDigit
          (rpt (pnt sxnt_digit)
               (SX_NUM o FOLDL (λa d. 10 * a + destSXNUM d) 0))) ;
     (mkNT sxnt_digit, tok isDigit (λc. SX_NUM (ORD c - ORD #"0"))) ;
     (mkNT sxnt_sexpsym,
      seq (tok isFirstSymChar (λc. SX_SYM [c]))
          (rpt (tok (λc. isGraph c ∧ c ∉ {#"("; #")"; #"'"}) (λc. SX_SYM [c]))
               (SX_SYM o FOLDR (λs a. destSXSYM s ++ a) []))
          (λs1 s2. SX_SYM (destSXSYM s1 ++ destSXSYM s2)));
     (mkNT sxnt_strcontents,
      rpt (pnt sxnt_strchar) (SX_STR o FOLDR (λs a. destSXSYM s ++ a) []));
     (mkNT sxnt_strchar,
      choicel [
        tokeq #"\\" ~> pnt sxnt_escapedstrchar ;
        pnt sxnt_normstrchar
      ]);
     (mkNT sxnt_escapedstrchar, choicel [tokeq #"\\"; tokeq #"\""]);
     (mkNT sxnt_normstrchar,
      tok (λc. isPrint c ∧ c ≠ #"\"" ∧ c ≠ #"\\") (λc. SX_SYM [c]))
    ]
  |>
`;

val sexpPEG_start = SIMP_CONV(srw_ss())[sexpPEG_def]``sexpPEG.start``
val ds = derive_compset_distincts ``:sexpNT``
val {lookups,fdom_thm,applieds} = derive_lookup_ths {pegth = sexpPEG_def, ntty = ``:sexpNT``, simp = SIMP_CONV (srw_ss())}
val sexpPEG_exec_thm = save_thm("sexpPEG_exec_thm",LIST_CONJ(sexpPEG_start::ds::lookups))
val _ = computeLib.add_persistent_funs["sexpPEG_exec_thm"];

val frange_image = prove(
  ``FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)``,
  simp[finite_mapTheory.FRANGE_DEF, pred_setTheory.EXTENSION] >> metis_tac[]);

val sexpPEG_range =
    SIMP_CONV (srw_ss())
              (fdom_thm :: frange_image :: applieds)
              ``FRANGE sexpPEG.rules``

val wfpeg_rwts = wfpeg_cases
                   |> ISPEC ``sexpPEG``
                   |> (fn th => map (fn t => Q.SPEC t th)
                                    [`seq e1 e2 f`, `choice e1 e2 f`, `tok P f`,
                                     `any f`, `empty v`, `not e v`, `rpt e f`,
                                     `choicel []`, `choicel (h::t)`, `tokeq t`,
                                     `pegf e f`
                      ])
                   |> map (CONV_RULE
                             (RAND_CONV (SIMP_CONV (srw_ss())
                                                   [choicel_def, tokeq_def,
                                                    pegf_def])))

val wfpeg_pnt = wfpeg_cases
                  |> ISPEC ``sexpPEG``
                  |> Q.SPEC `pnt n`
                  |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def]))

val peg0_rwts = peg0_cases
                  |> ISPEC ``sexpPEG`` |> CONJUNCTS
                  |> map (fn th => map (fn t => Q.SPEC t th)
                                       [`tok P f`, `choice e1 e2 f`, `seq e1 e2 f`,
                                        `tokeq t`, `empty l`, `not e v`, `rpt e f`])
                  |> List.concat
                  |> map (CONV_RULE
                            (RAND_CONV (SIMP_CONV (srw_ss())
                                                  [tokeq_def])))

val pegfail_t = ``pegfail``
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

val pegnt_case_ths = peg0_cases
                      |> ISPEC ``sexpPEG`` |> CONJUNCTS
                      |> map (Q.SPEC `pnt n`)
                      |> map (CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [pnt_def])))

fun pegnt(t,acc) = let
  val th =
      prove(``¬peg0 sexpPEG (pnt ^t)``,
            simp (fdom_thm::choicel_def::ignoreL_def::pegnt_case_ths @ applieds @ peg0_rwts) >>
            simp(peg0_rwts @ acc))
  val nm = "peg0_" ^ term_to_string t
  val th' = save_thm(nm, SIMP_RULE bool_ss [pnt_def] th)
  val _ = export_rewrites [nm]
in
  th::acc
end

val peg0_sexpnum = prove(
  ``peg0 sexpPEG (pnt sxnt_sexpnum)``,
  rw[Once peg0_cases,pnt_def,fdom_thm] >>
  rw applieds >>
  rw[checkAhead_def] >>
  rw[ignoreL_def] >>
  rw[Once peg0_cases] >>
  rw[Once peg0_cases] >>
  rw[Once peg0_cases] >>
  rw[Once peg0_cases,pnt_def] >>
  rw[fdom_thm] >>
  rw applieds >>
  rw[Once peg0_cases])

val peg0_sexp0 = prove(
  ``peg0 sexpPEG (pnt sxnt_sexp0)``,
  rw[Once peg0_cases,pnt_def,fdom_thm] >>
  rw applieds >>
  rw[peg0_sexpnum])

val peg0_WSsexp = prove(
  ``peg0 sexpPEG (pnt sxnt_WSsexp)``,
      rw[Once peg0_cases,pnt_def,fdom_thm] >>
      rw applieds >>
      rw[ignoreL_def] >- (
      rw[Once peg0_cases] >>
      rw[Once peg0_cases] ) >>
      rw[peg0_sexp0])

val nwfpeg_sexpstr = Q.prove(
  `¬wfpeg sexpPEG (pnt sxnt_sexpstr)`,
  rw(applieds@[wfpeg_pnt,fdom_thm]))

val npeg0_rwts =
    List.foldl pegnt []
   [``sxnt_symchars``, ``sxnt_symchar``,
    ``sxnt_strchar``, ``sxnt_sexpsym``, ``sxnt_sexpstr``,
    (*``sxnt_sexpnum``, ``sxnt_sexp0``, ``sxnt_sexp``, *) ``sxnt_normstrchar``,
    ``sxnt_grabWS``, ``sxnt_first_symchar``, ``sxnt_escapedstrchar``,
    ``sxnt_escapablechar``, ``sxnt_digit``(*, ``sxnt_WSsexp``*), ``sxnt_WS``]

fun wfnt(t,acc) = let
  val th =
    prove(``wfpeg sexpPEG (pnt ^t)``,
          SIMP_TAC (srw_ss())
                   (applieds @
                    [wfpeg_pnt, fdom_thm, ignoreL_def, ignoreR_def, checkAhead_def]) THEN
          fs(wfpeg_rwts @ npeg0_rwts @ peg0_rwts @ acc))
in
  th::acc
end;

val topo_nts =
  [(*``sxnt_symchar``,
   ``sxnt_symchars``,
   ``sxnt_first_symchar``,*)
   ``sxnt_sexpsym``,
   (*``sxnt_escapablechar``,*)
   ``sxnt_escapedstrchar``,
   ``sxnt_normstrchar``,
   ``sxnt_strchar``,
   ``sxnt_strcontents``,
   (*``sxnt_sexpstr``,*)
   ``sxnt_digit``,
   ``sxnt_sexpnum``,
   ``sxnt_sexp0``,
   (*``sxnt_WS``,
   ``sxnt_grabWS``,*)
   ``sxnt_WSsexp``,
   (*``sxnt_sexpseq``,*)
   ``sxnt_sexp``]

val wfpeg_thm = save_thm(
  "wfpeg_thm",
  LIST_CONJ (List.foldl wfnt [] topo_nts))

val subexprs_pnt = prove(
  ``subexprs (pnt n) = {pnt n}``,
  simp[subexprs_def, pnt_def]);

val PEG_exprs = save_thm(
  "PEG_exprs",
  ``Gexprs sexpPEG``
    |> SIMP_CONV (srw_ss())
         [Gexprs_def, subexprs_def,
          subexprs_pnt, sexpPEG_start, sexpPEG_range,
          ignoreR_def, ignoreL_def,
          choicel_def, tokeq_def, pegf_def, grabWS_def,
          checkAhead_def,
          pred_setTheory.INSERT_UNION_EQ
         ])

val PEG_wellformed = store_thm(
  "PEG_wellformed",
  ``¬wfG sexpPEG``,
  rw[wfG_def,PEG_exprs] >>
  srw_tac[boolSimps.DNF_ss][] >>
  simp(wfpeg_thm :: wfpeg_rwts @ npeg0_rwts) >>
  rw[peg0_WSsexp])

val _ = export_theory();
