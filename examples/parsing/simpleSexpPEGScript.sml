open HolKernel Parse boolLib bossLib;

open simpleSexpTheory

val _ = new_theory "simpleSexpPEG";

val tokeq_def = Define`tokeq t = tok ((=) t) (K (SX_SYM [t]))`
val grabWS_def = Define`
  grabWS s = rpt (tok isSpace ARB) (K ARB) >> s
`;

val pnt_def = Define`pnt ntsym = nt (mkNT ntsym) I`

val isFirstSymChar_def = Define`
  isFirstSymChar c ⇔ isGraph c ∧ ¬isDigit c ∧ c ∉ {#"("; #"'"; #")"; #"."}
`;

val sexpPEG_def = zDefine`
  sexpPEG : (char, sexpNT, sexp) peg = <|
    start := pnt sxnt_sexp ;
    rules :=
    FEMPTY |++
    [(mkNT sxnt_sexp, pnt sxnt_WSsexp << rpt (tok isSpace ARB) (K ARB));
     (mkNT sxnt_sexp0,
      choicel [
        pnt sxnt_sexpnum ;
        tokeq #"(" >> pnt sxnt_sexpseq << grabWS (tokeq #")") ;
        seq (tokeq #"(" >> pnt sxnt_WSsexp)
            (grabWS (tokeq #".") >> pnt sxnt_WSsexp << grabWS (tokeq #")"))
            SX_CONS ;
        tokeq #"\"" >> pnt sxnt_strcontents << tokeq #"\"" ;
        pegf (tokeq #"'" >> grabWS (pnt sxnt_sexp0))
             (λs. ⦇ SX_SYM "quote"; s⦈) ;
        pnt sxnt_sexpsym
      ]);
     (mkNT sxnt_sexpseq,
      rpt (pnt sxnt_WSsexp) (FOLDR SX_CONS (SX_SYM "nil")));
     (mkNT sxnt_WSsexp,
      rpt (tok isSpace ARB) (K ARB) >> pnt sxnt_sexp0);
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
        tokeq #"\\" >> pnt sxnt_escapedstrchar ;
        pnt sxnt_normstrchar
      ]);
     (mkNT sxnt_escapedstrchar, choicel [tokeq #"\\"; tokeq #"\""]);
     (mkNT sxnt_normstrchar,
      tok (λc. isPrint c ∧ c ≠ #"\"" ∧ c ≠ #"\\") (λc. SX_SYM [c]))
    ]
  |>
`;


val _ = export_theory();
