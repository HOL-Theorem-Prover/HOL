open HolKernel Parse boolLib bossLib;

open regexpTheory pegTheory monadsyntax

val _ = new_theory "reSyntax";

val _ = temp_add_monadsyntax()

val _ = overload_on ("monad_bind", ``OPTION_BIND``)
val _ = overload_on ("monad_unitbind", ``OPTION_IGNORE_BIND``)
val _ = temp_overload_on ("return", ``SOME``)
val _ = temp_overload_on ("fail", ``NONE``)

val _ = computeLib.add_persistent_funs ["option.OPTION_BIND_def",
                                        "option.OPTION_IGNORE_BIND_def",
                                        "option.OPTION_GUARD_def",
                                        "option.OPTION_MAP_DEF",
                                        "option.OPTION_MAP2_DEF",
                                        "option.OPTION_CHOICE_def"]

val _ = overload_on ("assert", ``option$OPTION_GUARD : bool -> unit option``)
val _ = overload_on ("++", ``option$OPTION_CHOICE``)
val _ = overload_on ("lift", ``option$OPTION_MAP``)


val _ = Datatype‘reNT = Top | Alt | Concat | Star | Atom | CharSet |
                        BslashSpecial’;
val _ = overload_on("mkNT", ``INL : reNT -> reNT inf``)

val sumID_def = Define`
  sumID (INL x) = x ∧
  sumID (INR y) = y
`;

val choicel_def = Define`
  choicel [] = not (empty NONE) NONE ∧
  choicel (h::t) = choice h (choicel t) sumID
`;

val pegf_def = Define‘
  pegf sym f = seq sym (empty NONE) (λl1 l2. OPTION_MAP f l1)
’

val try_def = Define`
  try sym = choicel [sym; empty NONE]
`;

val pnt_def = Define‘pnt sym = nt (mkNT sym) I’;

val igLeft_def = Define‘
  igLeft s1 s2 = seq s1 s2 (λl1 l2. l2)
’;
val _ = set_mapped_fixity { tok = "*>", term_name = "igLeft", fixity = Infixl 500 }

val igRight_def = Define‘
  igRight s1 s2 = seq s1 s2 (λl1 l2. l1)
’;
val _ = set_mapped_fixity { tok = "<*", term_name = "igRight", fixity = Infixl 500 }

val igtok_def = Define‘igtok P = tok P (K NONE)’

val DigitSet_def = Define‘
  DigitSet = charset_string "0123456789"
’

val EscapableChar_def = Define‘
  EscapableChar c <=> MEM c "\\.^$*+?|~{}[]()" ∨ ORD c = 96’

val OrM_def = Define‘
  OrM roptlist = OPTION_MAP Or (OPT_MMAP I roptlist)
’

val rePEG_def = Define‘
  rePEG = <|
    start := pnt Top ;
    rules := FEMPTY |++ [
      (mkNT Atom,
       choicel [
         tok ((=) #".") (K (SOME (Chset charset_full)));

         igtok ((=) #"(") *> pnt Top <* igtok ((=) #")");

         igtok ((=) #"[") *> pnt CharSet <* igtok ((=) #"]");

         igtok ((=) #"\\") *> pnt BslashSpecial ;

         not (tok EscapableChar (K NONE)) NONE *>
         any (λc. SOME (Chset (charset_sing c)))
       ]);

      (mkNT BslashSpecial,
       choicel [
         tok ((=) #"d") (K (SOME (Chset DigitSet)));
         tok EscapableChar (λc. SOME (Chset (charset_sing c)))
       ]);

      (mkNT Star,
       seq (pnt Atom) (try (tok ((=) #"*") (K (SOME (Chset charset_empty)))))
           (λa_m s_m. do
              a <- a_m ;
              (do s <- s_m ; return (Star a) od ++ return a)
            od));

      (mkNT Concat,
       seq (pnt Star) (try (pnt Concat))
           (λs_m c_m. do
              s <- s_m ;
              (do c <- c_m ; return (Cat s c) od ++ return s)
            od));

      (mkNT Alt,
       seq (pnt Concat) (rpt (igtok ((=) #"|") *> pnt Concat) OrM)
           (λc_m rep_m. do
              c <- c_m ;
              rep <- rep_m ;
              case rep of
                  Or l => return (Or (c::l))
                | _ => return c
            od));

      (mkNT Top, pnt Alt)
     ]
  |>
’;


(*
open pegexecTheory
val _ = computeLib.add_persistent_funs ["pegexec.peg_nt_thm"]

val r = EVAL ``peg_exec rePEG rePEG.start "\\d" [] done failed``
val r = EVAL ``peg_exec rePEG rePEG.start "\\(" [] done failed``
val r = EVAL ``peg_exec rePEG rePEG.start ".\\d" [] done failed``
val r = EVAL ``peg_exec rePEG rePEG.start "(ab)" [] done failed``
val r = EVAL ``peg_exec rePEG rePEG.start "(ab)*ab*" [] done failed``
val r = EVAL ``peg_exec rePEG rePEG.start "a|b*c|d" [] done failed``
*)

val _ = export_theory();
