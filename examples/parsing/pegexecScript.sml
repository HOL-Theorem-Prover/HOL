open HolKernel Parse boolLib bossLib

open boolSimps

open pegTheory

val _ = new_theory "pegexec"

val _ = Hol_datatype`
  kont =
    ksym of ('atok,'bnt,'cvalue,'etok) pegsym => kont => kont
  | appf1 of ('cvalue -> 'cvalue) => kont
  | appf2 of ('cvalue -> 'cvalue -> 'cvalue) => kont
  | returnTo of 'etok list => 'cvalue option list => kont
  | poplist of ('cvalue list -> 'cvalue) => kont
  | listsym of ('atok,'bnt,'cvalue,'etok) pegsym =>
               ('cvalue list -> 'cvalue) =>
               kont
  | done
  | failed
`

val poplist_aux_def = Define`
  poplist_aux acc (SOME h::t) = poplist_aux (h::acc) t ∧
  poplist_aux acc (NONE::t) = (acc,t)
`;

val poplistval_def = Define`
  poplistval f l = let (values,rest) = poplist_aux [] l
                   in
                     SOME(f values) :: rest
`;

val _ = Hol_datatype `
  evalcase = EV of ('atok,'bnt,'cvalue,'etok) pegsym =>
                   'etok list => 'cvalue option list =>
                   ('atok,'bnt,'cvalue,'etok) kont =>
                   ('atok,'bnt,'cvalue,'etok) kont
           | AP of ('atok,'bnt,'cvalue,'etok) kont =>
                   'etok list => 'cvalue option list
           | LV of ('atok,'bnt,'cvalue,'etok) pegsym =>
                   ('cvalue list -> 'cvalue) =>
                   'etok list => 'cvalue option list =>
                   ('atok,'bnt,'cvalue,'etok) kont
           | Result of ('cvalue # 'etok list) option
`;

val eval_def = Define`
  eval (G:('atok,'bnt,'cvalue,'etok)peg) e i r k fk =
    WHILE (λs. case s of Result _ => F
                       | _ => T)
          (λs. case s of
                   EV (empty v) i r k fk => AP k i (SOME v::r)
                 | EV (any tf) i r k fk =>
                   (case i of
                        [] => AP fk i r
                      | h::t => AP k t (SOME (tf (G.cf h) h) :: r))
                 | EV (tok tk tf2) i r k fk =>
                   (case i of
                        [] => AP fk i r
                      | h::t => if G.cf h = tk then AP k t (SOME (tf2 h)::r)
                                else AP fk i r)
                 | EV (nt n tf3) i r k fk =>
                   if n ∈ FDOM G.rules then
                     EV (G.rules ' n) i r (appf1 tf3 k) fk
                   else
                     Result NONE
                 | EV (seq e1 e2 f) i r k fk =>
                     EV e1 i r
                        (ksym e2 (appf2 f k) (returnTo i r fk))
                        fk
                 | EV (choice e1 e2 cf) i r k fk =>
                     EV e1 i r
                        (appf1 (cf o INL) k)
                        (returnTo i r (ksym e2 (appf1 (cf o INR) k) fk))
                 | EV (rpt e lf) i r k fk => LV e lf i (NONE::r) k
                 | EV (not e v) i r k fk =>
                     EV e i r (returnTo i r fk) (returnTo i (SOME v::r) k)
                 | AP done i r => Result(SOME(THE (HD r), i))
                 | AP failed i r => Result NONE
                 | AP (ksym e k fk) i r => EV e i r k fk
                 | AP (appf1 f1 k) i (SOME v :: r) => AP k i (SOME (f1 v) :: r)
                 | AP (appf2 f2 k) i (SOME v1 :: SOME v2 :: r) =>
                     AP k i (SOME (f2 v2 v1) :: r)
                 | AP (returnTo i r k) i' r' => AP k i r
                 | AP (listsym e f k) i r => LV e f i r k
                 | AP (poplist f k) i r => AP k i (poplistval f r)
                 | LV e f i r k => EV e i r (listsym e f k) (poplist f k))
          (EV e i r k fk)
`

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
val nrule =
  ``tok (mkTok Number) (\e. case e of ENumber n => XN n) : ^ty``
val paren_rule =
  ``seq (tok (mkTok LParen) (K (XN 0)))
        (seq (nt (INL "expr") I) (tok (mkTok RParen) (K (XN 0))) (\a b. a))
        (\a b. b) : ^ty``

val termpair =
  ``(INL "term" : string inf,
     choice ^nrule ^paren_rule (\s. case s of INL e => e | INR e => e))``

val factorpair = ``(INL "factor" : string inf,
                    seq (rpt (seq (nt (INL "term") I)
                                            (tok (mkTok Times) (K ARB))
                                            (\a b. a))
                                       XList)
                                  (nt (INL "term") I)
                                  (\a b.
                                    case a of
                                      XList (h::t) => FOLDL XTimes h (t ++ [b])
                                    | _ => b) : ^ty)``

val exprpair = ``(INL "expr" : string inf,
                  seq (rpt (seq (nt (INL "factor") I)
                                        (tok (mkTok Plus) (K ARB))
                                        (\a b. a))
                                   XList)
                              (nt (INL "factor") I)
                              (\a b.
                                case a of
                                  XList (h::t) => FOLDL XPlus h (t ++ [b])
                                | _ => b) : ^ty)``

val rules = ``FEMPTY |+ ^exprpair |+ ^factorpair |+ ^termpair``

val G = ``<| start := nt (INL "expr") I; rules := ^rules; cf := categorise |>``

val testexp = ``[ENumber 3; EPlus; ENumber 4; ETimes; ENumber 5]``

(*
val eval = ``eval`` and while_t = ``WHILE``
val _ =
    computeLib.monitoring :=
    SOME (fn t => same_const eval t orelse same_const while_t t)
val result =
EVAL ``eval ^G (nt (INL "term") I)
                        [ELParen; ENumber 1; ERParen] [] done failed``
*)


val _ = export_theory()
