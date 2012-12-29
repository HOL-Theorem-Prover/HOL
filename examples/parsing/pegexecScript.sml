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
           | Result of ('cvalue # 'etok list) option
`;

val coreloop_def = zDefine`
  coreloop G =
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
                 | EV (rpt e lf) i r k fk =>
                     EV e i (NONE::r) (listsym e lf k) (poplist lf k)
                 | EV (not e v) i r k fk =>
                     EV e i r (returnTo i r fk) (returnTo i (SOME v::r) k)
                 | AP done i r => Result(SOME(THE (HD r), i))
                 | AP failed i r => Result NONE
                 | AP (ksym e k fk) i r => EV e i r k fk
                 | AP (appf1 f1 k) i (SOME v :: r) => AP k i (SOME (f1 v) :: r)
                 | AP (appf2 f2 k) i (SOME v1 :: SOME v2 :: r) =>
                     AP k i (SOME (f2 v2 v1) :: r)
                 | AP (returnTo i r k) i' r' => AP k i r
                 | AP (listsym e f k) i r =>
                     EV e i r (listsym e f k) (poplist f k)
                 | AP (poplist f k) i r => AP k i (poplistval f r))
`;


val eval_def = zDefine`
  eval (G:('atok,'bnt,'cvalue,'etok)peg) e i r k fk = coreloop G (EV e i r k fk)
`

val applykont_def = zDefine`applykont G k i r = coreloop G (AP k i r)`

open lcsymtacs
val coreloop_result = store_thm(
  "coreloop_result",
  ``coreloop G (Result x) = Result x``,
  simp[coreloop_def, Once whileTheory.WHILE]);

fun inst_thm def (qs,ths) =
    def |> SIMP_RULE (srw_ss()) [Once whileTheory.WHILE, coreloop_def]
        |> SPEC_ALL
        |> Q.INST qs
        |> SIMP_RULE (srw_ss()) []
        |> SIMP_RULE bool_ss (GSYM eval_def :: GSYM coreloop_def ::
                              GSYM applykont_def :: coreloop_result :: ths)

val eval_thm = inst_thm eval_def

val better_evals =
    map eval_thm [([`e` |-> `empty v`], []),
                  ([`e` |-> `tok t f`, `i` |-> `[]`], []),
                  ([`e` |-> `tok t f`, `i` |-> `x::xs`], [Once COND_RAND]),
                  ([`e` |-> `any f`, `i` |-> `[]`], []),
                  ([`e` |-> `any f`, `i` |-> `x::xs`], []),
                  ([`e` |-> `seq e1 e2 sf`], []),
                  ([`e` |-> `choice e1 e2 cf`], []),
                  ([`e` |-> `nt n nfn`], [Once COND_RAND]),
                  ([`e` |-> `not e v`], []),
                  ([`e` |-> `rpt e lf`], [])]

val better_apply =
    map (inst_thm applykont_def)
        [([`k` |-> `ksym e k fk`], []),
         ([`k` |-> `appf1 f k`, `r` |-> `SOME v::r`], []),
         ([`k` |-> `appf2 f k`, `r` |-> `SOME v1::SOME v2::r`], []),
         ([`k` |-> `returnTo i' r' k`], []),
         ([`k` |-> `done`], []),
         ([`k` |-> `failed`], []),
         ([`k` |-> `poplist f k`], []),
         ([`k` |-> `listsym e f k`], [])]

val eval_thm = save_thm("eval_thm", LIST_CONJ better_evals);
val applykont_thm = save_thm("applykont_thm", LIST_CONJ better_apply);

val _ = computeLib.add_persistent_funs ["eval_thm", "applykont_thm"]


val _ = export_theory()
