(*  this is an -*- sml -*- file *)
open lcsymtacs boolSimps
open pred_setTheory nomsetTheory generic_termsTheory

fun rpt_hyp_dest_conj th = let
  fun foldthis (t, acc) = let
    fun dc t = let
      val (c1, c2) = dest_conj t
    in
      CONJ (dc c1) (dc c2)
    end handle HOL_ERR _ => ASSUME t
  in
    PROVE_HYP (dc t) acc
  end
in
  HOLset.foldl foldthis th (hypset th)
end

fun hCONJ th1 th2 =
    case (hyp th1, hyp th2) of
      ([h1], [h2]) => let
        val h12 = ASSUME(mk_conj(h1,h2))
      in
        CONJ th1 th2
             |> PROVE_HYP (CONJUNCT1 h12)
             |> PROVE_HYP (CONJUNCT2 h12)
      end
    | _ => CONJ th1 th2

fun elim_unnecessary_atoms th = let
  val th = th |> SPEC_ALL |> UNDISCH
  fun doit v t = let
    val (vs, bod) = strip_forall t
    val (h, c) = dest_imp bod
    val hcs = strip_conj h
    val (goodhs, badhs) = List.partition (not o free_in v) hcs
    val (goodvs, _) = List.partition (not o equal v) vs
    val a = list_mk_forall(goodvs, mk_imp(list_mk_conj goodhs, c)) |> ASSUME
    fun recreate h th =
        if is_conj h then let
            val (c1, c2) = dest_conj h
            val th' = th |> recreate c1 |> recreate c2
            val h_th = ASSUME h
          in
            th' |> PROVE_HYP (CONJUNCT1 h_th) |> PROVE_HYP (CONJUNCT2 h_th)
          end
        else ADD_ASSUM h th
  in
    a |> SPEC_ALL |> UNDISCH |> rpt_hyp_dest_conj
      |> recreate h |> DISCH h |> GENL vs
  end

  fun one_conj t = let
    val (vs, bod) = strip_forall t
    val (h, c) = dest_imp bod
    fun test v = type_of v = stringLib.string_ty andalso not (free_in v c)
  in
    case List.find test vs of
      NONE => ASSUME t
    | SOME v => doit v t
  end handle HOL_ERR _ => ASSUME t
  fun transform t = let
    val (c1, c2) = dest_conj t
  in
    hCONJ (transform c1) (transform c2)
  end handle HOL_ERR _ => one_conj t
in
  HOLset.foldl (fn (t, th) => PROVE_HYP (transform t) th) th (hypset th)
end

datatype NDTY = NDV of string
              | NEWTY of int
              | NTYOP of {Thy : string, Tyop : string, Args : NDTY list}
              | NATOM
fun ndty2ty ndty =
    case ndty of
      NDV v => mk_vartype v
    | NTYOP{Thy,Tyop,Args} => mk_thy_type {Thy=Thy,Tyop=Tyop,
                                           Args = map ndty2ty Args}
    | NEWTY _ => raise Fail "ndty2ty: NEWTY"
    | NATOM => stringLib.string_ty

fun ty2ndty ty =
    case Lib.total dest_thy_type ty of
      SOME {Thy,Tyop,Args} => NTYOP {Thy = Thy, Tyop = Tyop,
                                     Args = map ty2ndty Args}
    | NONE => NDV (dest_vartype ty)


datatype bstatus = Bound | Unbound
datatype constructor_spec =
         CSP of {name : string, args : (NDTY * bstatus) list}

type type_spec = (string * constructor_spec list) list

val term_spec = [("term",
                  [CSP {name = "LAM",
                        args = [(NATOM, Unbound), (NEWTY 0, Bound)]},
                   CSP {name = "APP",
                        args = [(NEWTY 0, Unbound), (NEWTY 0, Unbound)]},
                   CSP {name = "VAR", args = [(NATOM, Bound)]}])]

val lterm_spec = [("lterm",
                   [CSP {name = "LAMi",
                         args = [(ty2ndty ``:num``, Unbound),
                                 (NATOM, Unbound),
                                 (NEWTY 0, Bound),
                                 (NEWTY 0, Unbound)]},
                    CSP {name = "LAM",
                         args = [(NATOM, Unbound), (NEWTY 0, Bound)]},
                    CSP {name = "APP",
                         args = [(NEWTY 0, Unbound), (NEWTY 0, Unbound)]},
                    CSP {name = "VAR", args = [(NATOM, Bound)]}])]

fun ndty_exists P nty =
    P nty orelse
    (case nty of
       NTYOP{Args,...} => List.exists (ndty_exists P) Args
     | _ => false)

fun isNEWTY (NEWTY _) = true
  | isNEWTY _ = false

fun is_recursive (CSP{args,...}) =
    List.exists (ndty_exists isNEWTY o #1) args

fun consp_nonatom_extras (consp as CSP{name,args}, acc) =
    if is_recursive consp then let
        fun foldthis ((ndty,_), acc) =
            case ndty of
              NATOM => acc
            | _ => ndty2ty ndty :: acc handle Fail _ => acc
      in
        (name, foldl foldthis [] args) :: acc
      end
    else acc

fun extra_nonatom_types tysp = let
  fun foldthis ((_, consps), acc) = List.foldl consp_nonatom_extras acc consps
in
  foldl foldthis [] tysp
end

(* extra_nonatom_types term_spec = [("APP", []), ("LAM", [])] *)

fun ndty_filter P (ndty,acc) = let
  val subtree =
      case ndty of
        NTYOP {Args,...} => List.foldl (ndty_filter P) acc Args
      | _ => acc
in
  if P ndty then ndty :: subtree else subtree
end

fun isATOM (ndty, bstatus) =
    bstatus = Bound andalso ndty_exists (equal NATOM) ndty

fun consp_atom_extras (consp as CSP {name, args}, acc) =
    if List.exists isATOM args then let
        fun foldthis ((ndty, _), acc) =
            case ndty of
              NATOM => acc
            | _ => ndty2ty ndty :: acc
              handle Fail _ => raise Fail "Can't accompany bound atoms with\
                                           \ recursive types"
      in
        (name, List.foldl foldthis [] args) :: acc
      end
    else acc

fun extra_atom_types tysp = let
  fun foldthis ((_, consps), acc) = List.foldl consp_atom_extras acc consps
in
  foldl foldthis [] tysp
end

fun mk_atom_ty tysp = let
  val atomtys = extra_atom_types tysp
  fun one_bunch (_, []) = ``:unit``
    | one_bunch (_, tys) = pairSyntax.list_mk_prod tys
in
  List.foldr (fn (bnch,ty) => sumSyntax.mk_sum (one_bunch bnch, ty))
             (one_bunch (hd atomtys))
             (tl atomtys)
end




val vp = ``(λn u:unit. n = 0)``
val lp = ``(λn (d:unit + unit) tns uns.
               (n = 0) ∧ ISL d ∧ (tns = [0]) ∧ (uns = []) ∨
               (n = 0) ∧ ISR d ∧ (tns = []) ∧ (uns = [0;0]))``

val termP = ``genind  ^vp ^lp 0``

val _ = temp_overload_on ("termP", ``^termP``)

val LIST_REL_NIL1 = prove(
  ``LIST_REL R [] x ⇔ (x = [])``,
  Cases_on `x` >> srw_tac [][]);
val LIST_REL_CONS1 = prove(
  ``LIST_REL R (h::t) xs ⇔ ∃h' t'. (xs = h'::t') ∧ R h h' ∧ LIST_REL R t t'``,
  Cases_on `xs` >> srw_tac [][]);

val FORALL_ONE = prove(
  ``(∀x:unit. P x) ⇔ P ()``,
  srw_tac [][EQ_IMP_THM, oneTheory.one_induction]);


val term_exists = prove(
  ``∃x. ^termP x``,
  Q.EXISTS_TAC `GVAR s ()` >> srw_tac [][genind_rules]);

val term_bij_ax = new_type_definition("term", term_exists)
val term_ABSREP =
    define_new_type_bijections { ABS = "term_ABS", REP = "term_REP",
                                 name = "term_ABSREP", tyax = term_bij_ax}

val term_ABS_pseudo11 = prove(
  ``^termP x ∧ ^termP y ⇒ ((term_ABS x = term_ABS y) ⇔ (x = y))``,
  srw_tac [][EQ_IMP_THM] >> pop_assum (MP_TAC o Q.AP_TERM `term_REP`) >>
  metis_tac [term_ABSREP]);

val genind_exists = prove(
  ``^termP g ⇔ ∃t. (g = term_REP t)``,
  metis_tac [term_ABSREP]);

val genind_term_REP = prove(
  ``^termP (term_REP t)``,
  metis_tac [term_ABSREP]);


val LAM_def = new_definition(
  "LAM_def",
  ``LAM v t = term_ABS (GLAM v (INL ()) [term_REP t] [])``)

val [gvar,glam] = genind_rules |> SPEC_ALL |> CONJUNCTS

val LAM_termP = prove(
  ``^termP (GLAM v (INL ()) [term_REP t] [])``,
  match_mp_tac glam >> srw_tac [][genind_term_REP]);

val APP_def = new_definition(
  "APP_def",
  ``APP t1 t2 = term_ABS (GLAM ARB (INR ()) [] [term_REP t1; term_REP t2])``);

val APP_termP = prove(
  ``^termP (GLAM x (INR ()) [] [term_REP t1; term_REP t2])``,
  match_mp_tac glam >> srw_tac [][genind_term_REP])

val APP_def' = prove(
  ``term_ABS (GLAM v (INR ()) [] [term_REP t1; term_REP t2]) = APP t1 t2``,
  srw_tac [][APP_def, GLAM_NIL_EQ, term_ABS_pseudo11, APP_termP]);

val VAR_def = new_definition(
  "VAR_def",
  ``VAR s = term_ABS (GVAR s ())``);

val VAR_termP = prove(
  ``^termP (GVAR s ())``,
  srw_tac [][genind_rules]);

val tpm_def = new_definition(
  "tpm_def",
  ``tpm pi t = term_ABS (gtpm pi (term_REP t))``);

val repabs_id = term_ABSREP |> CONJUNCT2 |> SPEC_ALL |> (#1 o EQ_IMP_RULE)
                            |> GEN_ALL

val term_REP_tpm =
    tpm_def |> SPEC_ALL |> Q.AP_TERM `term_REP`
            |> SIMP_RULE bool_ss [repabs_id, genind_gtpm_eqn, genind_term_REP]

val tpm_is_perm = store_thm(
  "tpm_is_perm",
  ``is_perm tpm``,
  srw_tac [][is_perm_def, FUN_EQ_THM, tpm_def, gtpm_NIL,
             GSYM gtpm_compose, repabs_id, term_ABSREP]
  >- srw_tac [][GSYM term_REP_tpm, term_ABSREP] >>
  AP_TERM_TAC >> metis_tac [is_perm_def, gtpm_is_perm]);
val _ = export_rewrites ["tpm_is_perm"]


fun genit th = let
  val (_, args) = strip_comb (concl th)
  val (tm, x) = case args of [x,y] => (x,y) | _ => raise Fail "Bind"
  val ty = type_of tm
  val t = mk_var("t", ty)
in
  th |> INST [tm |-> t] |> GEN x |> GEN t
end

val term_ind =
    bvc_genind |> INST_TYPE [alpha |-> ``:unit+unit``, beta |-> ``:unit``]
               |> Q.INST [`vp` |-> `^vp`, `lp` |-> `^lp`]
               |> SIMP_RULE std_ss [LIST_REL_NIL1, LIST_REL_CONS1,
                                    RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR,
                                    DISJ_IMP_THM]
               |> Q.SPEC `λn t0 x. Q t0 x`
               |> Q.SPEC `fv`
               |> UNDISCH |> Q.SPEC `0` |> DISCH_ALL
               |> SIMP_RULE (std_ss ++ DNF_ss)
                            [sumTheory.FORALL_SUM, supp_listpm,
                             IN_UNION, NOT_IN_EMPTY, FORALL_ONE,
                             genind_exists, LIST_REL_CONS1, LIST_REL_NIL1]
               |> Q.INST [`Q` |-> `λt. P (term_ABS t)`]
               |> SIMP_RULE std_ss [GSYM LAM_def, APP_def', GSYM VAR_def,
                                    CONJUNCT1 term_ABSREP]
               |> elim_unnecessary_atoms
               |> genit |> DISCH_ALL |> Q.GEN `fv` |> Q.GEN `P`

fun mkX_ind th = th |> Q.SPEC `λt x. Q t` |> Q.SPEC `λx. X`
                    |> SIMP_RULE std_ss [] |> Q.GEN `X`
                    |> Q.INST [`Q` |-> `P`] |> Q.GEN `P`

val term_Xind = mkX_ind term_ind

val term_REP_eqv = prove(
   ``support (fnpm tpm gtpm) term_REP {}`` ,
   srw_tac [][support_def, fnpm_def, FUN_EQ_THM, term_REP_tpm, gtpm_sing_inv]);

val supp_term_REP = prove(
  ``supp (fnpm tpm gtpm) term_REP = {}``,
  REWRITE_TAC [GSYM SUBSET_EMPTY] >> MATCH_MP_TAC (GEN_ALL supp_smallest) >>
  srw_tac [][gtpm_is_perm, tpm_is_perm, term_REP_eqv])

val supptpm_support = prove(
  ``support tpm t (supp gtpm (term_REP t))``,
  srw_tac [][support_def, tpm_def, gtpm_fresh, GFV_supp, term_ABSREP]);

val supptpm_apart = prove(
  ``x ∈ supp gtpm (term_REP t) ∧ y ∉ supp gtpm (term_REP t) ⇒
    tpm [(x,y)] t ≠ t``,
  srw_tac [][tpm_def, GFV_supp]>>
  DISCH_THEN (MP_TAC o Q.AP_TERM `term_REP`) >>
  srw_tac [][repabs_id, genind_gtpm_eqn, genind_term_REP, GFV_apart]);

val supp_tpm = prove(
  ``supp tpm t = supp gtpm (term_REP t)``,
  match_mp_tac (GEN_ALL supp_unique_apart) >>
  srw_tac [][supptpm_support, supptpm_apart, GFV_supp, FINITE_GFV, tpm_is_perm])

val FINITE_FV = store_thm(
  "FINITE_FV",
  ``FINITE (FV t)``,
  srw_tac [][supp_tpm, GFV_supp, FINITE_GFV]);
val _ = export_rewrites ["FINITE_FV"]


val _ = overload_on ("FV", ``supp tpm``)
fun supp_clause contermP con_def = let
  val t = mk_comb(``FV``, lhand (concl (SPEC_ALL con_def)))
in
  t |> SIMP_CONV (srw_ss()) [supp_tpm, con_def, repabs_id, contermP,
                             GFV_supp, GFV_thm]
    |> SIMP_RULE (srw_ss()) [GSYM GFV_supp, GSYM supp_tpm]
    |> GEN_ALL
end

val supp_tpm_thm =
    LIST_CONJ
    [supp_clause VAR_termP VAR_def,
     supp_clause APP_termP APP_def,
     supp_clause LAM_termP LAM_def]

fun tpm_clause contermP con_def =
  con_def |> SPEC_ALL
          |> Q.AP_TERM `tpm pi`
          |> CONV_RULE (RAND_CONV (SIMP_CONV bool_ss [tpm_def]))
          |> SIMP_RULE std_ss [repabs_id, contermP, gtpm_thm, listTheory.MAP]
          |> SIMP_RULE bool_ss [GSYM con_def, GSYM term_REP_tpm]
          |> GEN_ALL

val tpm_thm =
    LIST_CONJ [tpm_clause VAR_termP VAR_def,
               tpm_clause APP_termP (GSYM APP_def'),
               tpm_clause LAM_termP LAM_def]

val recax = recursion_axiom

val (tmty, gtty) = dom_rng (type_of ``term_REP``)
val gtty' = ty_antiq gtty

val tlf =
  ``λ(v:string) (u:unit + unit) (ds1:α list) (ts1:^gtty' list)
     (ds2:α list) (ts2:^gtty' list).
       if ISL u then tlf v (HD ds1) (term_ABS (HD ts1)) : α
       else taf (HD ds2) (term_ABS (HD ts2))
                (HD (TL ds2)) (term_ABS (HD (TL ts2))) : α``
val tvf = ``λ(s:string) (u:unit). tvf s : α``

val LENGTH_NIL' =
    CONV_RULE (BINDER_CONV (LAND_CONV (REWR_CONV EQ_SYM_EQ)))
              listTheory.LENGTH_NIL
val LENGTH1 = prove(
  ``(1 = LENGTH l) ⇔ ∃e. l = [e]``,
  Cases_on `l` >> srw_tac [][listTheory.LENGTH_NIL]);
val LENGTH2 = prove(
  ``(2 = LENGTH l) ⇔ ∃a b. l = [a;b]``,
  Cases_on `l` >> srw_tac [][LENGTH1]);

val termP_elim = prove(
  ``(∀g. termP g ⇒ P g) ⇔ (∀t. P (term_REP t))``,
  srw_tac [][EQ_IMP_THM] >- srw_tac [][genind_term_REP] >>
  first_x_assum (qspec_then `term_ABS g` mp_tac) >>
  srw_tac [][repabs_id]);

fun ELIM_HERE t = let
  val (v,body) = dest_forall t
  val (h,c) = dest_imp body
in
  BINDER_CONV (LAND_CONV
                   (markerLib.move_conj_left (aconv (mk_comb(termP, v)))) THENC
               REWR_CONV (GSYM AND_IMP_INTRO) THENC
               RAND_CONV (UNBETA_CONV v)) THENC
  REWR_CONV termP_elim THENC BINDER_CONV BETA_CONV THENC
  PURE_REWRITE_CONV [CONJUNCT1 term_ABSREP, GSYM tpm_def]
end t

fun termP_removal t = let
  val (v, body) = dest_forall t
in
  if  Type.compare(type_of v, gtty) = EQUAL then
    (SWAP_FORALL_CONV THENC BINDER_CONV termP_removal) ORELSEC
    ELIM_HERE
  else NO_CONV
end t

val sub_cpos = SUBSET_DEF |> SPEC_ALL
                          |> REWRITE_RULE [ASSUME ``s:'a set ⊆ t``]
                          |> SPEC_ALL
                          |> CONV_RULE CONTRAPOS_CONV
                          |> DISCH_ALL
                          |> CONV_RULE (REWR_CONV AND_IMP_INTRO)
                          |> GEN_ALL

val APP_FCB = prove(
  ``is_perm dpm ∧ FINITE A ∧
    (∀x y a b t1 t2.
      x ∉ A ∧ y ∉ A ⇒
      (dpm [(x,y)] (taf a t1 b t2) =
       taf (dpm [(x,y)] a) (tpm [(x,y)] t1) (dpm [(x,y)] b)
           (tpm [(x,y)] t2))) ⇒
    ∀a r1 r2 t2 t1.
       a ∉ A ∧ a ∉ FV t1 ∧ a ∉ FV t2 ∧ a ∉ supp dpm r1 ∧
       a ∉ supp dpm r2 ⇒ a ∉ supp dpm (taf r1 t1 r2 t2)``,
  srw_tac [][] >>
  `FINITE (supp dpm r1) ∧ FINITE (supp dpm r2)`
     by (CONJ_TAC >> match_mp_tac (MP_CANON supp_absence_FINITE) >>
         srw_tac [][]) >>
  qsuff_tac `support dpm (taf r1 t1 r2 t2)
               (A ∪ FV t1 ∪ FV t2 ∪ supp dpm r1 ∪ supp dpm r2)`
  >- (strip_tac >> match_mp_tac sub_cpos >>
      qexists_tac `A ∪ FV t1 ∪ FV t2 ∪ supp dpm r1 ∪ supp dpm r2` >>
      srw_tac [][] >> match_mp_tac (GEN_ALL supp_smallest) >>
      srw_tac [][]) >>
  srw_tac [][support_def, supp_fresh]);

val stage1 =
    recax
        |> INST_TYPE [alpha |-> ``:unit + unit``, beta |-> ``:unit``,
                      gamma |-> alpha]
        |> Q.INST [`lf` |-> `^tlf`, `vf` |-> `^tvf`, `vp` |-> `^vp`,
                   `lp` |-> `^lp`, `n` |-> `0`]
        |> SIMP_RULE (srw_ss()) [sumTheory.FORALL_SUM, FORALL_AND_THM,
                                 GSYM RIGHT_FORALL_IMP_THM, IMP_CONJ_THM,
                                 LIST_REL_NIL1, LIST_REL_CONS1,
                                 LENGTH_NIL', LENGTH1, LENGTH2]
        |> SIMP_RULE (srw_ss() ++ DNF_ss) [LENGTH1, LENGTH2,
                                           listTheory.LENGTH_NIL]
        |> CONV_RULE (DEPTH_CONV termP_removal)
        |> SIMP_RULE (srw_ss()) [GSYM supp_tpm, UNDISCH APP_FCB]
        |> UNDISCH
        |> rpt_hyp_dest_conj

val hconcl = stage1 |> concl |> dest_exists |> #2

val _ = augment_srw_ss [rewrites [REWRITE_RULE [SYM GFV_supp] FINITE_GFV]]

val myh = prove(
  ``^hconcl ==> FINITE A ==>
    ∃hh.
      (∀s. hh (VAR s) = tvf s) ∧
      (∀t1 t2. hh (APP t1 t2) = taf (hh t1) t1 (hh t2) t2) ∧
      (∀v t. v ∉ A ⇒ (hh (LAM v t) = tlf v (hh t) t))``,
  rpt strip_tac >> qexists_tac `h o term_REP` >>
  asm_simp_tac (srw_ss()) [VAR_def, repabs_id, VAR_termP] >>
  srw_tac [][] >| [
    Q_TAC (NEWLib.NEW_TAC "z") `A ∪ FV t1 ∪ FV t2`>>
    SUBST_ALL_TAC (SYM (Q.INST [`v` |-> `z`] APP_def')) >>
    first_x_assum (qspecl_then [`()`, `z`, `t2`, `t1`] mp_tac) >>
    asm_simp_tac (srw_ss()) [repabs_id, APP_termP, genind_term_REP,
                             term_ABSREP],

    srw_tac [][LAM_def, repabs_id, LAM_termP, genind_term_REP, term_ABSREP]
  ]) |> UNDISCH_ALL

val stage2 = CHOOSE (#1 (dest_exists (concl stage1)), stage1) myh

val term_recursion = save_thm(
  "term_recursion",
  stage2 |> DISCH_ALL
         |> REWRITE_RULE [AND_IMP_INTRO, GSYM CONJ_ASSOC]
         |> SIMP_RULE (bool_ss ++ boolSimps.CONJ_ss) [])





