(* ========================================================================== *)
(* FILE    : nomdatatype.sml                                                  *)
(* TITLE   : Nominal datatype package                                         *)
(*                                                                            *)
(* AUTHORS : 2005-2011 Michael Norrish                                        *)
(*           2026      Chun Tian                                              *)
(* ========================================================================== *)

structure nomdatatype :> nomdatatype =
struct

open HolKernel Parse boolLib bossLib;
open binderLib generic_termsTheory nomsetTheory;

type coninfo = {con_termP : thm, con_def : thm}

val cpm_ty = let val sty = stringSyntax.string_ty
             in
               listSyntax.mk_list_type (pairSyntax.mk_prod (sty, sty))
             end

fun list_mk_icomb(f, args) = List.foldl (mk_icomb o swap) f args

(* utility functions *)
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

val FINITE_t = mk_thy_const{Name = "FINITE", Thy = "pred_set",
                            Ty = (stringSyntax.string_ty --> bool) --> bool}

fun elim_unnecessary_atoms {finite_fv} fths = let
  fun mainconv t = let
    val (vs, bod) = strip_forall t
    val (v,rest) = case vs of
                     [] => raise mk_HOL_ERR "nomdatatype" "elim_unnecessary_atoms"
                                            "Not a forall"
                   | v::vs => (v,vs)
    val _ = Type.compare(type_of v, stringSyntax.string_ty) = EQUAL orelse
            raise mk_HOL_ERR "nomdatatype" "elim_unnecessary_atoms"
                             "Forall not of an atom"
    val (h, c) = dest_imp bod
    val _ = free_in v h andalso not (free_in v c) orelse
            raise mk_HOL_ERR "nomdatatype" "elim_unnecessary_atoms"
                             "Uneliminable atom"
    fun PROVE_FINITE t = let
      open pred_setTheory pred_setSyntax
      val (v, bod) = dest_exists t
      val cs = strip_conj bod
      fun getset t = let
        val t0 = dest_neg t
      in
        if is_in t0 then rand t0 else mk_set [rhs t0]
      end
      val sets = map getset cs
      val union = List.foldl (mk_union o swap) (hd sets) (tl sets)
      val finite_t = mk_finite union
      val finite_th =
        REWRITE_CONV (FINITE_UNION::FINITE_INSERT::FINITE_EMPTY::finite_fv::fths)
                     finite_t
      val fresh_exists = MATCH_MP basic_swapTheory.new_exists (EQT_ELIM finite_th)
                                  |> REWRITE_RULE [IN_UNION, IN_INSERT, NOT_IN_EMPTY,
                                                   DE_MORGAN_THM, GSYM CONJ_ASSOC]
    in
      EQT_INTRO fresh_exists
    end

    val base = HO_REWR_CONV LEFT_FORALL_IMP_THM THENC
               LAND_CONV (((CHANGED_CONV EXISTS_AND_REORDER_CONV THENC
                            RAND_CONV PROVE_FINITE) ORELSEC
                           PROVE_FINITE)) THENC
               REWRITE_CONV []
    fun recurse t = ((SWAP_FORALL_CONV THENC BINDER_CONV recurse) ORELSEC base) t
  in
    recurse
  end t
in
  CONV_RULE (ONCE_DEPTH_CONV mainconv)
end

val gterm_ty = mk_thy_type {Thy = "generic_terms", Tyop = "gterm",
                            Args = [alpha]}

local
  val num_ty = numSyntax.num
  val numlist_ty = listSyntax.mk_list_type num_ty
  val string_ty = stringSyntax.string_ty
in
val genind_t =
  mk_thy_const {Thy = "generic_terms", Name = "genind",
                Ty = (num_ty --> num_ty --> alpha --> numlist_ty -->
                      numlist_ty --> bool) -->
                     num_ty --> gterm_ty --> bool}
end

fun first2 l =
    case l of
      (x::y::_) => (x,y)
    | _ => raise Fail "first2: list doesn't have at least two elements"

(* NOTE: In case multiple mutually recursive nominal types are being defined,
  "witnesses" argument takes a list of [genind_exists] theorems generated from
   previous calls to the current function, otherwise the proof of term_exists
   may not succeed.
 *)
type nomtyinfo = {term_ABS_pseudo11 : thm,
                        term_REP_11 : thm,
                        term_REP_t : term,
                        term_ABS_t : term,
                        absrep_id : thm,
                        repabs_pseudo_id : thm,
                        genind_term_REP : thm,
                        genind_exists : thm,
                        newty : hol_type,
                        termP : term};

fun new_type_step1 tyname n witnesses {lp} :nomtyinfo = let
  val list_mk_icomb = uncurry (List.foldl (mk_icomb o swap))
  val termP =
      list_mk_icomb (genind_t, [lp,numSyntax.mk_numeral (Arbnum.fromInt n)])
  fun termPf x = mk_comb(termP, x)
  val (gtty,_) = dom_rng (type_of termP)
  val x = mk_var("x",gtty) and y = mk_var("y", gtty)
  val glam_ty = #2 (dest_type gtty)
  val term_exists =
      prove(mk_exists(x, mk_comb(termP, x)),
            ((* hope type uses GLAM in base-case way *)
             irule_at (Pos hd) genind_rules THEN
             simpLib.SIMP_TAC (list_ss ++ boolSimps.DNF_ss) [] THEN
             simpLib.SIMP_TAC list_ss [sumTheory.EXISTS_SUM, EXISTS_OR_THM,
                                       listTheory.LENGTH_EQ_NUM_compute] THEN
             simpLib.SIMP_TAC list_ss witnesses))
  val {absrep_id, newty, repabs_pseudo_id, termP, termP_exists, termP_term_REP,
       term_ABS_t, term_ABS_pseudo11,
       term_REP_t, term_REP_11} =
      newtypeTools.rich_new_type {tyname = tyname, exthm = term_exists,
                                  ABS = tyname ^ "_ABS",
                                  REP = tyname ^ "_REP"}
in
  {term_ABS_pseudo11 = term_ABS_pseudo11, term_REP_11 = term_REP_11,
   term_REP_t = term_REP_t, term_ABS_t = term_ABS_t, absrep_id = absrep_id,
   repabs_pseudo_id = repabs_pseudo_id, genind_term_REP = termP_term_REP,
   genind_exists = termP_exists, newty = newty, termP = termP}
end

fun termP_removal (info as {elimth,absrep_id,tpm_def,termP,repty}) t = let
  val (v, body) = dest_forall t
  fun ELIM_HERE t = let
    val (v,body) = dest_forall t
    val (h,c) = dest_imp body
  in
    BINDER_CONV (LAND_CONV
                     (markerLib.move_conj_left (aconv (mk_comb(termP, v)))) THENC
                     TRY_CONV (REWR_CONV (GSYM AND_IMP_INTRO)) THENC
                     RAND_CONV (UNBETA_CONV v)) THENC
    REWR_CONV elimth THENC BINDER_CONV BETA_CONV THENC
    PURE_REWRITE_CONV [absrep_id, GSYM tpm_def]
  end t

in
  if Type.compare(type_of v, repty) = EQUAL then
    (SWAP_FORALL_CONV THENC BINDER_CONV (termP_removal info)) ORELSEC
    ELIM_HERE
  else NO_CONV
end t

fun lift_exfunction {repabs_pseudo_id, term_REP_t, cons_info} th = let
  fun mk_conremove {con_termP, con_def} =
      con_termP |> MATCH_MP repabs_pseudo_id
                |> CONV_RULE (LAND_CONV (RAND_CONV (REWR_CONV (GSYM con_def))))
                |> SYM
  val conremoves = map mk_conremove cons_info
  val f_REP_o = let
    val (d,r) = dom_rng (type_of term_REP_t)
    val f = mk_var("f", r --> Type.gen_tyvar())
    val x = mk_var("x", d)
  in
    prove(
      mk_eq(mk_comb(f, mk_comb(term_REP_t, x)),
            mk_comb(combinSyntax.mk_o(f, term_REP_t), x)),
      CONV_TAC (RAND_CONV (REWR_CONV combinTheory.o_THM)) THEN REFL_TAC)
  end

  fun fREPo_CONV t = let
    val (v, bod) = dest_exists t
    val o_t = combinSyntax.o_tm |> inst [alpha |-> Type.gen_tyvar()]
    val fREPo = list_mk_icomb(o_t, [v, term_REP_t])
  in
    BINDER_CONV (UNBETA_CONV fREPo) t
  end

  fun elimfREPo th = let
    val (v,bod) = dest_exists (concl th)
    val (vnm, _) = dest_var v
    val bod_th = ASSUME bod
    val (P, arg) = dest_comb bod
    val newf = mk_var(vnm, type_of arg)
    val newbod = mk_comb(P, newf)
  in
    CHOOSE (v, th) (EXISTS (mk_exists(newf, newbod), arg) bod_th)
           |> CONV_RULE (BINDER_CONV BETA_CONV)
  end
in
  th |> REWRITE_RULE (f_REP_o::conremoves)
     |> CONV_RULE fREPo_CONV
     |> elimfREPo
end

fun sort_uvars t = let
  val (v, bod) = dest_forall t
  val (v', _) = dest_forall bod
  val (nm1, ty1) = dest_var v
  val (nm2, ty2) = dest_var v'
  fun tycmp (ty1,ty2) =
      if Type.compare(ty1,ty2) = EQUAL then EQUAL
      else if Type.compare(ty1,``:string``) = EQUAL then LESS
      else if is_vartype ty2 andalso not (is_vartype ty1) then LESS
      else Type.compare(ty1, ty2)
in
  if pair_compare(tycmp,String.compare) ((ty1,nm1), (ty2,nm2)) = GREATER then
    SWAP_FORALL_CONV
  else NO_CONV
end t

fun rename_vars alist t = let
  val (bv, _) = dest_abs t
  val (v, _) = dest_var bv
in
  case Lib.total (Lib.assoc v) alist of
    NONE => NO_CONV
  | SOME v' => RENAME_VARS_CONV [v']
end t

fun gen_tactics rwts [] : tactic = ALL_TAC
  | gen_tactics rwts (ppm::xs) =
    match_mp_tac (GEN_ALL notinsupp_fnapp) \\
    EXISTS_TAC ppm \\
    srw_tac [] rwts \\
    gen_tactics rwts xs;

fun prove_alpha_fcbhyp {ppms, alphas, rwts} th = let
  open nomsetTheory
  val th = rpt_hyp_dest_conj (UNDISCH th)
  val tac = gen_tactics rwts ppms
  fun foldthis (h,th) = let
    val h_th =
      TAC_PROOF(([], h),
                rpt gen_tac >> strip_tac >>
                FIRST (map (match_mp_tac o GSYM) alphas) >> tac)
  in
    PROVE_HYP h_th th
  end
in
  HOLset.foldl foldthis th (hypset th)
end

val pi_t = mk_var("pi", cpm_ty)
val pmact_t = prim_mk_const{Name = "pmact", Thy = "nomset"}
val mk_pmact_t = prim_mk_const{Name = "mk_pmact", Thy = "nomset"}
val raw_gtpm_t =
    mk_thy_const{Name = "raw_gtpm", Thy = "generic_terms",
                 Ty = cpm_ty --> gterm_ty --> gterm_ty}
val gtpm_t = mk_icomb(pmact_t, mk_icomb(mk_pmact_t, raw_gtpm_t))

fun defined_const th = th |> concl |> strip_forall |> #2 |> lhs |> repeat rator

val pmact_absrep' = pmact_bijections |> CONJUNCT2 |> GSYM

fun Save_thm(n, th) = save_thm(n,th) before BasicProvers.export_rewrites [n]

fun define_permutation { name_pfx, name, term_ABS_t, term_REP_t,
                         absrep_id, repabs_pseudo_id, newty,
                         genind_term_REP, cons_info} = let
  val tpm_name = name_pfx ^ "pm"
  val raw_tpm_name = "raw_" ^ tpm_name
  val raw_tpm_t = mk_var(raw_tpm_name, cpm_ty --> newty --> newty)
  val t = mk_var("t", newty)
  val raw_tpm_def = new_definition(
    raw_tpm_name ^ "_def",
    mk_eq(list_mk_comb(raw_tpm_t, [pi_t, t]),
          mk_comb(term_ABS_t,
                  list_mk_icomb(gtpm_t, [pi_t, mk_comb(term_REP_t, t)]))))
  val raw_tpm_t = defined_const raw_tpm_def
  val t_pmact_name = name ^ "_pmact"
  val t_pmact_t = mk_icomb(mk_pmact_t, raw_tpm_t)
  val tpm_t = mk_icomb(pmact_t, t_pmact_t)
  val _ = overload_on (t_pmact_name, t_pmact_t)
  val _ = overload_on (tpm_name, tpm_t)
  val (termP_t, REPg) = dest_comb (concl genind_term_REP)
  val termP_gtpmREP =
      mk_comb(termP_t, list_mk_icomb(gtpm_t, [pi_t, REPg]))
             |> PURE_REWRITE_CONV [genind_gtpm_eqn]
             |> SYM |> C EQ_MP genind_term_REP
  val term_REP_raw_tpm =
      raw_tpm_def |> SPEC_ALL |> AP_TERM term_REP_t
                  |> PURE_REWRITE_RULE [MATCH_MP repabs_pseudo_id termP_gtpmREP]
  val tpm_raw = store_thm(
    tpm_name ^ "_raw",
    mk_eq(tpm_t, raw_tpm_t),
    REWRITE_TAC[pmact_absrep', is_pmact_def, FUN_EQ_THM, raw_tpm_def,
                pmact_nil, pmact_decompose, absrep_id] THEN
    REPEAT CONJ_TAC THENL [
      REPEAT GEN_TAC THEN
      NTAC 2 AP_TERM_TAC THEN CONV_TAC (REWR_CONV EQ_SYM_EQ) THEN
      REWRITE_TAC [GSYM term_REP_raw_tpm, absrep_id],
      REPEAT STRIP_TAC THEN
      AP_TERM_TAC THEN AP_THM_TAC THEN
      Q.ISPEC_THEN `gtpm`     (fn is_pmact_def =>
      Q.ISPEC_THEN `gt_pmact` (fn is_pmact_pmact =>
        is_pmact_def |> C EQ_MP is_pmact_pmact
                     |> CONJUNCTS |> last
                     |> MATCH_MP_TAC) is_pmact_pmact) is_pmact_def THEN
      POP_ASSUM ACCEPT_TAC
    ])
  val term_REP_tpm = SUBS [GSYM tpm_raw] term_REP_raw_tpm
  fun tpm_clause {con_termP, con_def} =
      con_def |> SPEC_ALL
              |> AP_TERM (mk_comb(tpm_t, pi_t))
              |> CONV_RULE (RAND_CONV (REWR_CONV
                                           (SUBS [GSYM tpm_raw] raw_tpm_def)))
              |> REWRITE_RULE [MATCH_MP repabs_pseudo_id con_termP,
                               gtpm_thm, listTheory.MAP, listpm_thm]
              |> REWRITE_RULE [GSYM con_def, GSYM term_REP_tpm]
              |> GEN_ALL
  val tpm_thm = Save_thm(tpm_name ^ "_thm",
                         LIST_CONJ (map tpm_clause cons_info))
in
  {term_REP_tpm = term_REP_tpm, tpm_thm = tpm_thm, t_pmact_t = t_pmact_t,
   tpm_t = tpm_t}
end

(* ----------------------------------------------------------------------
    The "Nominal_datatype" API
   ---------------------------------------------------------------------- *)

open ParseDatatype numSyntax listSyntax;

(*
val q = ‘term = VAR 'free | APP term term | LAM 'bound term’;
val asts = ParseDatatype.hparse (type_grammar()) q;
   [("term",
     Constructors
      [("VAR", [dVartype "'free"]),
       ("APP",
        [dTyop {Args = [], Thy = NONE, Tyop = "term"},
         dTyop {Args = [], Thy = NONE, Tyop = "term"}]),
       ("LAM",
        [dVartype "'bound", dTyop {Args = [], Thy = NONE, Tyop = "term"}])])]

val q = ‘cterm = VAR 'free | APP cterm cterm | LAM 'bound cterm | CONST 'a’;
val asts = ParseDatatype.hparse (type_grammar()) q;
   [("cterm",
     Constructors
      [("VAR", [dVartype "'free"]),
       ("APP",
        [dTyop {Args = [], Thy = SOME "term", Tyop = "term"},
         dTyop {Args = [], Thy = SOME "term", Tyop = "term"}]),
       ("LAM",
        [dVartype "'bound",
         dTyop {Args = [], Thy = SOME "term", Tyop = "term"}]),
       ("CONST", [dVartype "'a"])])]

val q = ‘lterm = VAR 'free
               | APP lterm lterm
               | LAM 'bound lterm
               | LAMi num 'bound lterm lterm’;
val asts = ParseDatatype.hparse (type_grammar()) q;
   [("lterm",
     Constructors
      [("VAR", [dVartype "'free"]),
       ("APP",
        [dTyop {Args = [], Thy = NONE, Tyop = "lterm"},
         dTyop {Args = [], Thy = NONE, Tyop = "lterm"}]),
       ("LAM",
        [dVartype "'bound", dTyop {Args = [], Thy = NONE, Tyop = "lterm"}]),
       ("LAMi",
        [dTyop {Args = [], Thy = SOME "num", Tyop = "num"},
         dVartype "'bound", dTyop {Args = [], Thy = NONE, Tyop = "lterm"},
         dTyop {Args = [], Thy = NONE, Tyop = "lterm"}])])]

val q =  ‘CCS = var 'free
              | prefix ('a Action) CCS
              | sum CCS CCS
              | par CCS CCS
              | restr ('a Label set) CCS
              | relab CCS ('a Relabeling)
              | rec 'bound CCS’;
val asts = ParseDatatype.hparse (type_grammar()) q;
   [("CCS",
     Constructors
      [("var", [dVartype "'free"]),
       ("prefix",
        [dTyop {Args = [dVartype "'a"], Thy = NONE, Tyop = "Action"},
         dTyop {Args = [], Thy = NONE, Tyop = "CCS"}]),
       ("sum",
        [dTyop {Args = [], Thy = NONE, Tyop = "CCS"},
         dTyop {Args = [], Thy = NONE, Tyop = "CCS"}]),
       ("par",
        [dTyop {Args = [], Thy = NONE, Tyop = "CCS"},
         dTyop {Args = [], Thy = NONE, Tyop = "CCS"}]),
       ("restr",
        [dTyop
          {Args =
           [dTyop {Args = [dVartype "'a"], Thy = NONE, Tyop = "Label"},
            dTyop {Args = [], Thy = SOME "min", Tyop = "bool"}], Thy =
           SOME "min", Tyop = "fun"},
         dTyop {Args = [], Thy = NONE, Tyop = "CCS"}]),
       ("relab",
        [dTyop {Args = [], Thy = NONE, Tyop = "CCS"},
         dTyop {Args = [dVartype "'a"], Thy = NONE, Tyop = "Relabeling"}]),
       ("rec",
        [dVartype "'bound", dTyop {Args = [], Thy = NONE, Tyop = "CCS"}])])]

  val q = ‘pi   = Nil                         (* 0 *)
                | Tau pi                      (* tau.P *)
                | Input 'free 'bound pi       (* a(x).P *)
                | Output 'free 'free pi       (* {a}b.P *)
                | Match 'free 'free pi        (* [a == b] P *)
                | Mismatch 'free 'free pi     (* [a <> b] P *)
                | Sum pi pi                   (* P + Q *)
                | Par pi pi                   (* P | Q *)
                | Res 'bound pi               (* nu x. P *)
                ;
       residual = TauR pi
                | InputS 'free 'bound pi      (* Input *)
                | BoundOutput 'free 'bound pi (* Bound output *)
                | FreeOutput 'free 'free pi   (* Free output *)’;
  val asts = ParseDatatype.hparse (type_grammar()) q;
   [("pi",
     Constructors
      [("Nil", []), ("Tau", [dTyop {Args = [], Thy = NONE, Tyop = "pi"}]),
       ("Input",
        [dVartype "'free", dVartype "'bound",
         dTyop {Args = [], Thy = NONE, Tyop = "pi"}]),
       ("Output",
        [dVartype "'free", dVartype "'free",
         dTyop {Args = [], Thy = NONE, Tyop = "pi"}]),
       ("Match",
        [dVartype "'free", dVartype "'free",
         dTyop {Args = [], Thy = NONE, Tyop = "pi"}]),
       ("Mismatch",
        [dVartype "'free", dVartype "'free",
         dTyop {Args = [], Thy = NONE, Tyop = "pi"}]),
       ("Sum",
        [dTyop {Args = [], Thy = NONE, Tyop = "pi"},
         dTyop {Args = [], Thy = NONE, Tyop = "pi"}]),
       ("Par",
        [dTyop {Args = [], Thy = NONE, Tyop = "pi"},
         dTyop {Args = [], Thy = NONE, Tyop = "pi"}]),
       ("Res",
        [dVartype "'bound", dTyop {Args = [], Thy = NONE, Tyop = "pi"}])]),
    ("residual",
     Constructors
      [("TauR", [dTyop {Args = [], Thy = NONE, Tyop = "pi"}]),
       ("InputS",
        [dVartype "'free", dVartype "'bound",
         dTyop {Args = [], Thy = NONE, Tyop = "pi"}]),
       ("BoundOutput",
        [dVartype "'free", dVartype "'bound",
         dTyop {Args = [], Thy = NONE, Tyop = "pi"}]),
       ("FreeOutput",
        [dVartype "'free", dVartype "'free",
         dTyop {Args = [], Thy = NONE, Tyop = "pi"}])])]
 *)

fun parse_datatype q = hparse (type_grammar()) q;

(* ["pi", "residual"] *)
fun extract_tynames (asts :AST list) = List.map fst asts;

(* ["Nil", "Tau", "Input", "Output", "Match", "Mismatch", "Sum", "Par",
    "Res", "TauR", "InputS", "BoundOutput", "FreeOutput"] *)
fun constructor_and_types (asts :AST list) =
    List.concat (List.map (fn (_,df) =>
                              case df of
                                  Constructors cs => cs
                                | Record _ => []) asts);

fun constructors (asts :AST list) = List.map fst (constructor_and_types asts);

(* The special type variables 'free and 'bound (by default) are free and bound
   names occurred in the nominal types being defined.

   NOTE: Due to Datatype syntax restriction, each constructor supports at most
   one bound name argument, and if it has two (or more) recursive term arguments,
   only one (the first) is considered bounded. For instance, in labelled lambda
   terms (lterm), we have the constructor ‘LAMi num 'bound lterm lterm’, which
   actually means an application ‘(LAMi num 'bound lterm) @@ lterm’, where the
   first lterm is bounded (by the name in the position of 'bound), while the
   second lterm is not bounded by that name.
 *)
val free_tyname  = ref "'free";
val bound_tyname = ref "'bound";

(* NOTE: This variant of pretypeToType returns only external types. Outputs for
   "dAQ pty" is meaningless (not supported).
 *)
fun pretypeToType1 pty =
  case pty of
    dVartype s => if s = !free_tyname orelse s = !bound_tyname then
                      NONE
                  else
                      SOME (Type.mk_vartype s)
  | dTyop {Tyop = s, Thy, Args} => let
    in
      case Thy of
        NONE => NONE (* This is referring to nominal types being defined *)
      | SOME t => SOME (Type.mk_thy_type{Tyop = s, Thy = t,
                                         Args = List.map pretypeToType Args})
    end
  | dAQ pty => SOME pty;

fun constructor_types (asts) =
    List.concat (List.map snd (constructor_and_types asts));

fun external_types (asts) =
    List.map Option.valOf
             (List.filter Option.isSome
                          (List.map pretypeToType1 (constructor_types asts)));

(* no leading ":" but with parenthesis, e.g. ('a Action) *)
fun type_to_string1 ty =
    let val s = type_to_string ty;
        val n = String.size s;
    in
        "(" ^ substring (s,1,n-1) ^ ")"
    end;

val external_type_vars = type_varsl o external_types;

val repcode = ref "";
val rprefix = ref "r";

(* e.g., ("cprefix", [``:'a Action``]) *)
fun repcode_pair (n,df) =
    (!rprefix ^ n,
     List.map Option.valOf
              (List.filter Option.isSome (List.map pretypeToType1 df)));

fun repcode_line (n,types) =
    [QUOTE n] @ (List.map (QUOTE o type_to_string1) types);

(* This function generates the term quotation and call it by Datatype, e.g.
Datatype:
  repcode = rNil | rTau | rInput | rOutput | rMatch | rMismatch | rSum
          | rPar | rRes | rTauR | rInputS | rBoundOutput | rFreeOutput
End
Datatype:
  crep = cvar
       | cprefix ('a Action) | csum | cpar
       | crestr ('a Label set)
       | crelab ('a Relabeling)
       | crec
End
 *)
fun define_repcode (asts :AST list) = let
    val lines = List.map repcode_pair (constructor_and_types asts);
    val tynames = extract_tynames asts;
    val repname = if !repcode = "" then (hd tynames) ^ "_repcode"
                  else !repcode;
    val dtype0 = [QUOTE repname] @ ‘=’ @ repcode_line (hd lines);
    val dtype1 = dtype0 @
                 List.concat (List.map (fn s => ‘|’ @ repcode_line s) (tl lines));
    val types = external_type_vars asts;
in
    (Datatype dtype1; mk_type (repname, types))
end;

(*
Example 1 (multiple types; mixed free and bound names in the same constructor):

  val q = ‘pi   = Nil                         (* 0 *)
                | Tau pi                      (* tau.P *)
                | Input 'free 'bound pi       (* a(x).P *)
                | Output 'free 'free pi       (* {a}b.P *)
                | Match 'free 'free pi        (* [a == b] P *)
                | Mismatch 'free 'free pi     (* [a <> b] P *)
                | Sum pi pi                   (* P + Q *)
                | Par pi pi                   (* P | Q *)
                | Res 'bound pi               (* nu x. P *)
                ;
       residual = TauR pi
                | InputS 'free 'bound pi      (* Input *)
                | BoundOutput 'free 'bound pi (* Bound output *)
                | FreeOutput 'free 'free pi   (* Free output *)’;
val asts = ParseDatatype.hparse (type_grammar()) q;
val lp =
  “(\n lfvs d tns uns.
     n = 0 /\ lfvs = 0 /\ d = rNil /\ tns = [] /\ uns = [] \/
     n = 0 /\ lfvs = 0 /\ d = rTau /\ tns = [] /\ uns = [0] \/
     n = 0 /\ lfvs = 1 /\ d = rInput /\ tns = [0] /\ uns = [] \/
     n = 0 /\ lfvs = 2 /\ d = rOutput /\ tns = [] /\ uns = [0] \/
     n = 0 /\ lfvs = 2 /\ d = rMatch /\ tns = [] /\ uns = [0] \/
     n = 0 /\ lfvs = 2 /\ d = rMismatch /\ tns = [] /\ uns = [0] \/
     n = 0 /\ lfvs = 0 /\ d = rSum /\ tns = [] /\ uns = [0; 0] \/
     n = 0 /\ lfvs = 0 /\ d = rPar /\ tns = [] /\ uns = [0; 0] \/
     n = 0 /\ lfvs = 0 /\ d = rRes /\ tns = [1] /\ uns = [] \/

     n = 1 /\ lfvs = 0 /\ d = rTauR /\ tns = [] /\ uns = [0] \/
     n = 1 /\ lfvs = 1 /\ d = rInputS /\ tns = [0] /\ uns = [] \/
     n = 1 /\ lfvs = 1 /\ d = rBoundOutput /\ tns = [0] /\ uns = [] \/
     n = 1 /\ lfvs = 2 /\ d = rFreeOutput /\ tns = [] /\ uns = [0]
    )”;

Example 2 (mixed free and bound recursive terms; with external type :num):

val q = ‘lterm = VAR 'free
               | APP lterm lterm
               | LAM 'bound lterm
               | LAMi num 'bound lterm lterm’;
val asts = ParseDatatype.hparse (type_grammar()) q;

val lp = “λn lfvs (d:lrep) tns uns.
            n = 0 /\ lfvs = 1 /\ d = lvar /\ tns = [] /\ uns = [] \/
            n = 0 /\ lfvs = 0 /\ d = lapp /\ tns = [] /\ uns = [0;0] \/
            n = 0 /\ lfvs = 0 /\ d = llam /\ tns = [0] /\ uns = [] \/
            ?m. n = 0 /\ lfvs = 0 /\ d = llmi m /\ tns = [0] /\ uns = [0]”;

  n is the index of (multiple) nominal types being defined
  lfvs is the number of 'free names in the constructor
  d is the repcode of the constructor
  tns is the list of indexes of bounded arguments
  uns is the list of indexes of unbounded (free) arguments.
*)

(* index_of "b" ["a", "b", "c"] = “1 :num” *)
local
    open Arbnum
    fun index_of_inner (n :num) e l =
        if e = hd l orelse tl l = [] then n
        else index_of_inner (n + one) e (tl l);
in
fun index_of e l = numSyntax.mk_numeral (index_of_inner Arbnum.zero e l)
end;

(* NOTE: “lfvs = _” where “_” is the number of “:free” of the constructor *)
fun build_lfvs (ptys) = let
    val i = List.length (List.filter (fn e => e = dVartype (!free_tyname)) ptys)
in
    mk_eq (“lfvs :num”, mk_numeral (Arbnum.fromInt i))
end;

(* find_prev 2 [1,2,3,4,5] = 3 *)
fun find_next e l = if hd l = e then hd (tl l) else find_next e (tl l);

(* NOTE: The "dAQ" contructor is not supported *)
fun pretypeToName pty =
    case pty of
        dVartype s => s
      | dTyop {Tyop = s, Thy, Args} => s
      | dAQ pty => type_to_string pty;

(* filter_this_next 2 [1,2,3,2,5] [] = [3,5] *)
fun filter_this_next e l acc =
    if l = [] then rev acc
    else
        if hd l = e then
            filter_this_next e (tl (tl l)) (hd (tl l)::acc)
        else
            filter_this_next e (tl l) acc;

(* NOTE: We assume there's always one bound nominal parameter after each 'bound
   name. In the existing examples, at most one 'bound is present.

   val ptys = [dVartype "'free", dVartype "'bound",
               dTyop {Args = [], Thy = NONE, Tyop = "pi"}]
   ==> tns = [0]
 *)
fun build_tns ptys tynames = let
    val dv = dVartype (!bound_tyname);
    val bound_args = filter_this_next dv ptys [];
    val indexes = List.map (fn e => index_of (pretypeToName e) tynames)
                           bound_args
in
    mk_eq (“tns :num list”, mk_list (indexes, numSyntax.num))
end;

(* NOTE: The "dAQ" constructor is not supported *)
fun pretypeIsNominal pty =
    case pty of
        dVartype s => false
      | dTyop {Tyop, Thy = thy, Args} => (thy = NONE)
      | dAQ pty => false;

(* filter_out_this_next 2 [1,2,3,4,5] [] = [1,4,5] *)
fun filter_out_this_next e l acc =
    if l = [] then rev acc
    else
        if hd l = e then
            filter_out_this_next e (tl (tl l)) acc
        else
            filter_out_this_next e (tl l) (hd l::acc);

(* The “uns” list contains indexes of all nominal types, excluding the one
   after 'bound (which is put into the “tns” list).
 *)
fun build_uns ptys tynames = let
    val l1 = filter_out_this_next (dVartype (!bound_tyname)) ptys [];
    val l2 = List.filter pretypeIsNominal l1;
    val uns = List.map (fn e => index_of (pretypeToName e) tynames) l2
in
    mk_eq (“uns :num list”, mk_list (uns, numSyntax.num))
end;

(* gen_names 3 [] = ["a0", "a1", "a2"] *)
fun gen_names n acc =
    if n = 0 then acc
    else
        gen_names (n - 1) (("a" ^ Int.toString (n - 1))::acc);

(* NOTE: This function only builds "external" arguments of each constructor. *)
fun build_args ptys = let
    val tys = List.map Option.valOf
                       (List.filter Option.isSome (List.map pretypeToType1 ptys));
    val n = List.length tys; (* could be zero *)
    val names = gen_names n []
in
    List.map mk_var (zip names tys)
end;

fun build_lp_inner cptys tyname tynames = let
    val n_tm = index_of tyname tynames
in
    List.map (fn (c:string,ptys) =>
                 (mk_eq (“n :num”, n_tm),
                  build_lfvs ptys,
                  c,
                  build_args ptys,
                  build_tns ptys tynames,
                  build_uns ptys tynames)) cptys
end;

(* NOTE: For lterm (LabelledTerm), the "LAMi" constructor has two recursive
   parameters, the first is bound (because it's immediately after 'bound), the
   second is free: ‘LAMi num 'bound lterm lterm’.

   We need to make sure the generated tns and uns lists each contain one value:

val data =
   [(``n = 0``, ``lfvs = 1``, "VAR", [], ``tns = []``, ``uns = []``),
    (``n = 0``, ``lfvs = 0``, "APP", [], ``tns = []``, ``uns = [0; 0]``),
    (``n = 0``, ``lfvs = 0``, "LAM", [], ``tns = [0]``, ``uns = []``),
    (``n = 0``, ``lfvs = 0``, "LAMi", [``a0``], ``tns = [0]``, ``uns = [0]``)]:
   (term * term * string * term list * term * term) list
 *)
fun build_lp_data (asts :AST list) = let
    val tynames = extract_tynames asts;
in
    List.concat (List.map (fn (tyname,df) =>
                              case df of
                                  Constructors cs =>
                                  build_lp_inner cs tyname tynames
                                | Record _ => []) asts)
end;

(* “d = _” *)
fun build_d_term cname args rep_t = let
    val rcname = !rprefix ^ cname;
    val argtypes = List.map type_of args;
    val c_ty = list_mk_fun (argtypes, rep_t);
    val c_tm = mk_const (rcname,c_ty);
    val d_tm = list_mk_comb (c_tm, args)
in
    mk_eq (mk_var("d", rep_t), d_tm)
end;

(* val it =
   ``\n lfvs d tns uns.
         n = 0 /\ lfvs = 1 /\ d = rvar /\ tns = [] /\ uns = [] \/
         (?a0. n = 0 /\ lfvs = 0 /\ d = rprefix a0 /\ tns = [] /\ uns = [0]) \/
         n = 0 /\ lfvs = 0 /\ d = rsum /\ tns = [] /\ uns = [0; 0] \/
         n = 0 /\ lfvs = 0 /\ d = rpar /\ tns = [] /\ uns = [0; 0] \/
         (?a0. n = 0 /\ lfvs = 0 /\ d = rrestr a0 /\ tns = [] /\ uns = [0]) \/
         (?a0. n = 0 /\ lfvs = 0 /\ d = rrelab a0 /\ tns = [] /\ uns = [0]) \/
         n = 0 /\ lfvs = 0 /\ d = rrec /\ tns = [0] /\ uns = []``: term
 *)
fun build_lp (asts :AST list) rep_t = let
    (* (n_tm,lfvs_tm,cname,args,tns_tm,uns_tm) *)
    val data = build_lp_data asts;
    val c_tms = List.map
                    (fn (n_tm,lfvs_tm,cname,args,tns_tm,uns_tm) =>
                        list_mk_exists
                            (args,
                             list_mk_conj [n_tm, lfvs_tm,
                                           build_d_term cname args rep_t,
                                           tns_tm, uns_tm])) data;
    val n_tm    = “n :num”
    and lfvs_tm = “lfvs :num”
    and d_tm    = mk_var ("d", rep_t)
    and tns_tm  = “tns :num list”
    and uns_tm  = “uns :num list”
in
    list_mk_abs ([n_tm, lfvs_tm, d_tm, tns_tm, uns_tm], list_mk_disj c_tms)
end;

(* NOTE: When calling "new_type_step1" for next tyname, the genind_exists slot
   of nomtyinfo from previous calls of "new_type_step1", must be supplied.
   This works for pi-calculus but perhaps not works for mutually exclusive types
   that we haven't met yet.
 *)
fun build_tydata [] index lp ths = []
  | build_tydata (tyname::tynames) index lp ths =
    let val tyinfo = new_type_step1 tyname index ths {lp = lp};
        val th = #genind_exists tyinfo
    in
        tyinfo :: build_tydata tynames (index + 1) lp (th :: ths)
    end;

type operinfo  = {oper_termP : thm, oper_def : thm, oper_def' : thm option}

val glam = genind_lam
val toArb = subst [“uu:string” |-> “ARB:string”]

(* Samples:
(* Tau pi *)
val Tau_t = mk_var("Tau", “:^newty1 -> ^newty1”);
val Tau_pattern = “GLAM uu [] rTau [] [^term_REP_t1 P]”;
val Tau_def = new_definition(
   "Tau_def",
  “^Tau_t P = ^term_ABS_t1 ^(toArb Tau_pattern)”);
val Tau_termP = prove(
    mk_comb(termP1, Tau_pattern),
    match_mp_tac glam >> srw_tac [][genind_term_REP1]);
val Tau_t = defined_const Tau_def;
val Tau_def' = prove(
  “^term_ABS_t1 ^Tau_pattern = ^Tau_t P”,
    srw_tac [][Tau_def, GLAM_NIL_EQ, term_ABS_pseudo11_1, Tau_termP]);

    only Tau_termP, Tau_def and Tau_def' (into operinfo), etc. are needed later.
 *)
fun pretypeToType2 pty tymap =
  case pty of
    dVartype s => if s = !free_tyname orelse s = !bound_tyname then
                      “:string”
                  else
                      Type.mk_vartype s
  | dTyop {Tyop = s, Thy, Args} => let
    in
      case Thy of
        NONE => assoc s tymap (* a nominal type here *)
      | SOME t => Type.mk_thy_type{Tyop = s, Thy = t,
                                   Args = List.map pretypeToType Args}
    end
  | dAQ pty => pty;

(* val Input_pattern = “GLAM x [a] rInput [^term_REP_t1 P] []”;

   x is the only bound name (otherwise it's “uu :string” here)
   [a] is the list of free names (a0, a1, a2, ...)
   rInput is the repcode
   [^term_REP_t1 P]: the first list is the (only) bound nominal argument (P)
   []: the second list is free nominal arguments (Q0, Q1, Q2, ...)

   External arguments are part of the repcode, e.g. in CCS:

   val prefix_pattern = “GLAM uu [] (cprefix u) [] [^term_REP_t E]”

   ``(GLAM :string ->
            string list -> 'a -> 'a gterm list -> 'a gterm list -> 'a gterm)``
   where 'a is instantiated to rep_t
 *)
val glam_t = “GLAM :string ->
               string list -> 'a -> 'a gterm list -> 'a gterm list -> 'a gterm”;

fun build_pattern tymap ty cname ptys rep_t = inst [alpha |-> rep_t] glam_t;

fun build_constructor tymap ty cname ptys rep_t = let
    val c_ty = list_mk_fun (List.map (fn e => pretypeToType2 e tymap) ptys, ty);
    val c_t = mk_var(cname, c_ty);
    val c_pattern = build_pattern tymap ty cname ptys rep_t
in
    (c_t, c_pattern)
end;

fun build_cons_inner cptys tyname tymap tydata rep_t = let
    val current_type = assoc tyname tymap
in
    List.map (fn (c:string,ptys) =>
                 build_constructor tymap current_type c ptys rep_t) cptys
end;

fun build_cons tynames (asts :AST list)
                       (tydata :nomtyinfo list) rep_t = let
    val newtys = List.map (fn e => #newty e) tydata;
    val tymap = zip tynames newtys
in
    List.concat (List.map (fn (tyname,df) =>
                              case df of
                                  Constructors cs =>
                                  build_cons_inner cs tyname tymap tydata rep_t
                                | Record _ => []) asts)
end;

(* The final API (so far) *)
fun nominal_datatype q = let
  val asts = parse_datatype q;
  val tynames = extract_tynames asts;
  val rep_t = define_repcode asts;
  val lp = build_lp asts rep_t;
  val tydata = build_tydata tynames 0 lp [];
  val cons = build_cons tynames asts tydata rep_t
in
    {tynames = tynames,
     tydata  = tydata,
     rep_t   = rep_t,
     lp      = lp}
end;

end (* struct *)
