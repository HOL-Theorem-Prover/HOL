(* ===================================================================== *)
(* LIBRARY: finset                                                       *)
(* FILE:                                                                 *)
(* DESCRIPTION: A simple theory of finite sets                           *)
(*                                                                       *)
(* AUTHOR: Axel Mamode                                                   *)
(* DATE:    June 1998                                                    *)
(* ===================================================================== *)

structure finsetScript =
struct

open HolKernel Parse basicHol90Lib
     arithmeticTheory prim_recTheory numTheory Num_induct Num_conv
     setTheory bossLib setLib simpLib;

type thm = Thm.thm
infix THEN THENL THENC ORELSE ORELSEC ## --> ++

val hol_ss =
  boolSimps.bool_ss ++ arithSimps.ARITH_ss ++ pairSimps.PAIR_ss ++
  UnwindSimps.UNWIND_ss


(* --------------------------------------------------------------------- *)
(* Create the new theory.                                                *)
(* --------------------------------------------------------------------- *)
(*
 Used for interactivity *)
(* load "bossLib";load "setTheory"; load "setLib"; load "simpLib"; load "HOLSimps";
 load "Q"; open bossLib setTheory simpLib;*)
val _ = new_theory "finset";

exception F_error of string;

val EXISTENCE_THM = prove
 (--`?s:'a set. FINITE s`--,
    EXISTS_TAC (--`{}:'a set`--) THEN
    REWRITE_TAC[FINITE_EMPTY]);

val finset_TY_DEF =
  new_type_definition {name="finset",
                       pred = ``FINITE:'a set -> bool``,
                       inhab_thm = EXISTENCE_THM};
val finset_ISO_DEF =
    define_new_type_bijections {name  = "finset_ISO_DEF",
                                ABS = "finset_ABS",
                                REP = "finset_REP",
                                tyax = finset_TY_DEF};

val FINITE_EXISTS = prove_rep_fn_onto finset_ISO_DEF;

(*----------------------------------------------------*)
(* Functions to translate set theorems to finset ones *)
(*----------------------------------------------------*)
fun type_cmp (s:Type.hol_type) s'= (s=s')

fun mk_finset_type ty = mk_type{Args=[ty], Tyop="finset"}
fun mk_set_type ty = mk_type{Args=[ty], Tyop="set"}

fun dest_set ty = let
  val {Args, Tyop} = dest_type ty
in
  if Tyop = "set" then hd Args else raise F_error "Not a set"
end;
val is_set = Lib.can dest_set;
val is_fun = Lib.can dom_rng;

(* Translation theorems, augmented throughout the script *)
val TRANSLATE_RULE_THMS = ref ([]: Thm.thm list);

fun add_thm_to_transl th = TRANSLATE_RULE_THMS:= th::(!TRANSLATE_RULE_THMS);

fun add_thms_to_transl [] = ()
  | add_thms_to_transl (hd::tl) = (add_thm_to_transl hd; add_thms_to_transl tl)

(* Not in the right place... *)
local
  fun f v (vs,l) = let
    val v' = variant vs v
  in
    (v'::vs, v'::l)
  end
in
  fun MY_SPEC_ALL th = let
    val (hvs, con) = (free_varsl ## I) (hyp th, concl th)
    val fvs = free_vars con
    and vars = fst(strip_forall con)
    val res = snd(itlist f vars (hvs@fvs,[]))
  in
    (SPECL res th, res)
  end
end;

val IMP_finset =store_thm(
  "IMP_finset",
  ``!P. (!s:'a set. FINITE s ==> P s) =
        (!fs. P (finset_REP fs))``,
  PROVE_TAC[FINITE_EXISTS]);

val REV_IMP_finset = store_thm(
  "REV_IMP_finset",
  ``!P. (!fs:'a finset. P fs) = (!s. FINITE s ==> P (finset_ABS s))``,
  SIMP_TAC bool_ss [finset_ISO_DEF, IMP_finset]);

    (* The translation process TRANSLATE_RULE implemented here is to
     track sets and try to transform them in finsets, using just
     finset_REP as an operator. The finset_REP are moved from their
     starting position in the Term tree to the upper position they may
     reach. There, they are removed by other rules *)
local
  val FORALL_SET_FINSET =
    TAC_PROOF(([],``!Q. (!s. Q s) ==> !fs. Q (finset_REP fs)``),
              PROVE_TAC[finset_ISO_DEF] )
in
  (* Introduction of finset_REP for universal quantifications over sets *)
  fun SET_TO_FINSET_FORALL_RULE th = let
    val body = (snd o strip_forall o concl) th
    val (th', vl) = MY_SPEC_ALL th
    fun trans [] =
      if is_imp body then
        DISCH (#ant (dest_imp body)) (SET_TO_FINSET_FORALL_RULE (UNDISCH th'))
      else th'
      | trans (v::tl) = let
          val th2 = trans tl
          val c = concl th2
          val ty = type_of v
        in
          if is_set ty then
            MP (BETA_RULE (ISPEC (mk_abs {Body = c, Bvar = v})
                           FORALL_SET_FINSET)) (GEN v th2)
          else
            GEN v th2
        end
  in
    trans vl
  end
end

fun set_absorb_list ty =
(* given a type 'a -> 'b set ... ->'o, returns ([(false, 'a), (true, 'b) ...], 'o) *)
(* This does not catch 'a -> ('a set -> 'a set) -> 'a so some formulas won't be translated *)
    if is_fun ty then
        let val (Arg, Rest) = dom_rng ty
            val (bl, tyend) = set_absorb_list Rest
        in
            ((if is_set Arg then (true, dest_set Arg) else (false, Arg))::bl, tyend)
        end
    else ([], ty)

fun set_to_finset_list (bl, tyend) =
(* with the result of the previous function, build finsets where sets where *)
    let fun stft [] = tyend
          | stft ((b, arg)::bl) =
                (if b then mk_finset_type arg
                 else arg) --> stft bl
    in
        stft bl
    end

local
    local
        fun to_prove v =
            (* given a function variable v:'a set -> 'b -> ... -> 'o, builds 3 terms of the form
             - !Q. (!v. Q(\fs pv ... . v (finset_REP fs) pv ...)) = (!v. Q v)
             - (\s pv ... . v (finset_ABS s) pv ...)
             - (\fs pv ... . v (finset_REP fs) pv ... )
             *)
            let
                fun build appl appl' [] = (appl, appl')
                  | build appl appl' ((b, arg)::typel) =
                    if not b then
                        let
                            val var_loc = variant (free_vars appl) (mk_var {Name = "pv", Ty = arg})
                            val (body, body') = build (mk_comb {Rand = var_loc, Rator = appl}) (mk_comb {Rand = var_loc, Rator = appl'}) typel
                        in
                            (mk_abs {Bvar= var_loc, Body=body}, mk_abs {Bvar= var_loc, Body=body'})
                        end
                    else
                        let
                            val var_loc  = variant (free_vars appl ) (mk_var {Name = "fs", Ty = mk_finset_type arg})
                            val var_loc' = variant (free_vars appl') (mk_var {Name = "s" , Ty = mk_set_type    arg})
                            val (body, body') = build ``^appl  (finset_REP ^var_loc )``
                                                      ``^appl' (finset_ABS ^var_loc')``
                                                      typel
                        in
                            (mk_abs {Bvar = var_loc, Body = body}, mk_abs {Bvar = var_loc', Body = body'})
                        end
                val (typel, tyend) = set_absorb_list (type_of v)
                val ty = set_to_finset_list (typel, tyend)
                val v' = mk_var {Name = #Name (dest_var v), Ty = ty}
                val (built, proof_help) = build v v' typel
            in
                (``!Q. (! ^v . Q ^built ) = (! ^v' . Q ^v')``,
                 proof_help, built)
            end
    in
        fun prover t =
    (* Proves theorems to transform functions ranging over sets to
    functions ranging over finsets *)
            let val (to_be_proved, hint, to_find) = to_prove t
            in
                (let val vl = fst (strip_abs to_find)
                 in
                     GENL vl (SYM (DEPTH_CONV BETA_CONV (list_mk_comb (to_find, vl))))
                 end,
                 TAC_PROOF (([], to_be_proved),
                            GEN_TAC THEN EQ_TAC THENL
                            [REPEAT STRIP_TAC THEN
                             POP_ASSUM (fn th => SIMP_TAC bool_ss [SIMP_RULE bool_ss [CONJUNCT1 finset_ISO_DEF] (SPEC hint th)]),
                             SIMP_TAC bool_ss []]),
                 to_find)
            end;
    end;
    fun is_set_absorb ty =
        if is_fun ty then
            let val (Arg, Rest)=dom_rng ty
            in
                is_set Arg orelse is_set_absorb Rest
            end
        else false
    fun parse_terms var replacer f =
        if is_comb f then
            let val (func, args')=strip_comb f
            in
                if aconv func var then
                    list_mk_comb (replacer, args')
                else list_mk_comb(parse_terms var replacer func, map (parse_terms var replacer) args')
            end
        else if is_abs f then
            let val {Bvar, Body}=dest_abs f in
                if op_mem aconv Bvar (free_vars var) then f else
                    mk_abs{Bvar=Bvar, Body = parse_terms var replacer Body}
            end
             else f
in
    fun ABSORB_RULE th =
    (* This function finds any universally quantified function
    ranging over sets and, provided it is applied to arguments, those
    which are sets being finset_REP, translate it in universally
    quatified function ranging over finsets *)
        let
            val (th', vl) = MY_SPEC_ALL th
            fun trans [] =
                let val body = concl th' in
                    if is_imp body then
                        DISCH (#ant (dest_imp body)) (ABSORB_RULE (UNDISCH th'))
                    else th'
                end
              | trans (v::tl) =
                let val th2 = trans tl
                    val ty = type_of v
                in
                    if is_set_absorb ty then
                        let val (them1, them2, to_find) =prover v
                            val th'2 = ONCE_REWRITE_RULE [them1] th2
                            val c = concl th'2
                            val thm2 = GEN_ALL (fst (EQ_IMP_RULE (SPEC_ALL them2)))
                            val (typel, tyend)=set_absorb_list ty
                            val ty' = set_to_finset_list (typel, tyend)
                            val tvar = variant (free_vars c @ vl) (mk_var{Name="f", Ty=ty'})
                            val pt = mk_abs {Body = parse_terms to_find tvar c, Bvar = tvar}
                        in
                            MP (BETA_RULE (SPEC pt thm2)) (GEN v th'2)
                        end handle _ => GEN v th2
                    else GEN v th2
                end
        in
            trans vl
        end
end;

fun TRANSLATE_RULE thms th= (ABSORB_RULE o (ASM_SIMP_RULE bool_ss ((!TRANSLATE_RULE_THMS) @ thms)) o SET_TO_FINSET_FORALL_RULE) th;

(* !a a'. (finset_REP a = finset_REP a') = a = a' *)
val _ = add_thm_to_transl (prove_rep_fn_one_one finset_ISO_DEF);

(* !a. ?r. (a = finset_ABS r) /\ FINITE r *)
val fREP_ONTO = prove_abs_fn_onto finset_ISO_DEF;
(* |- !r r'.
         FINITE r ==> FINITE r' ==> ((finset_ABS r = finset_ABS r') = r = r') *)
val fABS_11 = prove_abs_fn_one_one finset_ISO_DEF;

val FINITE_REP = store_thm("FINITE_REP",
                           ``FINITE (finset_REP (fs:'a finset))``,
                           REWRITE_TAC[finset_ISO_DEF]);

(*|- !r. FINITE r ==> (finset_REP (finset_ABS r) = r) *)
val rew =  (GEN_ALL o fst o EQ_IMP_RULE o SPEC_ALL o CONJUNCT2) finset_ISO_DEF;

val new_infix_definition = new_infixr_definition
val fIN_DEF = new_infix_definition ("fIN_DEF",
 --`fIN (x:'a) s = x IN (finset_REP s)`--,450);

val fEMPTY_DEF = new_definition ("fEMPTY", --`fEMPTY = finset_ABS ({}:'a set)`--);

val fSUBSET_DEF = new_infix_definition ("fSUBSET_DEF",
 --`fSUBSET (fs:'a finset) fs' = finset_REP fs SUBSET finset_REP fs'`--, 450);

val fINTER_DEF = new_infixl_definition ("fINTER_DEF",
 --`fINTER (fs:'a finset) fs' = finset_ABS (finset_REP fs INTER finset_REP fs')`--, 600);

val fUNION_DEF = new_infixl_definition ("fUNION_DEF",
 --`fUNION (fs:'a finset) fs' = finset_ABS (finset_REP fs UNION finset_REP fs')`--, 500);

val fINSERT_DEF = new_infixl_definition (
  "fINSERT_DEF",
  --`fINSERT (x:'a) fs = finset_ABS(x INSERT finset_REP fs)`--,
  500);

val fDIFF_DEF = new_infixl_definition (
  "fDIFF_DEF",
  ``fDIFF (fs:'a finset) fs' =
       finset_ABS (finset_REP fs DIFF finset_REP fs')``,
  500);

val fDELETE_DEF = new_infixl_definition (
  "fDELETE_DEF",
  --`fDELETE fs (x:'a) =  finset_ABS(finset_REP fs DELETE x)`--,
  500);

val fGSPEC_DEF = new_specification
    {consts = [{const_name = "fGSPEC", fixity = Prefix}],
     name = "fGSPEC_DEF",
     sat_thm = let
       val th =
         PROVE[finset_ISO_DEF]
         `!d. FINITE (GSPEC d) ==> ?s:'a finset. s = finset_ABS (GSPEC d)`
     in
       EQ_MP ((DEPTH_CONV RIGHT_IMP_EXISTS_CONV THENC SKOLEM_CONV) (concl th))
       th
     end};

val fCARD_DEF = new_definition (
  "fCARD_DEF",
  ``fCARD (fs:'a finset) = CARD (finset_REP fs)``);

val fCHOICE_DEF = new_definition(
  "fCHOICE_DEF",
  ``!fs:'a finset. fCHOICE fs = CHOICE (finset_REP fs)``);

val fREST_DEF = new_definition (
  "fREST_DEF",
  ``fREST (fs:'a finset) = finset_ABS (REST (finset_REP fs))``);

val _ =
  add_thms_to_transl (FINITE_REP ::
                      map GSYM [fCARD_DEF, fCHOICE_DEF, fIN_DEF, fSUBSET_DEF]);

val FINSET_CASES = store_thm (
  "FINSET_CASES",
  ``!fs. (fs = fEMPTY) \/
         (?(e:'a) fs'. (fs = e fINSERT fs') /\ ~(e fIN fs'))``,
  GEN_TAC THEN
  STRIP_ASSUME_TAC (Q.SPEC `fs` fREP_ONTO) THEN
  ASM_SIMP_TAC bool_ss [fEMPTY_DEF, FINITE_EMPTY, fABS_11] THEN
  DISJ_CASES_THEN STRIP_ASSUME_TAC (Q.SPEC `r` SET_CASES) THEN
  FULL_SIMP_TAC bool_ss [FINITE_INSERT, NOT_INSERT_EMPTY] THEN
  Q.EXISTS_TAC `x` THEN Q.EXISTS_TAC `finset_ABS t` THEN
  FULL_SIMP_TAC bool_ss [fIN_DEF, fINSERT_DEF, finset_ISO_DEF]);

val EMPTY_fEMPTY = store_thm(
  "EMPTY_fEMPTY",
  ``{} = finset_REP fEMPTY``,
  PROVE_TAC [FINITE_EMPTY, finset_ISO_DEF, fEMPTY_DEF])

val INSERT_fINSERT = store_thm (
  "INSERT_fINSERT",
  ``x INSERT (finset_REP s) = finset_REP (x fINSERT s)``,
  SIMP_TAC bool_ss [fINSERT_DEF, rew, FINITE_REP, FINITE_INSERT]);

val DIFF_fDIFF = store_thm(
  "DIFF_fDIFF",
  ``finset_REP fs DIFF finset_REP fs' = finset_REP (fs fDIFF fs')``,
  SIMP_TAC bool_ss [FINITE_DIFF, FINITE_REP, rew, fDIFF_DEF]);

val UNION_fUNION = store_thm (
  "UNION_fUNION",
  ``(finset_REP s1) UNION (finset_REP s2) = finset_REP (s1 fUNION s2)``,
  SIMP_TAC bool_ss [fUNION_DEF, rew, FINITE_REP, FINITE_UNION]);

val INTER_fINTER = store_thm (
  "INTER_fINTER",
  ``(finset_REP s1) INTER (finset_REP s2) = finset_REP (s1 fINTER s2)``,
  SIMP_TAC bool_ss [fINTER_DEF, rew, FINITE_REP, INTER_FINITE]);

val _ =
  add_thms_to_transl [EMPTY_fEMPTY, INSERT_fINSERT, DIFF_fDIFF, UNION_fUNION,
                      INTER_fINTER];

val DELETE_fDELETE = store_thm(
  "DELETE_fDELETE",
  ``finset_REP fs DELETE x = finset_REP (fs fDELETE x)``,
  SIMP_TAC bool_ss [FINITE_DELETE, FINITE_REP, rew, fDELETE_DEF]);
val REST_fREST = store_thm(
  "REST_fREST",
  ``REST (finset_REP fs) = finset_REP (fREST fs)``,
  SIMP_TAC bool_ss [fREST_DEF, rew, FINITE_REP, REST_DEF, FINITE_DELETE]);

val EQ_fEQ = store_thm(
  "EQ_fEQ",
  ``(finset_REP s = finset_REP s') = s = s'``,
  PROVE_TAC[finset_ISO_DEF]);

val _ = add_thms_to_transl [DELETE_fDELETE, REST_fREST, EQ_fEQ];

val fDELETE = save_thm("fDELETE", TRANSLATE_RULE [] DELETE_DEF);

val fCHOICE = save_thm("fCHOICE", TRANSLATE_RULE [] CHOICE_DEF);

val fREST = save_thm("fREST", TRANSLATE_RULE [] REST_DEF)

val fSUBSET = save_thm("fSUBSET_THM", TRANSLATE_RULE [] SUBSET_DEF);

val GSPEC_fGSPEC = store_thm(
  "GSPEC_fGSPEC",
  ``FINITE (GSPEC s) ==> (GSPEC s = finset_REP (fGSPEC s))``,
  PROVE_TAC [fGSPEC_DEF, finset_ISO_DEF]);

val fEXTENSION = save_thm("fEXTENSION", TRANSLATE_RULE [] EXTENSION);

val _ = add_thm_to_transl IMP_finset;

(* One good example of the use of TRANSLATE_RULE *)
val finset_INDUCT = save_thm(
  "finset_INDUCT",
  TRANSLATE_RULE [GSYM AND_IMP_INTRO] FINITE_INDUCT);

val SPEC_GSPEC = store_thm (
  "SPEC_GSPEC",
  ``SPEC P=GSPEC (\x. (x, P x))``,
  SIMP_TAC hol_ss [GSPEC_DEF]);

val TRANSLATE_THMS =
  ref ([IMP_finset, SPEC_GSPEC, GSPEC_fGSPEC, EMPTY_fEMPTY, INSERT_fINSERT,
        UNION_fUNION, INTER_fINTER, EQ_fEQ] @
       (map  GSYM [fIN_DEF, fSUBSET_DEF]))

fun TRANSLATE_TAC thms = ASM_SIMP_TAC bool_ss ((!TRANSLATE_THMS) @ thms);

fun op_set_delete (cmp_fn:'a -> 'a -> bool) [] _ = []
  | op_set_delete cmp_fn (big::tl1) small =
    if (cmp_fn big small) then
        tl1
    else big::(op_set_delete cmp_fn tl1 small)

 (* The functions that produce only finite sets if their arguments are
  finite *)
val not_needed = ref ["UNION", "EMPTY", "INTER", "INSERT", "DELETE", "DIFF"]

fun defined_consts comb =
    let val (const_term, args) = strip_comb comb
    in
        if is_const const_term
            andalso mem (#Name (dest_const const_term)) (!not_needed)
        then
            itlist (op_union aconv) (map defined_sets args) []
        else
            (*itlist (op_union aconv) (map defined_sets args)*) [comb]
    end
and defined_sets term =
    let val t = type_of term
    in
        if is_set t then
            if is_var term then [term]
            else defined_consts term
        else
            if (is_const term) orelse (is_var term) then
                []
            else if (is_abs term) then
                let val {Body, Bvar} = dest_abs term
                    val sets_body = defined_sets Body
                in
                    case (defined_sets Bvar) of
                        [] => sets_body
                      | [v1] => op_set_delete aconv sets_body v1
                      | _ => raise (HOL_ERR {origin_structure = "finsetTheory",
                                             origin_function = "defined_sets",
                                             message = "abstraction with multiple variables"})
                end
            else
        let val (app, args) = strip_comb term
            val ty = type_of term
        in
            (* Not sure this is the right behaviour in some cases... *)
            itlist (op_union aconv) (map defined_sets (app::args)) []
        end
    end

fun SET_FINSET0_TAC (assums, goal) =
    let val def_sets = itlist (op_union aconv) (map defined_sets (goal::assums)) []
        val new_assumed = map (fn s => (list_mk_comb
                                        (mk_const {Name = "FINITE", Ty = type_of s --> bool},
                                                  [s]))) def_sets
        fun solve (as1::assl) (th1::thl) fst_thm = MP (DISCH as1 (solve assl thl fst_thm)) th1
          | solve [] [] fst_thm = fst_thm
          | solve _ _ _ = raise Fail "Not to be applied with this number of arguments"
    in
        ((new_assumed @ assums, goal) :: (map (fn s => (assums, s)) new_assumed),
                                          (fn first_thm::left => solve new_assumed left first_thm))
    end;

val UNDISCH_ALL_TAC = REPEAT (FIRST_ASSUM (UNDISCH_TAC o concl));

val SET_FINSET_TAC = REPEAT GEN_TAC THEN
        UNDISCH_ALL_TAC THEN
        SET_FINSET0_TAC


val lemma = prove(
  ``!n.
      (EVEN n = ?fs. 0 fIN fs /\ n fIN fs /\
                     (!m. m <n ==> (m fIN fs = ~(SUC m fIN fs)))) /\
      (ODD  n = ?fs. 0 fIN fs /\ ~(n fIN fs) /\
                     (!m. m <n ==> (m fIN fs = ~(SUC m fIN fs))))``,
  GEN_TAC THEN Induct_on `n` THENL [
    REPEAT STRIP_TAC THEN SIMP_TAC hol_ss [EVEN, ODD_EVEN] THEN
    Q.EXISTS_TAC `0 fINSERT fEMPTY` THEN
    SIMP_TAC bool_ss [TRANSLATE_RULE [] IN_SING],
    POP_ASSUM STRIP_ASSUME_TAC THEN REPEAT STRIP_TAC THENL
    let
      fun prover (th1, th2, ptm) =
        SIMP_TAC bool_ss [EVEN, th1] THEN EQ_TAC THENL [
          RW_TAC bool_ss [] THEN
          Q.EXISTS_TAC ptm THEN
          ASM_SIMP_TAC hol_ss [TRANSLATE_RULE [] th2] THEN
          GEN_TAC THEN
          DISCH_THEN (STRIP_ASSUME_TAC o
                      CONV_RULE (REWR_CONV prim_recTheory.LESS_THM)) THEN
          ASM_SIMP_TAC hol_ss [],
          STRIP_TAC THEN ASM_SIMP_TAC hol_ss [] THEN Q.EXISTS_TAC `fs` THEN
          ASM_SIMP_TAC hol_ss []
        ]
     in
        map prover [(EVEN_ODD, IN_INSERT, `SUC n fINSERT fs`),
                    (ODD_EVEN, IN_DELETE, `fs fDELETE SUC n`)]
     end
  ]);

(* should use only EVEN_FINSET and ODD_EVEN, not ODD_FINSET *)
val EVEN_FINSET = save_thm (
  "EVEN_FINSET",
  GEN_ALL (CONJUNCT1 (SPEC_ALL lemma)));
val ODD_FINSET = save_thm(
  "ODD_FINSET",
  GEN_ALL (CONJUNCT2 (SPEC_ALL lemma)));

val _ = export_theory()

end