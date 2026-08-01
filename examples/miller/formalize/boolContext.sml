(* non-interactive mode
*)
structure boolContext :> boolContext =
struct
open HolKernel Parse boolLib;

structure Parse = struct
  open Parse
  val (Type,Term) =
      valOf (grammarDB {thyname = "pred_set"})
        |> apsnd ParseExtras.grammar_loose_equality
        |> parse_from_grammars
end
open Parse

open pairTheory pred_setTheory
     res_quanTheory hurdUtils ho_proverTools res_quanTools subtypeTools
     subtypeTheory boolContextContextTheory;

nonfix THEN THENL ORELSE;


(* --------------------------------------------------------------------- *)
(* Subtype checking.                                                     *)
(* --------------------------------------------------------------------- *)

val bool_sc =
  map SC_SIMPLIFICATION
  [PAIR_UNIV, FUNSET_DFUNSET, IN_INTER, IN_UNION, IN_COMPL, SUBSET_INTER,
   SUBSET_K, K_SUBSET] @
  map SC_JUDGEMENT
  [IN_UNIV, IN_PAIR, SUBSET_THM] @
  map SC_SUBTYPE
  [DEFAULT_SUBTYPE, COMB_SUBTYPE, ABS_SUBTYPE,
   COND_SUBTYPE, RES_ABSTRACT_SUBTYPE, UNCURRY_SUBTYPE];

(* --------------------------------------------------------------------- *)
(* Contextual rewriting.                                                 *)
(* --------------------------------------------------------------------- *)

(* Rules *)

val forall_rule = pattern_rule (``!x. P x``, wrap o var_GENVAR_SPEC);

val conj_rule = pattern_rule (``a /\ b``, var_CONJUNCTS);

val res_forall_rule =
  pattern_rule (``!x :: P. M x``, wrap o (I ## CONV_RULE RES_FORALL_CONV));

(* Rewrites *)

val beta_rewr = pattern_rewr (``(\x. (y : 'a -> 'b) x) z``, K (K BETA_CONV));
val neg_t_rewr =
  pattern_rewr (``~T``, K (K (REWR_CONV (ho_PROVE [] ``~T = F``))));
val neg_f_rewr =
  pattern_rewr (``~F``, K (K (REWR_CONV (ho_PROVE [] ``~F = T``))));

val basic_bool_rewrs =
  let
    val and_c = map GEN_ALL (CONJUNCTS (SPEC_ALL AND_CLAUSES))
    val or_c  = map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES))
    val imp_c = map GEN_ALL (CONJUNCTS (SPEC_ALL IMP_CLAUSES))
    val cond_c = map GEN_ALL (CONJUNCTS (SPEC_ALL COND_CLAUSES))
    val eq_c  = map GEN_ALL (CONJUNCTS (SPEC_ALL EQ_CLAUSES))
    val not_c = CONJUNCTS NOT_CLAUSES
    val dm    = map GEN_ALL (CONJUNCTS (SPEC_ALL DE_MORGAN_THM))
  in
    [List.nth (not_c, 0),                (* ~~a = a *)
     List.nth (eq_c, 1),                 (* (a = T) = a *)
     List.nth (eq_c, 3),                 (* (a = F) = ~a *)
     List.nth (eq_c, 0),                 (* (T = a) = a *)
     List.nth (eq_c, 2),                 (* (F = a) = ~a *)
     EQ_NEG_SELF_F,                      (* (a = ~a) = F *)
     NEG_EQ_SELF_F,                      (* (~a = a) = F *)
     List.nth (and_c, 2),                (* F /\ a = F *)
     List.nth (and_c, 3),                (* a /\ F = F *)
     List.nth (and_c, 0),                (* T /\ a = a *)
     List.nth (and_c, 1),                (* a /\ T = a *)
     List.nth (and_c, 4),                (* a /\ a = a *)
     NAND_SELF_F,                        (* ~a /\ a = F *)
     AND_NEG_SELF_F,                     (* a /\ ~a = F *)
     List.nth (or_c, 0),                 (* T \/ a = T *)
     List.nth (or_c, 1),                 (* a \/ T = T *)
     List.nth (or_c, 2),                 (* F \/ a = a *)
     List.nth (or_c, 3),                 (* a \/ F = a *)
     List.nth (or_c, 4),                 (* a \/ a = a *)
     NEG_OR_SELF_T,                      (* ~a \/ a = T *)
     OR_NEG_SELF_T,                      (* a \/ ~a = T *)
     List.nth (dm, 1),                   (* ~(a \/ b) = ~a /\ ~b *)
     List.nth (imp_c, 3),                (* a ==> a = T *)
     List.nth (imp_c, 1),                (* a ==> T = T *)
     List.nth (imp_c, 4),                (* a ==> F = ~a *)
     List.nth (imp_c, 0),                (* T ==> a = a *)
     List.nth (imp_c, 2),                (* F ==> a = T *)
     boolTheory.NOT_IMP,                 (* ~(a ==> b) = a /\ ~b *)
     REFL_CLAUSE,                        (* (a = a) = T *)
     NEG_EQ_EQ,                          (* (~a = ~b) = (a = b) *)
     List.nth (cond_c, 0),               (* (if T then a else b) = a *)
     List.nth (cond_c, 1),               (* (if F then a else b) = b *)
     NOT_FORALL_THM,
     NOT_EXISTS_THM,
     FORALL_TRIVIAL,
     EXISTS_TRIVIAL]
  end;

(* The precontext *)

val bool_pc = precontext_add
  ("bool",
   map C_RULE
   [forall_rule, conj_rule, res_forall_rule] @
   map C_CONG
   [comb_cong, abs_cong, conj_cong, disj_cong, imp_cong, cond_cong,
    res_forall_cong, res_exists_cong, res_select_cong, res_abstract_cong,
    uncurry_cong] @
   map C_REWR
   [beta_rewr, neg_t_rewr, neg_f_rewr] @
   map C_THM
   [PAIRED_BETA_THM, FST, SND, CLOSED_PAIR_EQ,
    RES_ABSTRACT_IDEMPOT, RES_ABSTRACT, IN_UNIV, NOT_IN_EMPTY, IN_SING,
    EMPTY_FUNSET, FUNSET_EMPTY, RES_FORALL_EMPTY,
    RES_EXISTS_EMPTY, RES_SELECT_EMPTY, RES_EXISTS_UNIQUE_EMPTY,
    RES_FORALL_UNIV, RES_EXISTS_UNIV, RES_SELECT_UNIV, RES_EXISTS_UNIQUE_UNIV,
    RES_FORALL_NULL, RES_EXISTS_NULL, RES_EXISTS_UNIQUE_NULL] @
   map C_THM basic_bool_rewrs @
   map C_SUBTYPE bool_sc)
  empty_precontext;

(* The context *)

val bool_c = precontext_compile bool_pc;

(*
try prove
(``!p. ((!x. p x) = T) ==> !y. p y``,
 SIMPLIFY_TAC bool_c []);

reset_traces ();
allow_trace "SIMPLIFY_TYPECHECK: (tm, res)";

try prove (``!x. ~x \/ ~~x``, SIMPLIFY_TAC bool_c []);

try prove (``!a :: p. (\x :: p. T) a``, SIMPLIFY_TAC bool_c []);
*)

(* non-interactive mode
*)
end;
