(* non-interactive mode
*)
structure boolContext :> boolContext =
struct
open HolKernel Parse boolLib;

structure Parse = struct
  open Parse
  val (Type,Term) =
      pred_setTheory.pred_set_grammars
        |> apsnd ParseExtras.grammar_loose_equality
        |> parse_from_grammars
end
open Parse

(* interactive mode
if !show_assums then () else
 (loadPath := ".."::"../../prob"::(!loadPath);
  load "bossLib";
  load "pred_setTheory";
  load "millerTools";
  load "miller_extraTheory";
  show_assums := true);
*)

open pairTheory pred_setTheory
     res_quanTheory hurdUtils ho_proverTools res_quanTools subtypeTools
     subtypeTheory;

infixr 0 ++ || ORELSEC ## THENC THEN_TCL ORELSE_TCL;
infix 1 >>;
nonfix THEN THENL ORELSE;

val op++ = op THEN;
val op|| = op ORELSE;
val op>> = op THEN1;

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
  map (prove o add_snd (ho_PROVE_TAC []))
  [``!a:bool. ~~a = a``,
   ``!a. (a = T) = a``,
   ``!a. (a = F) = ~a``,
   ``!a. (T = a) = a``,
   ``!a. (F = a) = ~a``,
   ``!a : bool. (a = ~a) = F``,
   ``!a : bool. (~a = a) = F``,
   ``!a. F /\ a = F``,
   ``!a. a /\ F = F``,
   ``!a. T /\ a = a``,
   ``!a. a /\ T = a``,
   ``!a. a /\ a = a``,
   ``!a. ~a /\ a = F``,
   ``!a. a /\ ~a = F``,
   ``!a. T \/ a = T``,
   ``!a. a \/ T = T``,
   ``!a. F \/ a = a``,
   ``!a. a \/ F = a``,
   ``!a. a \/ a = a``,
   ``!a. ~a \/ a = T``,
   ``!a. a \/ ~a = T``,
   ``!a b. ~(a \/ b) = ~a /\ ~b``,
   ``!a. a ==> a = T``,
   ``!a. a ==> T = T``,
   ``!a. a ==> F = ~a``,
   ``!a. T ==> a = a``,
   ``!a. F ==> a = T``,
   ``!a b. ~(a ==> b) = a /\ ~b``,
   ``!a : 'a. (a = a) = T``,
   ``!a b : bool. (~a = ~b) = (a = b)``,
   ``!(a : 'a) b. (if T then a else b) = a``,
   ``!(a : 'a) b. (if F then a else b) = b``,
   ``!p. ~(!x. p x) = ?x. ~p x``,
   ``!p. ~(?x. p x) = !x. ~p x``,
   ``!p. (!(x : 'a). p) = p``,
   ``!p. (?(x : 'a). p) = p``];

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
