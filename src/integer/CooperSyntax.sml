structure CooperSyntax :> CooperSyntax = struct

(* simple term manipulation functions, some term literals, and some
   conversions, all intended for very specific use within the
   implementation of Cooper's algorithm *)

open HolKernel boolLib intSyntax intSimps CooperThms
open int_arithTheory integerTheory Parse

infix THEN THENC ORELSEC |-> ##
infixr -->

val (Type,Term) = parse_from_grammars integerTheory.integer_grammars

fun ERR f msg = HOL_ERR {origin_structure = "CooperSyntax",
                         origin_function = f,
                         message = msg}

val not_tm = boolSyntax.negation;
val num_ty = numSyntax.num
val true_tm = boolSyntax.T
val false_tm = boolSyntax.F

(* ---------------------------------------------------------------------- *)
(* Generally applicable conversions                                       *)
(* ---------------------------------------------------------------------- *)

fun mk_abs_CONV var term = let
  val rhs = Rsyntax.mk_abs {Body = term, Bvar = var}
  val newrhs = Rsyntax.mk_comb {Rator = rhs, Rand = var}
in
  SYM (BETA_CONV newrhs)
end

(* ---------------------------------------------------------------------- *)
(* functions for dealing with "conjunctions" and "disjunctions"; logical  *)
(* operators that might have their meaning concealed under negations      *)
(* ---------------------------------------------------------------------- *)

val cpstrip_conj  = let
  (* treats negations over disjunctions as conjunctions *)
  fun doit posp acc tm = let
    val (l,r) = (if posp then dest_conj else dest_disj) tm
  in
    doit posp (doit posp acc r) l
  end handle HOL_ERR _ => let
    val t0 = dest_neg tm
  in
    doit (not posp) acc t0
  end handle HOL_ERR _ => if posp then tm::acc else mk_neg tm :: acc
in
  doit true []
end

val cpstrip_disj = let
  (* treats negations over conjunctions as disjunctions *)
  fun doit posp acc tm = let
    val (l,r) = (if posp then dest_disj else dest_conj) tm
  in
    doit posp (doit posp acc r) l
  end handle HOL_ERR _ => let
    val t0 = dest_neg tm
  in
    doit (not posp) acc t0
  end handle HOL_ERR _ => if posp then tm::acc else mk_neg tm :: acc
in
  doit true []
end

datatype term_op = CONJN | DISJN | NEGN
fun characterise t =
  (case #1 (dest_const (#1 (strip_comb t))) of
     "/\\" => SOME CONJN
   | "\\/" => SOME DISJN
   | "~" => SOME NEGN
   | _ => NONE) handle HOL_ERR _ => NONE
val bop_characterise = characterise


datatype reltype = rEQ | rDIV | rLT
fun categorise_leaf tm = let
  val (c, _) = strip_comb tm
in
  case dest_const c of
    ("int_lt", _) => rLT
  | ("=", _) => rEQ
  | ("int_divides", _) => rDIV
  | _ => raise Fail "categorise leaf applied to non Cooper leaf"
end


fun cpEVERY_CONJ_CONV c tm = let
  fun findconjunct posp tm =
    case (characterise tm, posp) of
      (SOME CONJN, true) => BINOP_CONV (findconjunct posp) tm
    | (SOME DISJN, false) => BINOP_CONV (findconjunct posp) tm
    | (SOME NEGN, _) => RAND_CONV (findconjunct (not posp)) tm
    | _ => c tm
in
  findconjunct true tm
end

fun cpEVERY_DISJ_CONV c tm = let
  fun finddisj posp tm =
    case (characterise tm, posp) of
      (SOME DISJN, true) => BINOP_CONV (finddisj posp) tm
    | (SOME CONJN, false) => BINOP_CONV (finddisj posp) tm
    | (SOME NEGN, _) => RAND_CONV (finddisj (not posp)) tm
    | _ => c tm
in
  finddisj true tm
end

fun cpis_disj tm =
  is_disj tm orelse let
    val tm0 = dest_neg tm
  in
    cpis_conj tm0
  end handle HOL_ERR _ => false
and cpis_conj tm =
  is_conj tm orelse let
    val tm0 = dest_neg tm
  in
    cpis_disj tm0
  end handle HOL_ERR _ => false


(* ---------------------------------------------------------------------- *)
(* determining whether or not terms include quantifiers, and what sort    *)
(* they might be.                                                         *)
(* ---------------------------------------------------------------------- *)

val int_exists = mk_thy_const{Name = "?", Thy = "bool",
                              Ty = (int_ty --> bool) --> bool}
val int_forall = mk_thy_const{Name = "!", Thy = "bool",
                              Ty = (int_ty --> bool) --> bool}

val has_exists = free_in int_exists
val has_forall = free_in int_forall

fun has_quant t =
  (* assumes that all head terms are not abstractions *)
  if is_abs t then has_quant (body t)
  else let
    val (f, args) = strip_comb t
  in
    f = int_exists orelse f = int_forall orelse
    List.exists has_quant args
  end


datatype qstatus = EITHER | NEITHER | qsUNIV | qsEXISTS
fun negstatus s = case s of qsUNIV => qsEXISTS | qsEXISTS => qsUNIV | x => x
fun goal_qtype tm = let
  fun recurse acc tm = let
    val (l, r) = dest_conj tm handle HOL_ERR _ => dest_disj tm
  in
    case (acc, recurse acc l) of
      (_, EITHER) => recurse acc r
    | (_, NEITHER) => NEITHER
    | (EITHER, x) => recurse x r
    | _ => recurse acc r
  end handle HOL_ERR _ => let
    val (f, args) = strip_comb tm
  in
    case (#Name (dest_thy_const f), acc) of
      ("~", _) => negstatus (recurse (negstatus acc) (hd args))
    | ("!", qsEXISTS) => NEITHER
    | ("!", _) => recurse qsUNIV (body (hd args))
    | ("?", qsUNIV) => NEITHER
    | ("?", _) => recurse qsEXISTS (body (hd args))
    | ("?!", _) => NEITHER
    | _ => acc
  end handle HOL_ERR _ => acc
in
  recurse EITHER tm
end

(* ---------------------------------------------------------------------- *)
(* Moving quantifiers as high as possible in a term                       *)
(* ---------------------------------------------------------------------- *)

val move_quants_up =
  REDEPTH_CONV (OR_EXISTS_CONV ORELSEC
                LEFT_OR_EXISTS_CONV ORELSEC RIGHT_OR_EXISTS_CONV ORELSEC
                LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV ORELSEC
                NOT_EXISTS_CONV ORELSEC NOT_FORALL_CONV ORELSEC
                AND_FORALL_CONV ORELSEC
                LEFT_AND_FORALL_CONV ORELSEC RIGHT_AND_FORALL_CONV ORELSEC
                LEFT_OR_FORALL_CONV ORELSEC RIGHT_OR_FORALL_CONV)

(* ---------------------------------------------------------------------- *)
(* Takes !x. P x                                                          *)
(*  and produces ~(?x. ~P x)                                              *)
(* ---------------------------------------------------------------------- *)
local
  val NOT_EXISTS_THM =
    GEN_ALL (SYM
             (PURE_REWRITE_RULE [NOT_CLAUSES]
              (BETA_RULE (SPEC (Term`\x:'a. ~ P x`)
                               boolTheory.NOT_EXISTS_THM))))
in

  fun flip_forall tm = let
    val (bvar, _) = dest_forall tm
  in
    BINDER_CONV (mk_abs_CONV bvar) THENC
    REWR_CONV NOT_EXISTS_THM THENC
    RAND_CONV (BINDER_CONV (RAND_CONV BETA_CONV)) THENC
    RAND_CONV (RENAME_VARS_CONV [#1 (dest_var bvar)])
  end tm
end



(* ---------------------------------------------------------------------- *)
(* If term is !x y z... . body                                            *)
(* change it to ~(?x y z... . body)                                       *)
(* ---------------------------------------------------------------------- *)

fun flip_foralls tm = let
  val (bvar, body) = dest_forall tm
in
  BINDER_CONV flip_foralls THENC flip_forall THENC
  TRY_CONV (RAND_CONV (BINDER_CONV (REWR_CONV NOT_NOT_P)))
end tm handle HOL_ERR _ => ALL_CONV tm

(* ---------------------------------------------------------------------- *)
(* Counts number of occurrences of variables in term with given name      *)
(* ---------------------------------------------------------------------- *)

fun count_occurrences str tm = let
  fun recurse acc tm =
    case strip_comb tm of
      (f, []) => ((if #1 (dest_var f) = str then 1 + acc else acc)
                  handle HOL_ERR _ => acc)
    | (_, args) => List.foldl (fn(t,a) => recurse a t) acc args
in
  recurse 0 tm
end

fun count_vars tm = let
  open Binarymap
  fun recurse (tm,dict) =
    case strip_comb tm of
      (f, []) => let
      in let
        val n = #1 (dest_var f)
      in
        case peek(dict,n) of
          NONE => insert(dict, n, 1)
        | SOME i => insert(dict, n, i+1)
      end handle HOL_ERR _ => dict end
    | (_, args) => List.foldl recurse dict args
in
  listItems (recurse (tm, mkDict String.compare))
end

(* dealing with constraints of the form lo < x /\ x <= hi *)
val resquan_onestep =
  REWR_CONV restricted_quantification_simp THENC
  REDUCE_CONV THENC REWRITE_CONV []

fun resquan_remove tm =
  (resquan_onestep THENC TRY_CONV (RAND_CONV resquan_remove) THENC
   REWRITE_CONV []) tm






val bmarker_tm = prim_mk_const { Name = "bmarker", Thy = "int_arith"};

val mk_bmark_thm = GSYM int_arithTheory.bmarker_def
fun mk_bmark tm = SPEC tm mk_bmark_thm

fun mark_conjunct P tm = let
in
  if is_conj tm then
    LAND_CONV (mark_conjunct P) ORELSEC RAND_CONV (mark_conjunct P)
  else if is_neg tm then
    if is_disj (rand tm) then
      REWR_CONV NOT_OR THENC mark_conjunct P
    else if P tm then
      mk_bmark
    else NO_CONV
  else if P tm then
    mk_bmark
  else NO_CONV
end tm

val move_bmarked_left = PURE_REWRITE_CONV [bmarker_rewrites] THENC
                        LAND_CONV (REWR_CONV int_arithTheory.bmarker_def)
fun move_conj_left P = mark_conjunct P THENC move_bmarked_left


(* special "constraint" terms will be wrapped in K terms, with the
   variable being constrained as the second argument to the combinator.
   The only free variable in the constraint term will be the constrained
   variable.  Further a constraint will be of the form
     d1 < j /\ j <= d2
   for some pair of integer literals d1 and d2, with the variable j. *)
val constraint_tm = mk_thy_const {Name = "K", Thy = "combin",
                                  Ty = bool --> (int_ty --> bool)}
fun mk_constraint (v,tm) = list_mk_comb(constraint_tm,[tm,v])
fun is_constraint tm = let
  val (f, args) = strip_comb tm
in
  f = constraint_tm andalso length args = 2
end
fun is_vconstraint v tm = let
  val (f, args) = strip_comb tm
in
  f = constraint_tm andalso length args = 2 andalso
  free_vars (hd (tl args)) = [v]
end


val K_THM = INST_TYPE [(alpha |-> bool), (beta |-> int_ty)] combinTheory.K_THM
fun MK_CONSTRAINT tm =
  case free_vars tm of
    [] => ALL_CONV tm
  | [v] => SYM (SPECL [tm,v] K_THM)
  | _ => raise Fail "MK_CONSTRAINT: Term has too many free variables"
fun UNCONSTRAIN tm = let
  val (f, args) = strip_comb tm
in
  SPECL args K_THM
end
fun IN_CONSTRAINT c = UNCONSTRAIN THENC c THENC MK_CONSTRAINT

fun quick_cst_elim tm = let
  (* eliminates constraints of the form
        K (lo < x /\ x <= hi) x
     where hi - lo <= 1, either replacing it with x = lo, or just false
     fails (NO_CONV) otherwise. *)
  val (_, args) = strip_comb tm  (* K and its args *)
  val cst = hd args
  val (_, cstargs) = strip_comb cst  (* two conjuncts *)
  val lo_cst = hd cstargs
  val hi_cst = hd (tl cstargs)
  val lo_t = rand (rator lo_cst)
  val hi_t = rand hi_cst
  val lo_i = int_of_term lo_t
  val hi_i = int_of_term hi_t
  open Arbint
in
  if hi_i - lo_i <= one then
    (UNCONSTRAIN THENC resquan_remove) tm
  else
    NO_CONV tm
end

fun reduce_if_ground tm =
  (* calls REDUCE_CONV on a ground term, does nothing otherwise *)
  if is_exists tm orelse not (HOLset.isEmpty (FVL [tm])) then ALL_CONV tm
  else REDUCE_CONV tm


fun fixup_newvar tm = let
  (* takes an existential term and replaces all occurrences of the bound
     variable in the body with 1 * v, except that we don't need to go
     looking for this variable under multiplications, nor under
     constraint terms *)
  open QConv
  val (v,body) = dest_exists tm
  val replace_thm = SYM (SPEC v INT_MUL_LID)
  fun recurse tm = let
    val (f, args) = strip_comb tm
  in
    case args of
      [] => if Term.compare(v,tm) = EQUAL then replace_thm
            else ALL_QCONV tm
    | [_] => RAND_CONV recurse tm
    | [_,_] => if Term.compare(f, constraint_tm) = EQUAL orelse
                  Term.compare(f, mult_tm) = EQUAL then ALL_QCONV tm
               else BINOP_QCONV recurse tm
    | _ => raise ERR "fixup_newvar"
                     ("found ternary operator - "^term_to_string tm)
  end
in
  QConv.QCONV (BINDER_CONV recurse) tm
end

(* with ?x. p \/ q \/ r...          (with or's right associated)
   expand to (?x. p) \/ (?x.q) \/ (?x.r) ...
*)
fun push_one_exists_over_many_disjs tm =
  ((EXISTS_OR_CONV THENC RAND_CONV push_one_exists_over_many_disjs) ORELSEC
   ALL_CONV) tm


fun remove_vacuous_existential tm = let
  (* term is of form  ?x. x = e *)
  val value = rhs (#2 (dest_exists tm))
  val thm = ISPEC value EXISTS_REFL
in
  EQT_INTRO thm
end


fun simple_divides var tm = let
  (* true if a term is a divides, where the right hand side's only
     free variable is the parameter var *)
  val (l,r) = dest_divides tm
in
  free_vars r = [var]
end handle HOL_ERR _ => false


local exception foo
in
fun push_in_exists_and_follow c tm = let
  (* looking at
       ?x. ... /\ P x /\ ...
     where the ... don't contain any instances of x
     Push the existential in over the conjuncts and finish by applying c
     to ?x. P x
  *)
  val th0 = EXISTS_AND_CONV tm handle HOL_ERR _ => raise foo
  val tm1 = rhs (concl th0)
  val goleft = is_exists (#1 (dest_conj tm1))
  val cconval = if goleft then LAND_CONV else RAND_CONV
in
  (K th0 THENC cconval (push_in_exists_and_follow c)) tm
end handle foo => c tm
end


(* given (p \/ q \/ r..) /\ s   (with the or's right associated)
   expand to (p /\ s) \/ (q /\ s) \/ (r /\ s) \/ ...
*)
fun expand_right_and_over_or tm =
  ((REWR_CONV RIGHT_AND_OVER_OR THENC
    BINOP_CONV expand_right_and_over_or) ORELSEC ALL_CONV) tm

fun ADDITIVE_TERMS_CONV c tm =
  if is_disj tm orelse is_conj tm then
    BINOP_CONV (ADDITIVE_TERMS_CONV c) tm
  else if is_neg tm then RAND_CONV (ADDITIVE_TERMS_CONV c) tm
  else if is_less tm orelse is_divides tm orelse is_eq tm then
    BINOP_CONV c tm
  else ALL_CONV tm


end

