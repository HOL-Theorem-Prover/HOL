structure CooperSyntax :> CooperSyntax = struct

(* simple term manipulation functions, some term literals, and some
   conversions, all intended for very specific use within the
   implementation of Cooper's algorithm *)

open HolKernel boolLib intSyntax CooperThms

infix THENC ORELSEC
infixr -->

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
              (BETA_RULE (Q.SPEC `\x. ~ P x` boolTheory.NOT_EXISTS_THM))))
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



end

