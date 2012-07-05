(* ========================================================================= *)
(* DEFINITIONAL CNF IN HOL.                                                  *)
(* Created by Joe Hurd, February 2002.                                       *)
(* ========================================================================= *)

(*
app load ["simpLib", "combinTheory", "boolSimps", "numLib", "normalForms",
          "defCNFTheory"];
guessing_tyvars := false;
*)

(*
*)
structure defCNF :> defCNF =
struct

open HolKernel Parse boolLib simpLib numLib normalForms defCNFTheory;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun ERR f s =
  HOL_ERR {message = s, origin_function = f, origin_structure = "defCNF"};

fun distinct [] = true
  | distinct (x :: rest) = not (mem x rest) andalso distinct rest;

val zero = numSyntax.zero_tm
val suc = numSyntax.suc_tm

val beq = mk_thy_const{Name = "=", Ty = bool --> bool --> bool, Thy = "min"}

fun dest_beq tm =
  let val (a, b, ty) = dest_eq_ty tm
  in if ty = bool then (a, b) else raise ERR "dest_beq" "not a bool"
  end;

val is_beq = can dest_beq;

val OKDEF = prim_mk_const{Thy = "defCNF", Name = "OKDEF"};

(* ------------------------------------------------------------------------- *)
(* Definitional Conjunctive Normal Form using variable vectors               *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (~(p = ~(q = r)) = ~(~(p = q) = r))                                     *)
(*   =                                                                       *)
(*   ?v.                                                                     *)
(*     (v 0 = (q = r)) /\ (v 1 = (p = v 0)) /\ (v 2 = (p = ~q)) /\           *)
(*     (v 3 = (v 2 = ~r)) /\ (v 4 = (v 1 = v 3)) /\ v 4                      *)
(* ------------------------------------------------------------------------- *)


fun sub_cnf f con defs (a, b) =
    let
      val (defs, a) = f defs a
      val (defs, b) = f defs b
      val tm = mk_comb (mk_comb (con, a), b)
    in
      (defs, tm)
    end;

fun def_step (defs as (vec, n, ds), tm) =
  case List.find (fn (_, b) => b = tm) ds of NONE =>
    let
      val g = mk_comb (vec, n)
      val n = rhs (concl (REDUCE_CONV (mk_comb (suc, n))))
    in
      ((vec, n, (g, tm) :: ds), g)
    end
  | SOME (v, _) => (defs, v);

fun gen_cnf defs tm =
  if is_conj tm then
    def_step (sub_cnf gen_cnf conjunction defs (dest_conj tm))
  else if is_disj tm then
    def_step (sub_cnf gen_cnf disjunction defs (dest_disj tm))
  else if is_beq tm then
    def_step (sub_cnf gen_cnf beq defs (dest_beq tm))
  else
    (defs, tm);

fun disj_cnf defs tm =
  if is_disj tm then sub_cnf disj_cnf disjunction defs (dest_disj tm)
  else gen_cnf defs tm;

fun conj_cnf defs tm =
  if is_conj tm then sub_cnf conj_cnf conjunction defs (dest_conj tm)
  else disj_cnf defs tm;

val DISCH_CONJ = CONV_RULE (REWR_CONV AND_IMP_INTRO) o uncurry DISCH;

val UNIQUE_CONV = let
  val v = mk_var("v", numSyntax.num --> bool)
in
  FIRST_CONV (map (REWR_CONV o GEN v o SYM) (CONJUNCTS UNIQUE_def))
end

val DEF_CONV = (REWR_CONV o GSYM o CONJUNCT2) DEF_def;

val FINAL_DEF_CONV =
  REWR_CONV FINAL_DEF THENC
  RAND_CONV (RATOR_CONV (RAND_CONV REDUCE_CONV));

fun TODEF_CONV tm =
  ((if is_conj tm then RAND_CONV TODEF_CONV else FINAL_DEF_CONV) THENC
   LAND_CONV UNIQUE_CONV THENC
   RAND_CONV (RATOR_CONV (RAND_CONV num_CONV)) THENC
   DEF_CONV) tm;

val AND_TRUEL_CONV = REWR_CONV (CONJUNCT1 (SPEC_ALL AND_CLAUSES));

local
  val OKDEF1_CONV = REWR_CONV (CONJUNCT1 OKDEF_def);
  val OKDEF2_CONV = REWR_CONV (CONJUNCT2 OKDEF_def);
in
  fun OKDEF_CONV tm =
    (OKDEF1_CONV ORELSEC
     (OKDEF2_CONV THENC
      LAND_CONV (REWRITE_CONV [OK_def] THENC REDUCE_CONV) THENC
      AND_TRUEL_CONV THENC
      RATOR_CONV (RAND_CONV REDUCE_CONV) THENC
      OKDEF_CONV)) tm;
end;

fun ELIM_DEFS tm =
  let
    val th1 = SYM (QUANT_CONV TODEF_CONV tm)
    val l = rand (snd (dest_exists (lhs (concl th1))))
    val th2 = OKDEF_CONV (mk_comb (mk_comb (OKDEF, zero), l))
  in
    EQ_MP th1 (MATCH_MP CONSISTENCY (EQT_ELIM th2))
  end;

val ELIM_DEFS_CONV = EQT_INTRO o ELIM_DEFS;

val pure_def_cnf_cleanup =
  CONV_RULE (LAND_CONV ((LAND_CONV ELIM_DEFS_CONV) THENC AND_TRUEL_CONV));

val dcnfgv = ref (K (genvar (num --> bool)))
val ndefs = ref T

fun PURE_DEF_CNF_VECTOR_CONV tm =
  let
    (*val (defs, tm') = conj_cnf (genvar (num --> bool), zero, []) tm*)
    val (defs, tm') = conj_cnf ((!dcnfgv)(), zero, []) tm
    val (vec, n, ds) = defs
    val _ = (ndefs:=n)
    val eqs = map mk_eq ds
    val th1 = SYM (REWRITE_CONV (map ASSUME eqs) tm')
  in
    case eqs of [] => th1
    | eq :: rest =>
    let
      val th2 = GEN vec (foldl DISCH_CONJ (DISCH eq th1) rest)
      val th3 = HO_MATCH_MP BIGSTEP th2
    in
      pure_def_cnf_cleanup th3
    end
  end;

val DEF_CNF_VECTOR_CONV =
  DEF_NNF_CONV THENC PURE_DEF_CNF_VECTOR_CONV THENC CLEANUP_DEF_CNF_CONV;

(* Quick testing
val Term = Parse.Term;
val Type = Parse.Type;
show_assums := true;
Globals.guessing_tyvars := true;
app load ["normalFormsTest", "numLib", "arithmeticTheory", "bossLib"];
open normalFormsTest numLib arithmeticTheory bossLib;
Parse.reveal "C";
val DEF_CNF_CONV' =
  time DEF_NNF_CONV THENC
  time PURE_DEF_CNF_VECTOR_CONV THENC
  time CLEANUP_DEF_CNF_CONV;

val th = DEF_CNF_CONV' ``~(p = q) ==> q /\ r``;
PRETTIFY_VARS_CONV (rhs (concl th));

try DEF_NNF_CONV ``~(p = ~(q = r)) = ~(~(p = q) = r)``;
try (DEF_CNF_CONV' THENC PRETTIFY_VARS_CONV)
  ``~(p = ~(q = r)) = ~(~(p = q) = r)``;
try DEF_CNF_CONV ``(p /\ (q \/ r /\ s)) /\ (~p \/ ~q \/ ~s)``;

(* Large formulas *)

val valid1 = time (mk_neg o Term) valid_1;

val _ = time DEF_CNF_CONV' valid1;

(* The pigeon-hole principle *)

fun test n = (((time DEF_CNF_CONV') o time (mk_neg o var_pigeon)) n; n);

test 8;
test 9;
test 10;
test 11;
test 12;
test 13;
test 14;
test 15;
test 16;
test 17;
test 18;
test 19;
test 20;

*)

end
