load "holyHammer";
open holyHammer;

(*-------------------------------------------------------------------------- 
  Example 1
  -------------------------------------------------------------------------- *)

val cj = ``a ≤ b ⇒ (g ** (b − a) * g ** a = g ** b)``  
  (* hh [] cj; *)
val lemmas = [fetch "arithmetic" "SUB_ADD", fetch "arithmetic" "EXP_ADD"];
val th = save_thm ("EXP_NEG",METIS_PROVE (lemmas) cj);

(*-------------------------------------------------------------------------- 
  Example 2
  -------------------------------------------------------------------------- *)

new_theory "zerok";

val BASE_DEF = new_definition ("BASE_DEF",``BASE = @(x:num). x >= 2``);
val th0 = INST_TYPE [alpha |-> ``:num``] SELECT_AX;
val th1 = save_thm ("hh0",SPECL [``\x.x>=(2:num)``,``2:num``] th0);
val cj = ``BASE>=2``;
  (* hh [th0,th1] cj; *)
val lemmas = [fetch "zerok" "BASE_DEF", fetch "numeral" "numeral_lte",
              fetch "arithmetic" "GREATER_EQ",
              fetch "arithmetic" "NUMERAL_DEF"];

val th = save_thm ("BASE_THM",METIS_PROVE ([th0,th1] @ lemmas) cj);

(*-------------------------------------------------------------------------- 
  Example 3
  -------------------------------------------------------------------------- *)

(* Tools to fetch rewrite theorems (could be programmed using DB.match) *)

fun is_rwthm_of c (s,thm) =
  let  
    val thml = CONJUNCTS thm 
    val th1 = SPEC_ALL (hd thml)
    val tm1 = concl th1
    val (c1,_) = strip_comb (lhs tm1) 
  in
    same_const c c1 
  end
  handle _ => false

fun fetch_rwthm c = 
  let 
    val {Name,Thy,Ty} = dest_thy_const c
    val thml = DB.thms Thy
    val thml1 = filter (is_rwthm_of c) thml
  in
    (List.hd thml1)
  end

fun all_rwthm term =
  let 
    val cl = filter (not o (same_const equality)) (find_terms is_const term) 
    val cl = mk_set cl
    val thml = map fetch_rwthm cl;
  in
    thml
  end

(* Starting Proof *)

load "complexTheory";
val cj = ``i * i = -1``;
(* all_rwthm cj; *)
(* hh [complexTheory.complex_mul] cj; *)
val eqthm = REWRITE_CONV [complexTheory.complex_mul] cj;
val new_cj = rhs (concl eqthm);
(* hh [complexTheory.complex_mul] cj; *)
(* hh [] new_cj; *)
val lemmas = [fetch "complex" "complex_neg", fetch "real" "REAL_MUL_RZERO",
              fetch "real" "REAL_ADD_LID", fetch "real" "REAL_MUL_RID",
              fetch "complex" "RE", fetch "pair" "FST",
              fetch "complex" "complex_of_num",
              fetch "complex" "complex_of_real", fetch "complex" "IM",
              fetch "pair" "SND", fetch "real" "real_sub",
              fetch "real" "REAL_ADD_RINV", fetch "complex" "i"];

val th = METIS_PROVE lemmas new_cj;
val th1 = EQ_MP (SYM eqthm) th;


(*-------------------------------------------------------------------------- 
  Example 4 (turning off minimization)
  -------------------------------------------------------------------------- *)

load "complexTheory";
val cj = ``(1:complex) + 1 = 2``;
hh [] cj;
hh [complexTheory.complex_add] cj;

val lemmas = [fetch "real" "REAL_MUL_RZERO", fetch "real" "REAL_MUL_RID",
              fetch "complex" "complex_scalar_lmul",
              fetch "complex" "COMPLEX_DOUBLE",
              fetch "complex" "complex_of_num", fetch "complex" "IM",
              fetch "pair" "SND", fetch "complex" "RE",
              fetch "complex" "complex_of_real", fetch "pair" "FST"];


val th = METIS_PROVE (complexTheory.complex_add :: lemmas) cj;

load "hhReconstruct";
open hhReconstruct;
minimize_flag:= false;

hh [complexTheory.complex_add] cj;
val lemmas = [fetch "pair" "FST", fetch "complex" "complex_of_real",
              fetch "complex" "RE", fetch "pair" "SND", fetch "complex" "IM",
              fetch "complex" "complex_of_num",
              fetch "complex" "COMPLEX_DOUBLE",
              fetch "complex" "complex_scalar_lmul",
              fetch "complex" "complex_pow_def_compute",
              fetch "real" "REAL_MUL_RID", fetch "real" "REAL_MUL_RZERO"];



