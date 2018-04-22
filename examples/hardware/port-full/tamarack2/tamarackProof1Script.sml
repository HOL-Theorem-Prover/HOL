(* ===================================================================== *)
(* 22 April 2018 - adapted to HOL 4                                      *)

(* ===================================================================== *)
(* 14 June 1989 - modified for HOL88                                     *)

(* ===================================================================== *)
(* Jeff Joyce, University of Cambridge, 1 November 1988                  *)
(*                                                                       *)
(* Derive results of executing individual microinstructions.             *)


open HolKernel boolLib bossLib Parse
open proofManagerLib

val _ = new_theory "tamarackProof1";

open arithmeticTheory stringTheory pairTheory prim_recTheory

open tamarackTheory

(* Evaluate definition of Microcode *)
val Microcode_THMS =
  SIMP_RULE (list_ss++stringSimps.STRING_ss) [Cntls_def, NextMpc_def]
  Microcode_def;


val remove_quant_time_eq = prove (
``!f1 f2. (!t:time. f1 t = f2 t) <=> (f1 = \t. f2 t)``,
SIMP_TAC std_ss [FUN_EQ_THM]);

val remove_quant_time_eq_SYM = prove (
``!f1 f2. (!t:time. f1 t = f2 t) <=> (f2 = \t. f1 t)``,
SIMP_TAC std_ss [FUN_EQ_THM] >> PROVE_TAC[]);


(* The definitions contain often wires defined somehow like this

   ?w. ... /\ (!t. w t = f t) ...

   For evaluating it is nice to be able to get rid of the quantifiers. For
   this, as a first step "(!t. w t = f t)" needs changing into "w = \t. f t".
   This is achived by remove_time_quant_def_CONV *)
fun remove_time_quant_def_CONV tm = let
  val (tv, tm1) = dest_forall tm
  val _ = if (type_of tv = ``:time``) then () else failwith "remove_time_quant_def_CONV"
  val (tm_l, tm_r) = dest_eq tm1
  fun is_simple tm_s = let
    val (v, a) = dest_comb tm_s
  in is_var v andalso aconv a tv end handle HOL_ERR _ => false
in
  if is_simple tm_l then
    HO_REWR_CONV remove_quant_time_eq tm
  else if is_simple tm_r then
    HO_REWR_CONV remove_quant_time_eq_SYM tm
  else failwith "remove_time_quant_def_CONV"
end

val remove_time_quant_def_ss = simpLib.std_conv_ss
      {name = "remove_time_quant_def_CONV",
       conv = remove_time_quant_def_CONV,
       pats = [``!t:time. _ = _``]}

(* Unfold and evaluate definition of Tamarack *)
val Tamarack_EVAL_THM = save_thm ("Tamarack_EVAL_THM",
let
  (* CntlUnit unfold *)
  val thm1 = SIMP_RULE (std_ss++remove_time_quant_def_ss) [CntlUnit_def, ROM_def]
    Tamarack_def

  (* Decoder unfold *)
  val thm2 = SIMP_RULE (std_ss++remove_time_quant_def_ss) [MpcUnit_def, Decoder_def,
    AND_def, OR_def, MUX_def, HWC_def, DEL_def] thm1

  val thm3 = SIMP_RULE (std_ss++remove_time_quant_def_ss) [ADDER_def] thm2

  (* DataPath unfold *)
  val thm4 = SIMP_RULE (std_ss++remove_time_quant_def_ss) [
    DataPath_def, CheckCntls_def, REG_def, MEM_def,
    BITS_def, TNZ_def, ALU_def, PWR_def, GND_def, Update_def] thm3

  (* Expand Microcode unfold *)
  val thm5 = SIMP_RULE (std_ss++remove_time_quant_def_ss) [FORALL_AND_THM,
    PULL_EXISTS, quantHeuristicsTheory.PAIR_EQ_EXPAND] thm4

  (* Combine qualifiers *)
  val thm6 = SIMP_RULE std_ss [GSYM FORALL_AND_THM] thm5
in
  thm6
end);


(* In the following theorems of the form

  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = n) ==>
    ((mpc (t+1),mem (t+1),mar (t+1),pc (t+1),acc (t+1)) =
     XXXX)

are proved. The idea is to unfold Tamarack and then instantiate
the time variable in this unfolded version with the one we want to prove
something about. This was we can exploit "mpc t = n". This is captured by
the following tactic. *)


val MPC_n_TAC = let
  val reorder_thm = prove (``
    (!bus:bus. !t:time. Q1 t ==> P bus t ==> Q2 t) ==>
    (?bus:bus. !t:time. P bus t) ==> (!t:time. Q1 t ==> Q2 t)``,
  METIS_TAC[])
in
  REPEAT GEN_TAC THEN
  REWRITE_TAC [Tamarack_EVAL_THM] THEN
  HO_MATCH_MP_TAC reorder_thm THEN
  SIMP_TAC std_ss [Microcode_THMS, ADDn_def]
end


val MPC_0_THM = store_thm ("MPC_0_THM",
``!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 0) ==>
    ((mpc (t+1),mem (t+1),mar (t+1),pc (t+1),acc (t+1)) =
     (1,mem t,pc t,pc t,acc t))``,

MPC_n_TAC);


val MPC_1_THM = store_thm ("MPC_1_THM",
``!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 1) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),ir (t+1)) =
     (2,mem t,pc t,acc t,mem t (Bits (0,n) (mar t))))``,

MPC_n_TAC);


val MPC_2_THM = store_thm ("MPC_2_THM",
``!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 2) ==>
    ((mpc (t+1),mem (t+1),mar (t+1),pc (t+1),acc (t+1),ir (t+1)) =
     ((Bits (n,3) (ir t)) + 3,mem t,ir t,pc t,acc t,ir t))``,

MPC_n_TAC THEN
SIMP_TAC arith_ss [Bits_def] THEN
REPEAT STRIP_TAC THEN
`(ir t DIV 2 ** n) MOD 8 < 8` by (MATCH_MP_TAC MOD_LESS >> DECIDE_TAC) THEN
DECIDE_TAC)



val MPC_3_THM = store_thm ("MPC_3_THM",
``!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 3) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),ir (t+1)) =
     (((if ((acc t) = 0) then 4 else 10),mem t,pc t,acc t,ir t)))``,
MPC_n_TAC >>
SIMP_TAC arith_ss []);



val MPC_4_THM = store_thm ("MPC_4_THM",
``!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 4) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
     (0,mem t,ir t,acc t))``,

MPC_n_TAC);


val MPC_5_THM = store_thm ("MPC_5_THM",
``!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 5) ==>
    ((mpc (t+1),mem (t+1),mar (t+1),pc (t+1),acc (t+1),arg (t+1)) =
     (12,mem t,mar t,pc t,acc t,acc t))``,

MPC_n_TAC);


val MPC_6_THM = store_thm ("MPC_6_THM",
``!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 6) ==>
    ((mpc (t+1),mem (t+1),mar (t+1),pc (t+1),acc (t+1),arg (t+1)) =
     (13,mem t,mar t,pc t,acc t,acc t))``,

MPC_n_TAC);


val MPC_7_THM = store_thm ("MPC_7_THM",
``!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 7) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
     (10,mem t,pc t,mem t (Bits (0,n) (mar t))))``,

MPC_n_TAC);


val MPC_8_THM = store_thm ("MPC_8_THM",
``!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 8) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
     (10,Update (mem t,Bits (0,n) (mar t),acc t),pc t,acc t))``,

MPC_n_TAC THEN
SIMP_TAC std_ss [Update_def]);


val MPC_9_THM = store_thm ("MPC_9_THM",
``!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 9) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
     (10,mem t,pc t,acc t))``,

MPC_n_TAC);


val MPC_10_THM = store_thm ("MPC_10_THM",
``!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 10) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),buf (t+1)) =
     (11,mem t,pc t,acc t,INCn (n+3) (pc t)))``,

MPC_n_TAC);


val MPC_11_THM = store_thm ("MPC_11_THM",
``!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 11) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
     (0,mem t,buf t,acc t))``,

MPC_n_TAC);


val MPC_12_THM = store_thm ("MPC_12_THM",
``!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 12) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),buf (t+1)) =
     (14,mem t,pc t,acc t,
      ADDn (n+3) (arg t,mem t (Bits (0,n) (mar t)))))``,

MPC_n_TAC);


val MPC_13_THM = store_thm ("MPC_13_THM",
``!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 13) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1),buf (t+1)) =
     (14,mem t,pc t,acc t,
      SUBn (n+3) (arg t,mem t (Bits (0,n) (mar t)))))``,

MPC_n_TAC);


val MPC_14_THM = store_thm ("MPC_14_THM",
``!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 14) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
     (10,mem t,pc t,buf t))``,

MPC_n_TAC);


val MPC_15_THM = store_thm ("MPC_15_THM",
``!n mpc mem mar pc acc ir arg buf.
  Tamarack n (mpc,mem,mar,pc,acc,ir,arg,buf)
  ==>
  !t.
    (mpc t = 15) ==>
    ((mpc (t+1),mem (t+1),pc (t+1),acc (t+1)) =
     (0,mem t,pc t,acc t))``,

MPC_n_TAC);


val _ = export_theory ();
