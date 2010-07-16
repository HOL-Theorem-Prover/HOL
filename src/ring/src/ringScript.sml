(*
load "abs_tools";
load "RecordType";
load "semi_ringTheory";
*)

open HolKernel Parse boolLib;
open BasicProvers Datatype;
open  abs_tools; (* Rebinds Term and Define *)

fun EQ_TRANS_TAC t = MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC t THEN CONJ_TAC;


val _ = new_theory "ring";

val _ = Hol_datatype `ring = <| R0 : 'a;
                                R1 : 'a;
                                RP : 'a -> 'a -> 'a;
                                RM : 'a -> 'a -> 'a;
                                RN : 'a -> 'a
                             |>`;

val r = --`r:'a ring`--;
val _ = app (C add_impl_param [r]) ["R0","R1","RP","RM","RN"];
val _ = app (fn s => overload_on (s, Parse.Term [QUOTE ("ring_"^s)]))
            ["R0","R1","RP","RM","RN"];

val p_plus_sym = Term`!n m.  RP n m = RP m n`;
val p_plus_assoc = Term`!n m p.  RP n (RP m p) = RP (RP n m) p`;
val p_mult_sym = Term`!n m.  RM n m = RM m n`;
val p_mult_assoc = Term`!n m p.  RM n (RM m p) = RM (RM n m) p`;
val p_plus_zero_left = Term`!n.  RP R0 n = n`;
val p_mult_one_left = Term`!n.  RM R1 n = n`;
val p_opp_def = Term`!n.  RP n (RN n) = R0`;
val p_distr_left = Term`!n m p.  RM (RP n m) p = RP (RM n p) (RM m p)`;


val is_ring_def = Define `
  is_ring ^r =
       ^p_plus_sym
    /\ ^p_plus_assoc
    /\ ^p_mult_sym
    /\ ^p_mult_assoc
    /\ ^p_plus_zero_left
    /\ ^p_mult_one_left
    /\ ^p_opp_def
    /\ ^p_distr_left `;

(* We work on an abstract_ring r *)
val _ = set_assums [ --`is_ring ^r`-- ];


val ring_proj_tac =
  POP_ASSUM MP_TAC THEN REWRITE_TAC [is_ring_def] THEN STRIP_TAC;

val plus_sym =
  asm_store_thm("plus_sym",p_plus_sym, ring_proj_tac);
val plus_assoc =
  asm_store_thm("plus_assoc",p_plus_assoc, ring_proj_tac);
val mult_sym =
  asm_store_thm("mult_sym",p_mult_sym, ring_proj_tac);
val mult_assoc =
  asm_store_thm("mult_assoc",p_mult_assoc, ring_proj_tac);
val plus_zero_left =
  asm_store_thm("plus_zero_left",p_plus_zero_left, ring_proj_tac);
val mult_one_left =
  asm_store_thm("mult_one_left",p_mult_one_left, ring_proj_tac);
val opp_def =
  asm_store_thm("opp_def",p_opp_def, ring_proj_tac);
val distr_left =
  asm_store_thm("distr_left",p_distr_left, ring_proj_tac);


val plus_zero_right = asm_store_thm
    ("plus_zero_right",
     Term` !n. RP n R0 = n `,
REPEAT GEN_TAC THEN
ONCE_REWRITE_TAC [plus_sym] THEN
REWRITE_TAC [plus_zero_left]);


val mult_zero_left = asm_store_thm
    ("mult_zero_left",
     Term` !n. RM R0 n = R0 `,
GEN_TAC THEN
EQ_TRANS_TAC(Term` RP (RM (RP R0 R0) n) (RN (RM R0 n)) `) THENL
  [ REWRITE_TAC[distr_left,GSYM plus_assoc], ALL_TAC ] THEN
REWRITE_TAC[opp_def, plus_zero_right]);

val mult_zero_right = asm_store_thm
    ("mult_zero_right",
     Term` !n. RM n R0 = R0 `,
REPEAT GEN_TAC THEN
ONCE_REWRITE_TAC [mult_sym] THEN
REWRITE_TAC [mult_zero_left]);


(* A ring is a semi_ring *)
val semi_ring_of_def = Define `semi_ring_of = (semi_ring R0 R1 RP RM) `;

val ring_is_semi_ring = asm_store_thm
    ("ring_is_semi_ring",
     Term` is_semi_ring semi_ring_of`,
RW_TAC bool_ss [ semi_ring_of_def, semi_ringTheory.is_semi_ring_def,
		 semi_ringTheory.semi_ring_accessors] THEN
MAP_FIRST MATCH_ACCEPT_TAC
  [ plus_sym,plus_assoc,mult_sym,mult_assoc,plus_zero_left,mult_one_left,
    mult_zero_left, distr_left ]);

(* Thus, we import the thms of semi_ringTheory *)
(* TODO: reexport these lemmas *)
val { plus_permute, plus_rotate, mult_permute, mult_rotate, distr_right,
      mult_one_right,...} =
  semi_ringTheory.IMPORT
    { Vals=[Term`semi_ring_of`],
      Inst=[ring_is_semi_ring],
      Rule=REWRITE_RULE[ semi_ring_of_def,
			 semi_ringTheory.semi_ring_accessors],
      Rename=K NONE }
;
val _ = asm_save_thm("mult_one_right",mult_one_right);


val neg_mult = asm_store_thm
    ("neg_mult",
     Term`!a b. RM (RN a) b = RN (RM a b)`,
REPEAT GEN_TAC THEN
EQ_TRANS_TAC(Term` RP (RM (RP a (RN a)) b) (RN (RM a b)) `) THENL
  [ REWRITE_TAC[distr_left],
    REWRITE_TAC[opp_def,mult_zero_left,plus_zero_left] ] THEN
ONCE_REWRITE_TAC[plus_permute] THEN
REWRITE_TAC[opp_def, plus_zero_left]);



val _ = export_param_theory();
