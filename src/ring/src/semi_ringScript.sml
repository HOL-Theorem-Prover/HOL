(*
app load ["abs_tools", "RecordType", "BasicProvers", "Datatype"];
*)
open HolKernel Parse boolLib;
open BasicProvers Datatype;
open abs_tools;  (* Rebinds Term and Define *)

val APP_DIFF = REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC);

val _ = new_theory "semi_ring";

val _ = Hol_datatype
          `semi_ring = <| SR0 : 'a;
                          SR1 : 'a;
                          SRP : 'a -> 'a -> 'a;
                          SRM : 'a -> 'a -> 'a
                       |>`;

val sr = Term`r:'a semi_ring`;
val _ = add_parameter sr;
val _ = app (C add_impl_param [sr]) ["SR0","SR1","SRP","SRM"];

val _ = app (fn s => overload_on (s, Parse.Term [QUOTE ("semi_ring_"^s)]))
        ["SR0","SR1","SRP","SRM"];

val sp_plus_sym       = Term`!n m.  SRP n m = SRP m n`;
val sp_plus_assoc     = Term`!n m p.  SRP n (SRP m p) = SRP (SRP n m) p`;
val sp_mult_sym       = Term`!n m.  SRM n m = SRM m n`;
val sp_mult_assoc     = Term`!n m p.  SRM n (SRM m p) = SRM (SRM n m) p`;
val sp_plus_zero_left = Term`!n.  SRP SR0 n = n`;
val sp_mult_one_left  = Term`!n.  SRM SR1 n = n`;
val sp_mult_zero_left = Term`!n.  SRM SR0 n = SR0`;
val sp_distr_left     = Term`!n m p.  SRM (SRP n m) p = SRP (SRM n p) (SRM m p)`;

val is_semi_ring_def = Define `
  is_semi_ring =
       ^sp_plus_sym
    /\ ^sp_plus_assoc
    /\ ^sp_mult_sym
    /\ ^sp_mult_assoc
    /\ ^sp_plus_zero_left
    /\ ^sp_mult_one_left
    /\ ^sp_mult_zero_left
    /\ ^sp_distr_left `;

(* We work on an abstract semi ring r *)
val _ = set_assums [ Term`is_semi_ring ` ];


val semi_ring_proj_tac =
  POP_ASSUM MP_TAC THEN REWRITE_TAC [is_semi_ring_def] THEN STRIP_TAC;

val plus_sym =
  asm_store_thm("plus_sym",sp_plus_sym, semi_ring_proj_tac);
val plus_assoc =
  asm_store_thm("plus_assoc",sp_plus_assoc, semi_ring_proj_tac);
val mult_sym =
  asm_store_thm("mult_sym",sp_mult_sym, semi_ring_proj_tac);
val mult_assoc =
  asm_store_thm("mult_assoc",sp_mult_assoc, semi_ring_proj_tac);
val plus_zero_left =
  asm_store_thm("plus_zero_left",sp_plus_zero_left, semi_ring_proj_tac);
val mult_one_left =
  asm_store_thm("mult_one_left",sp_mult_one_left, semi_ring_proj_tac);
val mult_zero_left =
  asm_store_thm("mult_zero_left",sp_mult_zero_left, semi_ring_proj_tac);
val distr_left =
  asm_store_thm("distr_left",sp_distr_left, semi_ring_proj_tac);


val plus_zero_right = asm_store_thm
    ("plus_zero_right",
     Term` !n. SRP n SR0 = n `,
REPEAT GEN_TAC THEN
ONCE_REWRITE_TAC [plus_sym] THEN
REWRITE_TAC [plus_zero_left]);


val mult_one_right = asm_store_thm
    ("mult_one_right",
     Term` !n. SRM n SR1 = n `,
REPEAT GEN_TAC THEN
ONCE_REWRITE_TAC [mult_sym] THEN
REWRITE_TAC [mult_one_left]);


val mult_zero_right = asm_store_thm
    ("mult_zero_right",
     Term` !n. SRM n SR0 = SR0 `,
REPEAT GEN_TAC THEN
ONCE_REWRITE_TAC [mult_sym] THEN
REWRITE_TAC [mult_zero_left]);


val distr_right = asm_store_thm
    ("distr_right",
     Term` !m n p. SRM m (SRP n p) = SRP (SRM m n) (SRM m p) `,
REPEAT GEN_TAC THEN
ONCE_REWRITE_TAC [mult_sym] THEN
REWRITE_TAC [distr_left]);



val plus_rotate = asm_store_thm
    ("plus_rotate",
     Term` !m n p. SRP (SRP m n) p = SRP (SRP n p) m `,
REPEAT GEN_TAC THEN
CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[plus_sym])) THEN
REWRITE_TAC [plus_assoc]);


val plus_permute = asm_store_thm
    ("plus_permute",
     Term` !m n p. SRP (SRP m n) p = SRP (SRP m p) n `,
ONCE_REWRITE_TAC [plus_rotate] THEN APP_DIFF THEN
PROVE_TAC[plus_sym]);


val mult_rotate = asm_store_thm
    ("mult_rotate",
     Term` !m n p. SRM (SRM m n) p = SRM (SRM n p) m `,
REPEAT GEN_TAC THEN
CONV_TAC(RAND_CONV(ONCE_REWRITE_CONV[mult_sym])) THEN
REWRITE_TAC [mult_assoc]);


val mult_permute = asm_store_thm
    ("mult_permute",
     Term` !m n p. SRM (SRM m n) p = SRM (SRM m p) n `,
ONCE_REWRITE_TAC [mult_rotate] THEN APP_DIFF THEN
PROVE_TAC[mult_sym]);


val _ = export_param_theory();
