(* Interactive mode
app load ["listSyntax", "combinSyntax", "state_transformerTheory"];
*)

open HolKernel boolLib Parse bossLib pairSyntax numSyntax listSyntax
  combinSyntax arithmeticTheory mesonLib simpLib boolSimps numLib
  optionTheory oneTheory listTheory combinTheory state_transformerTheory
  pairTheory;

val _ = new_theory "Encode";

infix 0 THEN |->;
infixr 1 --> by;

val arith_ss = bool_ss ++ numSimps.ARITH_ss;

(*---------------------------------------------------------------------------
        Booleans
 ---------------------------------------------------------------------------*)

val encode_bool_def = TotalDefn.Define
  `encode_bool (x : bool) = [x]`;

(*---------------------------------------------------------------------------
        Pairs
 ---------------------------------------------------------------------------*)

val encode_prod_def =
  TotalDefn.Define
  `encode_prod xb yb (x : 'a, y : 'b) : bool list = APPEND (xb x) (yb y)`;

(*---------------------------------------------------------------------------
        Sums
 ---------------------------------------------------------------------------*)

val encode_sum_def =
  TotalDefn.Define
  `(encode_sum xb yb (INL (x : 'a)) : bool list = T :: xb x) /\
   (encode_sum xb yb (INR (y : 'b)) = F :: yb y)`;

(*---------------------------------------------------------------------------
        Options
 ---------------------------------------------------------------------------*)

val encode_option_def =
  TotalDefn.Define
  `(encode_option xb NONE = [F]) /\
   (encode_option xb (SOME x) = T :: xb x)`;

(*---------------------------------------------------------------------------
        Lists
 ---------------------------------------------------------------------------*)

val encode_list_def = 
  TotalDefn.Define
  `(encode_list xb [] = [F]) /\
   (encode_list xb (x :: xs) = T :: APPEND (xb x) (encode_list xb xs))`;

(*---------------------------------------------------------------------------
        Nums (Norrish numeral encoding)
 ---------------------------------------------------------------------------*)

val (encode_num_def, encode_num_ind) =
  Defn.tprove
  (Defn.Hol_defn "encode_num"
   `encode_num (n:num) = 
    if n = 0 then [T; T]
    else if EVEN n then F :: encode_num ((n - 2) DIV 2)
    else T :: F :: encode_num ((n - 1) DIV 2)`,
   TotalDefn.WF_REL_TAC `$<` THEN
   REPEAT STRIP_TAC THEN
   (KNOW_TAC (Term`?j. n = SUC j`) THEN1 ASM_MESON_TAC [num_CASES]) THEN
   STRIP_TAC THEN
   IMP_RES_TAC EVEN_EXISTS THEN
   ASM_SIMP_TAC arith_ss
   [SUC_SUB1,MULT_DIV,DIV_LESS_EQ,
    EQT_ELIM (ARITH_CONV (Term `2n*m - 2n = (m-1n)*2n`)),
    EQT_ELIM (ARITH_CONV (Term `x < SUC y = x <= y`))]);

val _ = save_thm ("encode_num_def", encode_num_def);
val _ = save_thm ("encode_num_ind", encode_num_ind);
  
  (*--------------------------------------------------------------------
       Termination proof can also go: 

           WF_REL_TAC `$<` THEN intLib.COOPER_TAC

       but then we'd need integers.
   ----------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
      The unit type is cool because it consumes no space in the
      target list: the type has all the information!
 ---------------------------------------------------------------------------*)

val encode_unit_def =
  TotalDefn.Define `encode_unit (_ : one) : bool list = []`;

(*---------------------------------------------------------------------------*)
(* A congruence rule for encode_list                                         *)
(*---------------------------------------------------------------------------*)

val encode_list_cong = store_thm
 ("encode_list_cong",
  ``!l1 l2 f1 f2.
      (l1=l2) /\ (!x. MEM x l2 ==> (f1 x = f2 x)) 
              ==>
      (encode_list f1 l1 = encode_list f2 l2)``,
  Induct THEN SIMP_TAC list_ss [MEM,encode_list_def]
         THEN RW_TAC list_ss []);

val _ = DefnBase.write_congs (encode_list_cong::DefnBase.read_congs());


val _ = adjoin_to_theory
{sig_ps = NONE,
 struct_ps = SOME(fn ppstrm =>
   let val S = PP.add_string ppstrm
       fun NL() = PP.add_newline ppstrm
   in
  S "val _ = DefnBase.write_congs (encode_list_cong::DefnBase.read_congs());";
  NL()
  end)};


val _ = export_theory ();
