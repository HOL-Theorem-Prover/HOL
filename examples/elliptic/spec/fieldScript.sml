(* ========================================================================= *)
(* Create "fieldTheory" setting up the theory of field curves                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories.                                          *)
(* (Comment out "load"s and "quietdec"s for compilation.)                    *)
(* ------------------------------------------------------------------------- *)
(*
val () = loadPath := [] @ !loadPath;
val () = app load
  ["Algebra",
   "bossLib", "metisLib", "res_quanTools",
   "optionTheory", "listTheory",
   "arithmeticTheory", "dividesTheory", "gcdTheory",
   "pred_setTheory", "pred_setSyntax",
   "primalityTools"];
val () = quietdec := true;
*)

open HolKernel Parse boolLib bossLib metisLib res_quanTools;
open optionTheory listTheory arithmeticTheory dividesTheory gcdTheory;
open pred_setTheory;
open primalityTools;
open groupTheory groupTools;

(*
val () = quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "field".                                        *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "field";

val ERR = mk_HOL_ERR "field";
val Bug = mlibUseful.Bug;
val Error = ERR "";

val Bug = fn s => (print ("\n\nBUG: " ^ s ^ "\n\n"); Bug s);

(* ------------------------------------------------------------------------- *)
(* Sort out the parser.                                                      *)
(* ------------------------------------------------------------------------- *)

val () = Parse.add_infix ("/", 600, HOLgrammars.LEFT);

(* ------------------------------------------------------------------------- *)
(* Show oracle tags.                                                         *)
(* ------------------------------------------------------------------------- *)

val () = show_tags := true;

(* ------------------------------------------------------------------------- *)
(* The subtype context.                                                      *)
(* ------------------------------------------------------------------------- *)

val context = group_context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

(* ------------------------------------------------------------------------- *)
(* Helper proof tools.                                                       *)
(* ------------------------------------------------------------------------- *)

infixr 0 <<
infixr 1 ++ || THENC ORELSEC ORELSER ## orelse_bdd_conv
infix 2 >>

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;
val REVERSE = Tactical.REVERSE;
val lemma = Tactical.prove;

val cond_rewr_conv = subtypeTools.cond_rewr_conv;

val cond_rewrs_conv = subtypeTools.cond_rewrs_conv;

val named_conv_to_simpset_conv = subtypeTools.named_conv_to_simpset_conv;

val norm_rule =
    SIMP_RULE (simpLib.++ (pureSimps.pure_ss, resq_SS))
      [GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_FORALL_IMP_THM,
       AND_IMP_INTRO, GSYM CONJ_ASSOC];

fun match_tac th =
    let
      val th = norm_rule th
      val (_,tm) = strip_forall (concl th)
    in
      (if is_imp tm then MATCH_MP_TAC else MATCH_ACCEPT_TAC) th
    end;

(* ------------------------------------------------------------------------- *)
(* Helper theorems.                                                          *)
(* ------------------------------------------------------------------------- *)

val DIV_THEN_MULT = store_thm
  ("DIV_THEN_MULT",
   ``!p q. SUC q * (p DIV SUC q) <= p``,
   NTAC 2 STRIP_TAC
   ++ Know `?r. p = (p DIV SUC q) * SUC q + r`
   >> (Know `0 < SUC q` >> DECIDE_TAC
       ++ PROVE_TAC [DIVISION])
   ++ STRIP_TAC
   ++ Suff `p = SUC q * (p DIV SUC q) + r`
   >> (POP_ASSUM_LIST (K ALL_TAC) ++ DECIDE_TAC)
   ++ PROVE_TAC [MULT_COMM]);

val MOD_EXP = store_thm
  ("MOD_EXP",
   ``!a n m. 0 < m ==> (((a MOD m) ** n) MOD m = (a ** n) MOD m)``,
   RW_TAC std_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [EXP]
   ++ MP_TAC (Q.SPEC `m` MOD_TIMES2)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ ASM_SIMP_TAC std_ss [MOD_MOD]);

val MULT_EXP = store_thm
  ("MULT_EXP",
   ``!a b n. (a * b) ** n = (a ** n) * (b ** n)``,
   RW_TAC std_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [EXP, EQ_MULT_LCANCEL, GSYM MULT_ASSOC]
   ++ RW_TAC std_ss
        [EXP, ONCE_REWRITE_RULE [MULT_COMM] EQ_MULT_LCANCEL, MULT_ASSOC]
   ++ METIS_TAC [MULT_COMM]);

val EXP_EXP = store_thm
  ("EXP_EXP",
   ``!a b c. (a ** b) ** c = a ** (b * c)``,
   RW_TAC std_ss []
   ++ Induct_on `b`
   ++ RW_TAC std_ss [EXP, MULT, EXP_1]
   ++ RW_TAC std_ss [MULT_EXP, EXP_ADD]
   ++ METIS_TAC [MULT_COMM]);

(* ========================================================================= *)
(* Fields                                                                    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The basic definitions                                                     *)
(* ------------------------------------------------------------------------- *)

val () = Hol_datatype
  `field = <| carrier : 'a -> bool;
              sum : 'a group;
              prod : 'a group |>`;

val field_accessors = fetch "-" "field_accessors";

val field_zero_def = Define `field_zero (f : 'a field) = f.sum.id`;

val field_one_def = Define `field_one (f : 'a field) = f.prod.id`;

val field_neg_def = Define `field_neg (f : 'a field) = f.sum.inv`;

val field_inv_def = Define `field_inv (f : 'a field) = f.prod.inv`;

val field_add_def = Define `field_add (f : 'a field) = f.sum.mult`;

val field_sub_def = Define
  `field_sub (f : 'a field) x y = field_add f x (field_neg f y)`;

val field_mult_def = Define `field_mult (f : 'a field) = f.prod.mult`;

val field_div_def = Define
  `field_div (f : 'a field) x y = field_mult f x (field_inv f y)`;

val field_nonzero_def = Define
  `field_nonzero f = f.carrier DIFF {field_zero f}`;

val field_num_def = Define
  `(field_num (f : 'a field) 0 = field_zero f) /\
   (field_num (f : 'a field) (SUC n) =
    field_add f (field_num f n) (field_one f))`;

val field_exp_def = Define
  `(field_exp (f : 'a field) x 0 = field_one f) /\
   (field_exp (f : 'a field) x (SUC n) = field_mult f x (field_exp f x n))`;

val Field_def = Define
  `Field =
   { (f : 'a field) |
     f.sum IN AbelianGroup /\
     f.prod IN AbelianGroup /\
     (f.sum.carrier = f.carrier) /\
     (f.prod.carrier = field_nonzero f) /\
     (!x :: (f.carrier). field_mult f (field_zero f) x = field_zero f) /\
     (!x y z :: (f.carrier).
        field_mult f x (field_add f y z) =
        field_add f (field_mult f x y) (field_mult f x z)) }`;

val FiniteField_def = Define
  `FiniteField = { (f : 'a field) | f IN Field /\ FINITE f.carrier }`;

val context = subtypeTools.add_rewrite2'' field_sub_def context;
(*val context = subtypeTools.add_rewrite2'' field_div_def context;*)
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

(* ------------------------------------------------------------------------- *)
(* Syntax operations                                                         *)
(* ------------------------------------------------------------------------- *)

val field_ty_op = "field";

fun mk_field_type ty = mk_type (field_ty_op,[ty]);

fun dest_field_type ty =
    case dest_type ty of
      (ty_op,[a]) => if ty_op = field_ty_op then a
                     else raise ERR "dest_field_type" ""
    | _ => raise ERR "dest_field_type" "";

val is_field_type = can dest_field_type;

val field_zero_tm = ``field_zero : 'a field -> 'a``;

fun mk_field_zero f =
    let
      val ty = dest_field_type (type_of f)
      val zero_tm = inst [{redex = alpha, residue = ty}] field_zero_tm
    in
      mk_comb (zero_tm,f)
    end;

fun dest_field_zero tm =
    let
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_zero_tm orelse raise ERR "dest_field_zero" ""
    in
      f
    end;

val is_field_zero = can dest_field_zero;

val field_one_tm = ``field_one : 'a field -> 'a``;

fun mk_field_one f =
    let
      val ty = dest_field_type (type_of f)
      val one_tm = inst [{redex = alpha, residue = ty}] field_one_tm
    in
      mk_comb (one_tm,f)
    end;

fun dest_field_one tm =
    let
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_one_tm orelse raise ERR "dest_field_one" ""
    in
      f
    end;

val is_field_one = can dest_field_one;

val field_num_tm = ``field_num : 'a field -> num -> 'a``;

fun mk_field_num (f,n) =
    let
      val ty = dest_field_type (type_of f)
      val num_tm = inst [{redex = alpha, residue = ty}] field_num_tm
    in
      list_mk_comb (num_tm,[f,n])
    end;

fun dest_field_num tm =
    let
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_num_tm orelse raise ERR "dest_field_num" ""
    in
      (f,x)
    end;

val is_field_num = can dest_field_num;

val field_neg_tm = ``field_neg : 'a field -> 'a -> 'a``;

fun mk_field_neg (f,x) =
    let
      val ty = dest_field_type (type_of f)
      val neg_tm = inst [{redex = alpha, residue = ty}] field_neg_tm
    in
      list_mk_comb (neg_tm,[f,x])
    end;

fun dest_field_neg tm =
    let
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_neg_tm orelse raise ERR "dest_field_neg" ""
    in
      (f,x)
    end;

val is_field_neg = can dest_field_neg;

val field_add_tm = ``field_add : 'a field -> 'a -> 'a -> 'a``;

fun mk_field_add (f,x,y) =
    let
      val ty = dest_field_type (type_of f)
      val add_tm = inst [{redex = alpha, residue = ty}] field_add_tm
    in
      list_mk_comb (add_tm,[f,x,y])
    end;

fun dest_field_add tm =
    let
      val (tm,y) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_add_tm orelse raise ERR "dest_field_add" ""
    in
      (f,x,y)
    end;

val is_field_add = can dest_field_add;

val field_sub_tm = ``field_sub : 'a field -> 'a -> 'a -> 'a``;

fun mk_field_sub (f,x,y) =
    let
      val ty = dest_field_type (type_of f)
      val sub_tm = inst [{redex = alpha, residue = ty}] field_sub_tm
    in
      list_mk_comb (sub_tm,[f,x,y])
    end;

fun dest_field_sub tm =
    let
      val (tm,y) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_sub_tm orelse raise ERR "dest_field_sub" ""
    in
      (f,x,y)
    end;

val is_field_sub = can dest_field_sub;

val field_inv_tm = ``field_inv : 'a field -> 'a -> 'a``;

fun mk_field_inv (f,x) =
    let
      val ty = dest_field_type (type_of f)
      val inv_tm = inst [{redex = alpha, residue = ty}] field_inv_tm
    in
      list_mk_comb (inv_tm,[f,x])
    end;

fun dest_field_inv tm =
    let
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_inv_tm orelse raise ERR "dest_field_inv" ""
    in
      (f,x)
    end;

val is_field_inv = can dest_field_inv;

val field_mult_tm = ``field_mult : 'a field -> 'a -> 'a -> 'a``;

fun mk_field_mult (f,x,y) =
    let
      val ty = dest_field_type (type_of f)
      val mult_tm = inst [{redex = alpha, residue = ty}] field_mult_tm
    in
      list_mk_comb (mult_tm,[f,x,y])
    end;

fun dest_field_mult tm =
    let
      val (tm,y) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_mult_tm orelse raise ERR "dest_field_mult" ""
    in
      (f,x,y)
    end;

val is_field_mult = can dest_field_mult;

val field_exp_tm = ``field_exp : 'a field -> 'a -> num -> 'a``;

fun mk_field_exp (f,x,n) =
    let
      val ty = dest_field_type (type_of f)
      val exp_tm = inst [{redex = alpha, residue = ty}] field_exp_tm
    in
      list_mk_comb (exp_tm,[f,x,n])
    end;

fun dest_field_exp tm =
    let
      val (tm,n) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_exp_tm orelse raise ERR "dest_field_exp" ""
    in
      (f,x,n)
    end;

val is_field_exp = can dest_field_exp;

val field_div_tm = ``field_div : 'a field -> 'a -> 'a -> 'a``;

fun mk_field_div (f,x,y) =
    let
      val ty = dest_field_type (type_of f)
      val div_tm = inst [{redex = alpha, residue = ty}] field_div_tm
    in
      list_mk_comb (div_tm,[f,x,y])
    end;

fun dest_field_div tm =
    let
      val (tm,y) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_div_tm orelse raise ERR "dest_field_div" ""
    in
      (f,x,y)
    end;

val is_field_div = can dest_field_div;

fun mk_field_num_mult (f,x,n) = mk_field_mult (f, mk_field_num (f,n), x);

fun dest_field_num_mult tm =
    let
      val (f,t,x) = dest_field_mult tm
      val (_,n) = dest_field_num t
    in
      (f,x,n)
    end;

val is_field_num_mult = can dest_field_num_mult;

fun field_compare (x,y) =
    case (total dest_field_num x, total dest_field_num y) of
      (NONE,NONE) => compare (x,y)
    | (SOME _, NONE) => LESS
    | (NONE, SOME _) => GREATER
    | (SOME (_,x), SOME (_,y)) => compare (x,y);

(* ------------------------------------------------------------------------- *)
(* Theorems                                                                  *)
(* ------------------------------------------------------------------------- *)

val FiniteField_Field = store_thm
  ("FiniteField_Field",
   ``!f. f IN FiniteField ==> f IN Field``,
   RW_TAC std_ss [FiniteField_def, GSPECIFICATION]);

val context = subtypeTools.add_judgement2 FiniteField_Field context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_nonzero_carrier = store_thm
  ("field_nonzero_carrier",
   ``!f :: Field. !x :: field_nonzero f. x IN f.carrier``,
   RW_TAC resq_ss [field_nonzero_def, IN_DIFF]);

val context = subtypeTools.add_judgement2 field_nonzero_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_nonzero_alt = store_thm
  ("field_nonzero_alt",
   ``!f x. x IN f.carrier /\ ~(x = field_zero f) ==> x IN field_nonzero f``,
   RW_TAC std_ss [field_nonzero_def, IN_DIFF, IN_SING]);

val field_nonzero_eq = store_thm
  ("field_nonzero_eq",
   ``!f :: Field. !x :: (f.carrier).
       ~(x = field_zero f) = x IN field_nonzero f``,
   RW_TAC std_ss [field_nonzero_def, IN_DIFF, IN_SING]);

val field_zero_carrier = store_thm
  ("field_zero_carrier",
   ``!f :: Field. field_zero f IN f.carrier``,
   RW_TAC resq_ss [Field_def, field_one_def, GSPECIFICATION, field_zero_def]
   ++ Q.UNDISCH_TAC `f.sum IN AbelianGroup`
   ++ RW_TAC std_ss [AbelianGroup_def, GSPECIFICATION, Group_def]);

val context = subtypeTools.add_reduction2 field_zero_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_one_carrier = store_thm
  ("field_one_carrier",
   ``!f :: Field. field_one f IN f.carrier``,
   RW_TAC resq_ss [Field_def, field_one_def, GSPECIFICATION, field_zero_def]
   ++ Q.UNDISCH_TAC `f.prod IN AbelianGroup`
   ++ RW_TAC std_ss
        [AbelianGroup_def, GSPECIFICATION, Group_def, IN_DIFF,
         field_nonzero_def]);

val field_one_zero = store_thm
  ("field_one_zero",
   ``!f :: Field. ~(field_one f = field_zero f)``,
   RW_TAC resq_ss
     [Field_def, field_one_def, field_zero_def, GSPECIFICATION,
      AbelianGroup_def, field_nonzero_def]
   ++ Know `f.prod.id IN f.prod.carrier`
   >> METIS_TAC [group_id_carrier]
   ++ RW_TAC std_ss [IN_DIFF, IN_SING]);

val context = subtypeTools.add_rewrite2 field_one_zero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_zero_one = store_thm
  ("field_zero_one",
   ``!f :: Field. ~(field_zero f = field_one f)``,
   RW_TAC alg_ss []);

val field_one_nonzero = store_thm
  ("field_one_nonzero",
   ``!f :: Field. field_one f IN field_nonzero f``,
   RW_TAC resq_ss
     [field_nonzero_def, IN_DIFF, IN_SING, field_one_carrier, field_one_zero]);

val context = subtypeTools.add_reduction2 field_one_nonzero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_neg_carrier = store_thm
  ("field_neg_carrier",
   ``!f :: Field. !x :: (f.carrier). field_neg f x IN f.carrier``,
   RW_TAC resq_ss [Field_def, GSPECIFICATION, field_neg_def, AbelianGroup_def]
   ++ METIS_TAC [group_inv_carrier]);

val context = subtypeTools.add_reduction2 field_neg_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_add_carrier = store_thm
  ("field_add_carrier",
   ``!f :: Field. !x y :: (f.carrier). field_add f x y IN f.carrier``,
   RW_TAC resq_ss [Field_def, GSPECIFICATION, field_add_def, AbelianGroup_def]
   ++ METIS_TAC [group_mult_carrier]);

val context = subtypeTools.add_reduction2 field_add_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_add_assoc = store_thm
  ("field_add_assoc",
   ``!f :: Field. !x y z :: (f.carrier).
       field_add f (field_add f x y) z = field_add f x (field_add f y z)``,
   RW_TAC resq_ss
     [Field_def, GSPECIFICATION, field_add_def, AbelianGroup_def,
      Group_def]);

val context = subtypeTools.add_rewrite2'' field_add_assoc context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_add_comm = store_thm
  ("field_add_comm",
   ``!f :: Field. !x y :: (f.carrier). field_add f x y = field_add f y x``,
   RW_TAC resq_ss
     [Field_def, GSPECIFICATION, field_add_def, AbelianGroup_def]);

val field_add_comm' = store_thm
  ("field_add_comm'",
   ``!f :: Field. !x y z :: (f.carrier).
        field_add f x (field_add f y z) = field_add f y (field_add f x z)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss [GSYM field_add_assoc]
   ++ METIS_TAC [field_add_comm]);

val field_num_zero = store_thm
  ("field_num_zero",
   ``!f. field_num f 0 = field_zero f``,
   RW_TAC std_ss [field_num_def]);

val context = subtypeTools.add_rewrite2 field_num_zero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_add_lzero = store_thm
  ("field_add_lzero",
   ``!f :: Field. !x :: (f.carrier). field_add f (field_zero f) x = x``,
   RW_TAC resq_ss
     [Field_def, GSPECIFICATION, field_add_def, field_zero_def,
      AbelianGroup_def]
   ++ match_tac group_lid
   ++ RW_TAC std_ss []);

val context = subtypeTools.add_rewrite2 field_add_lzero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_num_one = store_thm
  ("field_num_one",
   ``!f :: Field. field_num f 1 = field_one f``,
   REWRITE_TAC [ONE, field_num_def]
   ++ RW_TAC alg_ss []);

val context = subtypeTools.add_rewrite2'' (GSYM field_num_one) context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_add_lzero' = store_thm
  ("field_add_lzero'",
   ``!f :: Field. !x :: (f.carrier). field_add f (field_num f 0) x = x``,
   RW_TAC alg_ss [field_num_zero]);

val context = subtypeTools.add_rewrite2 field_add_lzero' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_add_rzero = store_thm
  ("field_add_rzero",
   ``!f :: Field. !x :: (f.carrier). field_add f x (field_zero f) = x``,
   METIS_TAC [field_add_lzero, field_add_comm, field_zero_carrier]);

val context = subtypeTools.add_rewrite2 field_add_rzero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_add_rzero' = store_thm
  ("field_add_rzero'",
   ``!f :: Field. !x :: (f.carrier). field_add f x (field_num f 0) = x``,
   RW_TAC alg_ss [field_num_zero]);

val context = subtypeTools.add_rewrite2 field_add_rzero' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_lneg = store_thm
  ("field_lneg",
   ``!f :: Field. !x :: (f.carrier).
       (field_add f (field_neg f x) x = field_zero f)``,
   RW_TAC resq_ss
     [Field_def, GSPECIFICATION, field_add_def, field_zero_def,
      AbelianGroup_def, field_neg_def]
   ++ match_tac group_linv
   ++ RW_TAC std_ss [IN_DIFF, IN_SING]);

val context = subtypeTools.add_rewrite2 field_lneg context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_lneg' = store_thm
  ("field_lneg'",
   ``!f :: Field. !x y :: (f.carrier).
       (field_add f (field_neg f x) (field_add f x y) = y)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss [GSYM field_add_assoc]);

val context = subtypeTools.add_rewrite2 field_lneg' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_rneg = store_thm
  ("field_rneg",
   ``!f :: Field. !x :: (f.carrier).
       (field_add f x (field_neg f x) = field_zero f)``,
   METIS_TAC [field_lneg, field_add_comm, field_neg_carrier]);

val context = subtypeTools.add_rewrite2 field_rneg context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_rneg' = store_thm
  ("field_rneg'",
   ``!f :: Field. !x y :: (f.carrier).
       (field_add f x (field_add f (field_neg f x) y) = y)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss [GSYM field_add_assoc]);

val context = subtypeTools.add_rewrite2 field_rneg' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_add_lcancel_imp = store_thm
  ("field_add_lcancel_imp",
   ``!f :: Field. !x y z :: (f.carrier).
       (field_add f x y = field_add f x z) ==> (y = z)``,
   RW_TAC resq_ss [Field_def, GSPECIFICATION, AbelianGroup_def, field_add_def]
   ++ match_tac group_lcancel_imp
   ++ Q.EXISTS_TAC `f.sum`
   ++ Q.EXISTS_TAC `x`
   ++ RW_TAC std_ss []);

val field_add_lcancel = store_thm
  ("field_add_lcancel",
   ``!f :: Field. !x y z :: (f.carrier).
       (field_add f x y = field_add f x z) = (y = z)``,
   METIS_TAC [field_add_lcancel_imp]);

val context = subtypeTools.add_rewrite2' field_add_lcancel context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_add_rcancel_imp = store_thm
  ("field_add_rcancel_imp",
   ``!f :: Field. !x y z :: (f.carrier).
       (field_add f y x = field_add f z x) ==> (y = z)``,
   METIS_TAC [field_add_lcancel_imp, field_add_comm]);

val field_add_rcancel = store_thm
  ("field_add_rcancel",
   ``!f :: Field. !x y z :: (f.carrier).
       (field_add f y x = field_add f z x) = (y = z)``,
   METIS_TAC [field_add_rcancel_imp]);

val context = subtypeTools.add_rewrite2' field_add_rcancel context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_inv_nonzero = store_thm
  ("field_inv_nonzero",
   ``!f :: Field. !x :: field_nonzero f. field_inv f x IN field_nonzero f``,
   RW_TAC resq_ss [Field_def, GSPECIFICATION, field_nonzero_def]
   ++ Suff `field_inv f x IN f.prod.carrier`
   >> RW_TAC std_ss []
   ++ Know `x IN f.prod.carrier`
   >> RW_TAC std_ss [IN_DIFF, IN_INSERT, NOT_IN_EMPTY]
   ++ Q.UNDISCH_TAC `f.prod IN AbelianGroup`
   ++ POP_ASSUM_LIST (K ALL_TAC)
   ++ RW_TAC std_ss
        [AbelianGroup_def, GSPECIFICATION, Group_def, field_inv_def]);

val context = subtypeTools.add_reduction2 field_inv_nonzero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_lzero = store_thm
  ("field_mult_lzero",
   ``!f :: Field. !x :: (f.carrier).
       field_mult f (field_zero f) x = field_zero f``,
   RW_TAC resq_ss [Field_def, GSPECIFICATION]);

val context = subtypeTools.add_rewrite2 field_mult_lzero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_lzero' = store_thm
  ("field_mult_lzero'",
   ``!f :: Field. !x :: (f.carrier).
       field_mult f (field_num f 0) x = field_zero f``,
   RW_TAC alg_ss [field_num_zero]);

val context = subtypeTools.add_rewrite2 field_mult_lzero' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_distrib_ladd = store_thm
  ("field_distrib_ladd",
   ``!f :: Field. !x y z :: (f.carrier).
       field_mult f x (field_add f y z) =
       field_add f (field_mult f x y) (field_mult f x z)``,
   RW_TAC resq_ss [Field_def, GSPECIFICATION]);

(***
val context = subtypeTools.add_rewrite2'' field_distrib_ladd context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;
***)

val field_mult_rzero = store_thm
  ("field_mult_rzero",
   ``!f :: Field. !x :: (f.carrier).
       field_mult f x (field_zero f) = field_zero f``,
   RW_TAC resq_ss []
   ++ Cases_on `x = field_zero f`
   >> METIS_TAC [field_mult_lzero]
   ++ Know `field_mult f x (field_zero f) IN f.carrier`
   >> (Suff
         `field_mult f x (field_add f (field_one f) (field_neg f (field_one f)))
          IN f.carrier`
       >> RW_TAC alg_ss [field_rneg]
       ++ RW_TAC alg_ss [field_distrib_ladd]
       ++ match_tac field_add_carrier
       ++ Q.UNDISCH_TAC `f IN Field`
       ++ RW_TAC std_ss
            [GSPECIFICATION, Field_def, AbelianGroup_def, field_one_def,
             field_mult_def, field_neg_def, field_nonzero_def]
       >> (Suff `f.prod.mult x f.prod.id IN f.prod.carrier`
           >> RW_TAC std_ss [IN_DIFF]
           ++ match_tac group_mult_carrier
           ++ RW_TAC std_ss [group_id_carrier, IN_DIFF, IN_SING])
       ++ Suff `f.prod.mult x (f.sum.inv f.prod.id) IN f.prod.carrier`
       >> RW_TAC std_ss [IN_DIFF]
       ++ Q.PAT_ASSUM `f.sum.carrier = f.carrier`
            (MP_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ])
       ++ STRIP_TAC
       ++ match_tac group_mult_carrier
       ++ ASM_SIMP_TAC std_ss [IN_DIFF, IN_SING]
       ++ Know `f.prod.id IN f.prod.carrier`
       >> RW_TAC std_ss [group_id_carrier]
       ++ ASM_SIMP_TAC std_ss [IN_DIFF, IN_SING]
       ++ FULL_SIMP_TAC std_ss [field_zero_def]
       ++ RW_TAC std_ss []
       >> (match_tac group_inv_carrier
           ++ RW_TAC std_ss [])
       ++ STRIP_TAC
       ++ Q.PAT_ASSUM `~(X = Y)` MP_TAC
       ++ RW_TAC std_ss []
       ++ match_tac group_lcancel_imp
       ++ Q.EXISTS_TAC `f.sum`
       ++ Q.EXISTS_TAC `f.sum.inv f.prod.id`
       ++ CONJ_TAC >> METIS_TAC [group_linv, group_id_carrier]
       ++ CONJ_TAC >> METIS_TAC [group_linv, group_id_carrier]
       ++ CONJ_TAC >> METIS_TAC [group_linv, group_id_carrier]
       ++ CONJ_TAC >> METIS_TAC [group_linv, group_id_carrier]
       ++ POP_ASSUM (fn th => CONV_TAC (RAND_CONV (REWRITE_CONV [th])))
       ++ RW_TAC std_ss [group_linv, group_lid, group_id_carrier])
   ++ RW_TAC std_ss []
   ++ Suff
        `field_add f (field_mult f x (field_zero f))
                     (field_mult f x (field_zero f)) =
         field_add f (field_zero f) (field_mult f x (field_zero f))`
   >> RW_TAC alg_ss []
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC
        `field_mult f x (field_add f (field_zero f) (field_zero f))`
   ++ REVERSE CONJ_TAC
   >> RW_TAC alg_ss []
   ++ MATCH_MP_TAC EQ_SYM
   ++ match_tac field_distrib_ladd
   ++ RW_TAC alg_ss []);

val context = subtypeTools.add_rewrite2 field_mult_rzero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_rzero' = store_thm
  ("field_mult_rzero'",
   ``!f :: Field. !x :: (f.carrier).
       field_mult f x (field_num f 0) = field_zero f``,
   RW_TAC alg_ss [field_num_zero]);

val context = subtypeTools.add_rewrite2 field_mult_rzero' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_nonzero = store_thm
  ("field_mult_nonzero",
   ``!f :: Field. !x y :: field_nonzero f.
       field_mult f x y IN field_nonzero f``,
   RW_TAC resq_ss
     [Field_def, GSPECIFICATION, field_mult_def, AbelianGroup_def,
      field_nonzero_def]
   ++ Suff `f.prod.mult x y IN f.prod.carrier`
   >> RW_TAC std_ss []
   ++ match_tac group_mult_carrier
   ++ RW_TAC std_ss []);

val context = subtypeTools.add_reduction2 field_mult_nonzero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_carrier = store_thm
  ("field_mult_carrier",
   ``!f :: Field. !x y :: (f.carrier). field_mult f x y IN f.carrier``,
   RW_TAC resq_ss []
   ++ Cases_on `x = field_zero f`
   >> RW_TAC std_ss [field_mult_lzero]
   ++ Cases_on `y = field_zero f`
   >> RW_TAC std_ss [field_mult_rzero]
   ++ match_tac field_nonzero_carrier
   ++ RW_TAC std_ss []
   ++ match_tac field_mult_nonzero
   ++ RW_TAC std_ss [field_nonzero_def, IN_DIFF, IN_SING]);

val context = subtypeTools.add_reduction2 field_mult_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_assoc = store_thm
  ("field_mult_assoc",
   ``!f :: Field. !x y z :: (f.carrier).
       field_mult f (field_mult f x y) z = field_mult f x (field_mult f y z)``,
   RW_TAC resq_ss []
   ++ Cases_on `x = field_zero f`
   >> RW_TAC std_ss [field_mult_lzero, field_mult_rzero, field_mult_carrier]
   ++ Cases_on `y = field_zero f`
   >> RW_TAC std_ss [field_mult_lzero, field_mult_rzero, field_mult_carrier]
   ++ Cases_on `z = field_zero f`
   >> RW_TAC std_ss [field_mult_lzero, field_mult_rzero, field_mult_carrier]
   ++ Q.UNDISCH_TAC `f IN Field`
   ++ RW_TAC std_ss
        [Field_def, GSPECIFICATION, field_add_def, AbelianGroup_def,
         Group_def, field_mult_def, field_nonzero_def]
   ++ FIRST_ASSUM match_tac
   ++ RW_TAC std_ss [IN_DIFF, IN_SING]);

val context = subtypeTools.add_rewrite2'' field_mult_assoc context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_comm = store_thm
  ("field_mult_comm",
   ``!f :: Field. !x y :: (f.carrier). field_mult f x y = field_mult f y x``,
   RW_TAC resq_ss []
   ++ Cases_on `x = field_zero f`
   >> RW_TAC std_ss [field_mult_lzero, field_mult_rzero]
   ++ Cases_on `y = field_zero f`
   >> RW_TAC std_ss [field_mult_lzero, field_mult_rzero]
   ++ Q.UNDISCH_TAC `f IN Field`
   ++ RW_TAC std_ss
        [Field_def, GSPECIFICATION, field_mult_def, AbelianGroup_def,
         field_nonzero_def]
   ++ Q.PAT_ASSUM `!x y :: (f.prod.carrier). P x y` match_tac
   ++ RW_TAC std_ss [IN_DIFF, IN_INSERT, NOT_IN_EMPTY]);

val field_mult_comm' = store_thm
  ("field_mult_comm'",
   ``!f :: Field. !x y z :: (f.carrier).
        field_mult f x (field_mult f y z) = field_mult f y (field_mult f x z)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss [GSYM field_mult_assoc]
   ++ METIS_TAC [field_mult_comm]);

val field_entire = store_thm
  ("field_entire",
   ``!f :: Field. !x y :: (f.carrier).
       (field_mult f x y = field_zero f) =
       (x = field_zero f) \/ (y = field_zero f)``,
   RW_TAC resq_ss []
   ++ REVERSE EQ_TAC
   >> (STRIP_TAC ++ RW_TAC std_ss [field_mult_lzero, field_mult_rzero])
   ++ MATCH_MP_TAC (PROVE [] ``(~b ==> ~a) ==> (a ==> b)``)
   ++ Know `field_mult f x y IN f.carrier`
   >> METIS_TAC [field_mult_carrier]
   ++ RW_TAC std_ss []
   ++ Q.UNDISCH_TAC `f IN Field`
   ++ RW_TAC std_ss
        [Field_def, GSPECIFICATION, AbelianGroup_def, field_nonzero_def]
   ++ Suff `f.prod.mult x y IN f.prod.carrier`
   >> RW_TAC std_ss [IN_DIFF, IN_INSERT, NOT_IN_EMPTY, field_mult_def]
   ++ match_tac group_mult_carrier
   ++ RW_TAC std_ss [IN_DIFF, IN_INSERT, NOT_IN_EMPTY]);

val context = subtypeTools.add_rewrite2' field_entire context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_lone = store_thm
  ("field_mult_lone",
   ``!f :: Field. !x :: (f.carrier). field_mult f (field_one f) x = x``,
   RW_TAC resq_ss []
   ++ Cases_on `x = field_zero f`
   >> RW_TAC std_ss [field_mult_rzero, field_one_carrier]
   ++ Q.UNDISCH_TAC `f IN Field`
   ++ RW_TAC std_ss
        [Field_def, GSPECIFICATION, field_mult_def, field_one_def,
         AbelianGroup_def, field_nonzero_def]
   ++ match_tac group_lid
   ++ RW_TAC std_ss [IN_DIFF, IN_INSERT, NOT_IN_EMPTY]);

val context = subtypeTools.add_rewrite2 field_mult_lone context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_lone' = store_thm
  ("field_mult_lone'",
   ``!f :: Field. !x :: (f.carrier). field_mult f (field_num f 1) x = x``,
   RW_TAC alg_ss [field_num_one]);

val context = subtypeTools.add_rewrite2 field_mult_lone' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_rone = store_thm
  ("field_mult_rone",
   ``!f :: Field. !x :: (f.carrier). field_mult f x (field_one f) = x``,
   METIS_TAC [field_mult_lone, field_mult_comm, field_one_carrier]);

val context = subtypeTools.add_rewrite2 field_mult_rone context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_rone' = store_thm
  ("field_mult_rone'",
   ``!f :: Field. !x :: (f.carrier). field_mult f x (field_num f 1) = x``,
   RW_TAC alg_ss [field_num_one]);

val context = subtypeTools.add_rewrite2 field_mult_rone' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_linv = store_thm
  ("field_linv",
   ``!f :: Field. !x :: field_nonzero f.
       field_mult f (field_inv f x) x = field_one f``,
   RW_TAC resq_ss
     [Field_def, GSPECIFICATION, field_mult_def, field_one_def,
      AbelianGroup_def, field_inv_def, field_nonzero_def]
   ++ match_tac group_linv
   ++ RW_TAC std_ss []);

val context = subtypeTools.add_rewrite2 field_linv context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_linv' = store_thm
  ("field_linv'",
   ``!f :: Field. !x :: field_nonzero f. !y :: (f.carrier).
       (field_mult f (field_inv f x) (field_mult f x y) = y)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss [GSYM field_mult_assoc]);

val context = subtypeTools.add_rewrite2 field_linv' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_rinv = store_thm
  ("field_rinv",
   ``!f :: Field. !x :: field_nonzero f.
       (field_mult f x (field_inv f x) = field_one f)``,
   METIS_TAC
     [field_linv, field_mult_comm, field_inv_nonzero, field_nonzero_carrier]);

val context = subtypeTools.add_rewrite2 field_rinv context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_rinv' = store_thm
  ("field_rinv'",
   ``!f :: Field. !x :: field_nonzero f. !y :: (f.carrier).
       (field_mult f x (field_mult f (field_inv f x) y) = y)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss [GSYM field_mult_assoc]);

val context = subtypeTools.add_rewrite2 field_rinv' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_lcancel_imp = store_thm
  ("field_mult_lcancel_imp",
   ``!f :: Field. !x :: field_nonzero f. !y z :: (f.carrier).
       (field_mult f x y = field_mult f x z) ==> (y = z)``,
   RW_TAC resq_ss [field_nonzero_def, IN_DIFF, IN_SING]
   ++ POP_ASSUM MP_TAC
   ++ Cases_on `y = field_zero f`
   >> RW_TAC std_ss [field_mult_rzero, field_entire]
   ++ Cases_on `z = field_zero f`
   >> RW_TAC std_ss [field_mult_rzero, field_entire]
   ++ Q.UNDISCH_TAC `f IN Field`
   ++ RW_TAC std_ss
        [field_mult_def, Field_def, GSPECIFICATION, AbelianGroup_def,
         field_nonzero_def]
   ++ match_tac group_lcancel_imp
   ++ Q.EXISTS_TAC `f.prod`
   ++ Q.EXISTS_TAC `x`
   ++ RW_TAC std_ss [IN_DIFF, IN_INSERT, NOT_IN_EMPTY]);

val field_mult_lcancel = store_thm
  ("field_mult_lcancel",
   ``!f :: Field. !x :: field_nonzero f. !y z :: (f.carrier).
       (field_mult f x y = field_mult f x z) = (y = z)``,
   METIS_TAC [field_mult_lcancel_imp]);

val context = subtypeTools.add_rewrite2' field_mult_lcancel context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_rcancel_imp = store_thm
  ("field_mult_rcancel_imp",
   ``!f :: Field. !x :: field_nonzero f. !y z :: (f.carrier).
       (field_mult f y x = field_mult f z x) ==> (y = z)``,
   METIS_TAC [field_mult_lcancel_imp, field_mult_comm, field_nonzero_carrier]);

val field_mult_rcancel = store_thm
  ("field_mult_rcancel",
   ``!f :: Field. !x :: field_nonzero f. !y z :: (f.carrier).
       (field_mult f y x = field_mult f z x) = (y = z)``,
   METIS_TAC [field_mult_rcancel_imp]);

val context = subtypeTools.add_rewrite2' field_mult_rcancel context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_neg_neg = store_thm
  ("field_neg_neg",
   ``!f :: Field. !x :: (f.carrier). field_neg f (field_neg f x) = x``,
   RW_TAC resq_ss [field_neg_def, Field_def, GSPECIFICATION, AbelianGroup_def]
   ++ METIS_TAC [group_inv_inv]);

val context = subtypeTools.add_rewrite2 field_neg_neg context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_neg_cancel = store_thm
  ("field_neg_cancel",
   ``!f :: Field. !x y :: (f.carrier).
       (field_neg f x = field_neg f y) = (x = y)``,
   RW_TAC resq_ss [field_neg_def, Field_def, GSPECIFICATION, AbelianGroup_def]
   ++ METIS_TAC [group_inv_cancel]);

val context = subtypeTools.add_rewrite2 field_neg_cancel context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_neg_cancel_imp = store_thm
  ("field_neg_cancel_imp",
   ``!f :: Field. !x y :: (f.carrier).
       (field_neg f x = field_neg f y) ==> (x = y)``,
   METIS_TAC [field_neg_cancel]);

val field_neg_eq_swap_imp = store_thm
  ("field_neg_eq_swap_imp",
   ``!f :: Field. !x y :: (f.carrier).
       (field_neg f x = y) ==> (x = field_neg f y)``,
   METIS_TAC [field_neg_neg]);

val field_neg_eq_swap = store_thm
  ("field_neg_eq_swap",
   ``!f :: Field. !x y :: (f.carrier).
       (field_neg f x = y) = (x = field_neg f y)``,
   METIS_TAC [field_neg_eq_swap_imp]);

val field_neg_eq_swap_imp' = store_thm
  ("field_neg_eq_swap_imp'",
   ``!f :: Field. !x y :: (f.carrier).
       (x = field_neg f y) ==> (field_neg f x = y)``,
   METIS_TAC [field_neg_eq_swap]);

val field_neg_eq_imp = store_thm
  ("field_neg_eq_imp",
   ``!f :: Field. !x y :: (f.carrier).
       (field_neg f x = y) ==> (field_add f x y = field_zero f)``,
   RW_TAC resq_ss [field_rneg]);

val field_neg_eq_imp' = store_thm
  ("field_neg_eq_imp'",
   ``!f :: Field. !x y :: (f.carrier).
       (field_add f x y = field_zero f) ==> (field_neg f x = y)``,
   RW_TAC resq_ss []
   ++ match_tac field_add_lcancel_imp
   ++ Q.EXISTS_TAC `f`
   ++ Q.EXISTS_TAC `x`
   ++ RW_TAC std_ss [field_neg_carrier, field_rneg]);

val field_neg_eq = store_thm
  ("field_neg_eq",
   ``!f :: Field. !x y :: (f.carrier).
       (field_neg f x = y) = (field_add f x y = field_zero f)``,
   METIS_TAC [field_neg_eq_imp, field_neg_eq_imp']);

val field_neg_zero = store_thm
  ("field_neg_zero",
   ``!f :: Field. field_neg f (field_zero f) = field_zero f``,
   RW_TAC resq_ss
     [Field_def, GSPECIFICATION, AbelianGroup_def, field_zero_def,
      field_neg_def]
   ++ METIS_TAC [group_inv_id]);

val context = subtypeTools.add_rewrite2 field_neg_zero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_add_eq = store_thm
  ("field_add_eq",
   ``!f x1 y1 x2 y2.
       (x1 = x2) /\ (y1 = y2) ==> (field_add f x1 y1 = field_add f x2 y2)``,
   RW_TAC std_ss []);

val field_distrib_radd = store_thm
  ("field_distrib_radd",
   ``!f :: Field. !x y z :: (f.carrier).
       field_mult f (field_add f y z) x =
       field_add f (field_mult f y x) (field_mult f z x)``,
   RW_TAC resq_ss []
   ++ METIS_TAC [field_mult_comm, field_add_carrier, field_distrib_ladd]);

(***
val context = subtypeTools.add_rewrite2'' field_distrib_radd context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;
***)

val field_distrib = save_thm
  ("field_distrib", CONJ field_distrib_ladd field_distrib_radd);

val field_mult_lneg = store_thm
  ("field_mult_lneg",
   ``!f :: Field. !x y :: (f.carrier).
       field_mult f (field_neg f x) y = field_neg f (field_mult f x y)``,
   RW_TAC resq_ss []
   ++ match_tac (GSYM field_neg_eq_imp')
   ++ RW_TAC std_ss [field_mult_carrier, field_neg_carrier]
   ++ RW_TAC std_ss
        [GSYM field_distrib_radd, field_neg_carrier, field_rneg,
         field_mult_lzero]);

val context = subtypeTools.add_rewrite2 field_mult_lneg context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_rneg = store_thm
  ("field_mult_rneg",
   ``!f :: Field. !x y :: (f.carrier).
       field_mult f x (field_neg f y) = field_neg f (field_mult f x y)``,
   METIS_TAC [field_mult_lneg, field_mult_comm, field_neg_carrier]);

val context = subtypeTools.add_rewrite2 field_mult_rneg context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_inv_mult' = store_thm
  ("field_inv_mult'",
   ``!f :: Field. !x y :: field_nonzero f.
       field_inv f (field_mult f x y) =
       field_mult f (field_inv f y) (field_inv f x)``,
   RW_TAC resq_ss
     [field_mult_def, Field_def, GSPECIFICATION, field_inv_def,
      AbelianGroup_def, field_nonzero_def]
   ++ match_tac group_inv_mult
   ++ RW_TAC std_ss []);

val field_inv_mult = store_thm
  ("field_inv_mult",
   ``!f :: Field. !x y :: field_nonzero f.
       field_inv f (field_mult f x y) =
       field_mult f (field_inv f x) (field_inv f y)``,
   METIS_TAC [field_inv_nonzero, field_nonzero_carrier, field_mult_comm,
              field_inv_mult']);

val context = subtypeTools.add_rewrite2'' field_inv_mult context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_exp_carrier = store_thm
  ("field_exp_carrier",
   ``!f :: Field. !x :: (f.carrier). !n. field_exp f x n IN f.carrier``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [field_exp_def, field_one_carrier, field_mult_carrier]);

val context = subtypeTools.add_reduction2 field_exp_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_exp_nonzero = store_thm
  ("field_exp_nonzero",
   ``!f :: Field. !x :: field_nonzero f. !n.
       field_exp f x n IN field_nonzero f``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [field_exp_def, field_one_nonzero, field_mult_nonzero]);

val context = subtypeTools.add_reduction2 field_exp_nonzero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_num_carrier = store_thm
  ("field_num_carrier",
   ``!f :: Field. !n. field_num f n IN f.carrier``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC alg_ss [field_num_def]);

val context = subtypeTools.add_reduction2 field_num_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_small = store_thm
  ("field_mult_small",
   ``!f :: Field. !x :: (f.carrier).
       (field_mult f (field_num f 0) x = field_zero f) /\
       (field_mult f (field_num f 1) x = x) /\
       (field_mult f (field_num f 2) x = field_add f x x) /\
       (field_mult f (field_num f 3) x =
        field_add f x (field_mult f (field_num f 2) x))``,
   RW_TAC (simpLib.++ (std_ss, numSimps.SUC_FILTER_ss)) [field_num_def]
   ++ RW_TAC alg_ss [field_distrib_radd, field_add_assoc]);

val field_exp_small = store_thm
  ("field_exp_small",
   ``!f :: Field. !x :: (f.carrier).
       (field_exp f x 0 = field_one f) /\
       (field_exp f x 1 = x) /\
       (field_exp f x 2 = field_mult f x x) /\
       (field_exp f x 3 = field_mult f x (field_exp f x 2)) /\
       (field_exp f x 4 = field_mult f x (field_exp f x 3)) /\
       (field_exp f x 5 = field_mult f x (field_exp f x 4)) /\
       (field_exp f x 6 = field_mult f x (field_exp f x 5)) /\
       (field_exp f x 7 = field_mult f x (field_exp f x 6)) /\
       (field_exp f x 8 = field_mult f x (field_exp f x 7)) /\
       (field_exp f x 9 = field_mult f x (field_exp f x 8))``,
   RW_TAC (simpLib.++ (std_ss, numSimps.SUC_FILTER_ss))
     [field_exp_def, field_mult_rone]);

val field_inv_one = store_thm
  ("field_inv_one",
   ``!f :: Field. field_inv f (field_one f) = field_one f``,
   RW_TAC resq_ss [field_inv_def, field_one_def, Field_def, GSPECIFICATION]
   ++ RW_TAC alg_ss []);

val context = subtypeTools.add_rewrite2 field_inv_one context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_exp_zero = store_thm
  ("field_exp_zero",
   ``!f :: Field. !x :: (f.carrier). field_exp f x 0 = field_one f``,
   RW_TAC alg_ss [field_exp_def]);

val context = subtypeTools.add_rewrite2 field_exp_zero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_exp_one = store_thm
  ("field_exp_one",
   ``!f :: Field. !x :: (f.carrier). field_exp f x 1 = x``,
   REWRITE_TAC [ONE, field_exp_def]
   ++ RW_TAC alg_ss []);

val context = subtypeTools.add_rewrite2 field_exp_one context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_neg_add' = store_thm
  ("field_neg_add'",
   ``!f :: Field. !x y :: (f.carrier).
       field_neg f (field_add f x y) =
       field_add f (field_neg f y) (field_neg f x)``,
   RW_TAC resq_ss
     [field_add_def, Field_def, GSPECIFICATION, field_neg_def,
      AbelianGroup_def]
   ++ match_tac group_inv_mult
   ++ RW_TAC std_ss []);

val field_neg_add = store_thm
  ("field_neg_add",
   ``!f :: Field. !x y :: (f.carrier).
       field_neg f (field_add f x y) =
       field_add f (field_neg f x) (field_neg f y)``,
   METIS_TAC [field_neg_carrier, field_add_comm, field_neg_add']);

val context = subtypeTools.add_rewrite2'' field_neg_add context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_exp_suc = store_thm
  ("field_exp_suc",
   ``!f :: Field. !x :: (f.carrier). !n.
       field_exp f x (SUC n) = field_mult f (field_exp f x n) x``,
   RW_TAC alg_ss [field_exp_def]
   ++ METIS_TAC [field_mult_comm, field_exp_carrier]);

val field_num_suc = store_thm
  ("field_num_suc",
   ``!f :: Field. !n.
       field_num f (SUC n) = field_add f (field_one f) (field_num f n)``,
   RW_TAC alg_ss [field_num_def]
   ++ METIS_TAC [field_add_comm, field_one_carrier, field_num_carrier]);

val field_num_add = store_thm
  ("field_num_add",
   ``!f :: Field. !m n.
       field_add f (field_num f m) (field_num f n) = field_num f (m + n)``,
   RW_TAC resq_ss []
   ++ Induct_on `m`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_num_suc, ADD, field_add_assoc]);

val context = subtypeTools.add_rewrite2 field_num_add context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_num_add' = store_thm
  ("field_num_add'",
   ``!f :: Field. !m n. !x :: (f.carrier).
       field_add f (field_num f m) (field_add f (field_num f n) x) =
       field_add f (field_num f (m + n)) x``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_num_add]);

val context = subtypeTools.add_rewrite2'' field_num_add' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_num_mult = store_thm
  ("field_num_mult",
   ``!f :: Field. !m n.
       field_mult f (field_num f m) (field_num f n) = field_num f (m * n)``,
   RW_TAC resq_ss []
   ++ Induct_on `m`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_num_def, MULT, field_distrib_radd]);

val context = subtypeTools.add_rewrite2 field_num_mult context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_num_mult' = store_thm
  ("field_num_mult'",
   ``!f :: Field. !m n. !x :: (f.carrier).
       field_mult f (field_num f m) (field_mult f (field_num f n) x) =
       field_mult f (field_num f (m * n)) x``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_num_mult]);

val context = subtypeTools.add_rewrite2'' field_num_mult' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_num_exp = store_thm
  ("field_num_exp",
   ``!f :: Field. !m n.
       field_exp f (field_num f m) n = field_num f (m ** n)``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC alg_ss [EXP, field_num_one, field_exp_def]);

val context = subtypeTools.add_rewrite2 field_num_exp context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_single_add_single = store_thm
  ("field_single_add_single",
   ``!f :: Field. !x :: (f.carrier).
       field_add f x x = field_mult f (field_num f 2) x``,
   RW_TAC alg_ss [field_mult_small]);

val context = subtypeTools.add_rewrite2'' field_single_add_single context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_single_add_single' = store_thm
  ("field_single_add_single'",
   ``!f :: Field. !x y :: (f.carrier).
       field_add f x (field_add f x y) =
       field_add f (field_mult f (field_num f 2) x) y``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_single_add_single]);

val context = subtypeTools.add_rewrite2'' field_single_add_single' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_single_add_mult = store_thm
  ("field_single_add_mult",
   ``!f :: Field. !x :: (f.carrier). !n.
       field_add f x (field_mult f (field_num f n) x) =
       field_mult f (field_num f (n + 1)) x``,
   RW_TAC bool_ss [field_num_suc, GSYM ADD1]
   ++ RW_TAC alg_ss [field_distrib_radd]);

val context = subtypeTools.add_rewrite2'' field_single_add_mult context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_single_add_mult' = store_thm
  ("field_single_add_mult'",
   ``!f :: Field. !x y :: (f.carrier). !n.
       field_add f x (field_add f (field_mult f (field_num f n) x) y) =
       field_add f (field_mult f (field_num f (n + 1)) x) y``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_single_add_mult]);

val context = subtypeTools.add_rewrite2'' field_single_add_mult' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_single_add_neg_mult = store_thm
  ("field_single_add_neg_mult",
   ``!f :: Field. !x :: (f.carrier). !n.
       field_add f x (field_neg f (field_mult f (field_num f n) x)) =
       (if n = 0 then x
        else field_neg f (field_mult f (field_num f (n - 1)) x))``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss []
   ++ Cases_on `n`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_num_suc, field_distrib_radd]
   ++ RW_TAC alg_ss [field_neg_add, GSYM field_add_assoc]);

val context = subtypeTools.add_rewrite2'' field_single_add_neg_mult context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_single_add_neg_mult' = store_thm
  ("field_single_add_neg_mult'",
   ``!f :: Field. !x y :: (f.carrier). !n.
       field_add f x
         (field_add f (field_neg f (field_mult f (field_num f n) x)) y) =
       (if n = 0 then field_add f x y
        else field_add f
               (field_neg f (field_mult f (field_num f (n - 1)) x)) y)``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_single_add_neg_mult]
   ++ RW_TAC resq_ss []
   ++ RW_TAC resq_ss []);

val context = subtypeTools.add_rewrite2'' field_single_add_neg_mult' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_add_mult = store_thm
  ("field_mult_add_mult",
   ``!f :: Field. !x :: (f.carrier). !m n.
       field_add f (field_mult f (field_num f m) x)
         (field_mult f (field_num f n) x) =
       field_mult f (field_num f (m + n)) x``,
   RW_TAC resq_ss []
   ++ Induct_on `m`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_num_suc, field_distrib_radd, ADD]
   ++ POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
   ++ RW_TAC alg_ss [field_add_assoc]);

val context = subtypeTools.add_rewrite2'' field_mult_add_mult context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_add_mult' = store_thm
  ("field_mult_add_mult'",
   ``!f :: Field. !x y :: (f.carrier). !m n.
       field_add f (field_mult f (field_num f m) x)
         (field_add f (field_mult f (field_num f n) x) y) =
       field_add f (field_mult f (field_num f (m + n)) x) y``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_mult_add_mult]);

val context = subtypeTools.add_rewrite2'' field_mult_add_mult' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_add_neg = store_thm
  ("field_mult_add_neg",
   ``!f :: Field. !x :: (f.carrier). !n.
       field_add f (field_mult f (field_num f n) x) (field_neg f x) =
       (if n = 0 then field_neg f x
        else field_mult f (field_num f (n - 1)) x)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss []
   ++ Cases_on `n`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_num_def, field_distrib_radd, field_add_assoc]);

val context = subtypeTools.add_rewrite2'' field_mult_add_neg context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_add_neg' = store_thm
  ("field_mult_add_neg'",
   ``!f :: Field. !x y :: (f.carrier). !n.
       field_add f (field_mult f (field_num f n) x)
         (field_add f (field_neg f x) y) =
       (if n = 0 then field_add f (field_neg f x) y
        else field_add f (field_mult f (field_num f (n - 1)) x) y)``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_mult_add_neg]
   ++ RW_TAC resq_ss []
   ++ RW_TAC resq_ss []);

val context = subtypeTools.add_rewrite2'' field_mult_add_neg' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_add_neg_mult = store_thm
  ("field_mult_add_neg_mult",
   ``!f :: Field. !x :: (f.carrier). !m n.
       field_add f (field_mult f (field_num f m) x)
         (field_neg f (field_mult f (field_num f n) x)) =
       (if m < n then field_neg f (field_mult f (field_num f (n - m)) x)
        else field_mult f (field_num f (m - n)) x)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss []
   << [Know `m <= n` >> DECIDE_TAC
       ++ POP_ASSUM (K ALL_TAC)
       ++ Induct_on `m`
       ++ RW_TAC alg_ss []
       ++ Cases_on `n = SUC m` >> RW_TAC alg_ss' []
       ++ Q.PAT_ASSUM `X ==> Y` MP_TAC
       ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
       ++ CONJ_TAC >> DECIDE_TAC
       ++ RW_TAC alg_ss [field_num_suc, field_distrib_radd, field_add_assoc]
       ++ Know `n - m = SUC (n - SUC m)` >> DECIDE_TAC
       ++ RW_TAC alg_ss [field_num_suc, field_distrib_radd,
                         GSYM field_add_assoc, field_neg_add],
       Know `n <= m` >> DECIDE_TAC
       ++ POP_ASSUM (K ALL_TAC)
       ++ Induct_on `m`
       ++ RW_TAC alg_ss []
       ++ Cases_on `n = SUC m` >> RW_TAC alg_ss' []
       ++ Q.PAT_ASSUM `X ==> Y` MP_TAC
       ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
       ++ CONJ_TAC >> DECIDE_TAC
       ++ RW_TAC alg_ss [field_num_suc, field_distrib_radd, field_add_assoc]
       ++ Know `SUC m - n = SUC (m - n)` >> DECIDE_TAC
       ++ RW_TAC alg_ss [field_num_suc, field_distrib_radd,
                         GSYM field_add_assoc, field_neg_add]]);

val context = subtypeTools.add_rewrite2'' field_mult_add_neg_mult context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_add_neg_mult' = store_thm
  ("field_mult_add_neg_mult'",
   ``!f :: Field. !x y :: (f.carrier). !m n.
       field_add f (field_mult f (field_num f m) x)
         (field_add f (field_neg f (field_mult f (field_num f n) x)) y) =
       (if m < n then
          field_add f (field_neg f (field_mult f (field_num f (n - m)) x)) y
        else field_add f (field_mult f (field_num f (m - n)) x) y)``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_mult_add_neg_mult]
   ++ RW_TAC resq_ss []
   ++ RW_TAC resq_ss []);

val context = subtypeTools.add_rewrite2'' field_mult_add_neg_mult' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_neg_add_neg = store_thm
  ("field_neg_add_neg",
   ``!f :: Field. !x :: (f.carrier).
       field_add f (field_neg f x) (field_neg f x) =
       field_neg f (field_mult f (field_num f 2) x)``,
   RW_TAC alg_ss [field_mult_small, field_neg_add]);

val context = subtypeTools.add_rewrite2'' field_neg_add_neg context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_neg_add_neg' = store_thm
  ("field_neg_add_neg'",
   ``!f :: Field. !x y :: (f.carrier).
       field_add f (field_neg f x) (field_add f (field_neg f x) y) =
       field_add f (field_neg f (field_mult f (field_num f 2) x)) y``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_neg_add_neg]);

val context = subtypeTools.add_rewrite2'' field_neg_add_neg' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_neg_add_neg_mult = store_thm
  ("field_neg_add_neg_mult",
   ``!f :: Field. !x :: (f.carrier). !n.
       field_add f (field_neg f x)
         (field_neg f (field_mult f (field_num f n) x)) =
       field_neg f (field_mult f (field_num f (n + 1)) x)``,
   RW_TAC alg_ss [GSYM field_single_add_mult]
   ++ RW_TAC alg_ss' []);

val context = subtypeTools.add_rewrite2'' field_neg_add_neg_mult context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_neg_add_neg_mult' = store_thm
  ("field_neg_add_neg_mult'",
   ``!f :: Field. !x y :: (f.carrier). !n.
       field_add f (field_neg f x)
         (field_add f (field_neg f (field_mult f (field_num f n) x)) y) =
       field_add f (field_neg f (field_mult f (field_num f (n + 1)) x)) y``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_neg_add_neg_mult]);

val context = subtypeTools.add_rewrite2'' field_neg_add_neg_mult' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_neg_mult_add_neg_mult = store_thm
  ("field_neg_mult_add_neg_mult",
   ``!f :: Field. !x :: (f.carrier). !m n.
       field_add f (field_neg f (field_mult f (field_num f m) x))
         (field_neg f (field_mult f (field_num f n) x)) =
       field_neg f (field_mult f (field_num f (m + n)) x)``,
   RW_TAC resq_ss []
   ++ Induct_on `m`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_num_suc, field_distrib_radd, ADD, field_neg_add]
   ++ POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
   ++ RW_TAC alg_ss [field_add_assoc]);

val context = subtypeTools.add_rewrite2'' field_neg_mult_add_neg_mult context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_neg_mult_add_neg_mult' = store_thm
  ("field_neg_mult_add_neg_mult'",
   ``!f :: Field. !x y :: (f.carrier). !m n.
       field_add f (field_neg f (field_mult f (field_num f m) x))
         (field_add f (field_neg f (field_mult f (field_num f n) x)) y) =
       field_add f (field_neg f (field_mult f (field_num f (m + n)) x)) y``,
   RW_TAC alg_ss [GSYM field_add_assoc, field_neg_mult_add_neg_mult]);

val context = subtypeTools.add_rewrite2'' field_neg_mult_add_neg_mult' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_single_mult_single = store_thm
  ("field_single_mult_single",
   ``!f :: Field. !x :: (f.carrier). field_mult f x x = field_exp f x 2``,
   RW_TAC alg_ss' [field_exp_small]);

val context = subtypeTools.add_rewrite2'' field_single_mult_single context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_single_mult_single' = store_thm
  ("field_single_mult_single'",
   ``!f :: Field. !x y :: (f.carrier).
       field_mult f x (field_mult f x y) = field_mult f (field_exp f x 2) y``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_single_mult_single]);

val context = subtypeTools.add_rewrite2'' field_single_mult_single' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_single_mult_exp = store_thm
  ("field_single_mult_exp",
   ``!f :: Field. !x :: (f.carrier). !n.
       field_mult f x (field_exp f x n) = field_exp f x (n + 1)``,
   METIS_TAC [field_exp_def, ADD1]);

val context = subtypeTools.add_rewrite2'' field_single_mult_exp context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_single_mult_exp' = store_thm
  ("field_single_mult_exp'",
   ``!f :: Field. !x y :: (f.carrier). !n.
       field_mult f x (field_mult f (field_exp f x n) y) =
       field_mult f (field_exp f x (n + 1)) y``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_single_mult_exp]);

val context = subtypeTools.add_rewrite2'' field_single_mult_exp' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_single_mult_inv_exp = store_thm
  ("field_single_mult_inv_exp",
   ``!f :: Field. !x :: field_nonzero f. !n.
       field_mult f x (field_inv f (field_exp f x n)) =
       (if n = 0 then x else field_inv f (field_exp f x (n - 1)))``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss []
   ++ Cases_on `n`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_exp_def, GSYM field_mult_assoc, field_inv_mult]);

val context = subtypeTools.add_rewrite2'' field_single_mult_inv_exp context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_single_mult_inv_exp' = store_thm
  ("field_single_mult_inv_exp'",
   ``!f :: Field. !x :: field_nonzero f. !n. !y :: (f.carrier).
       field_mult f x (field_mult f (field_inv f (field_exp f x n)) y) =
       (if n = 0 then field_mult f x y
        else field_mult f (field_inv f (field_exp f x (n - 1))) y)``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_single_mult_inv_exp]
   ++ RW_TAC resq_ss []
   ++ RW_TAC resq_ss []);

val context = subtypeTools.add_rewrite2'' field_single_mult_inv_exp' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_exp_mult_exp = store_thm
  ("field_exp_mult_exp",
   ``!f :: Field. !x :: (f.carrier). !m n.
       field_mult f (field_exp f x m) (field_exp f x n) =
       field_exp f x (m + n)``,
   RW_TAC resq_ss []
   ++ Induct_on `m`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_exp_def, ADD_CLAUSES]
   ++ POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
   ++ RW_TAC alg_ss [field_mult_assoc]);

val context = subtypeTools.add_rewrite2'' field_exp_mult_exp context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_exp_mult_exp' = store_thm
  ("field_exp_mult_exp'",
   ``!f :: Field. !x y :: (f.carrier). !m n.
       field_mult f (field_exp f x m) (field_mult f (field_exp f x n) y) =
       field_mult f (field_exp f x (m + n)) y``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_exp_mult_exp]);

val context = subtypeTools.add_rewrite2'' field_exp_mult_exp' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_exp_mult_inv = store_thm
  ("field_exp_mult_inv",
   ``!f :: Field. !x :: field_nonzero f. !n.
       field_mult f (field_exp f x n) (field_inv f x) =
       (if n = 0 then field_inv f x else field_exp f x (n - 1))``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss []
   ++ Cases_on `n`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_exp_suc, field_mult_assoc]);

val context = subtypeTools.add_rewrite2'' field_exp_mult_inv context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_exp_mult_inv' = store_thm
  ("field_exp_mult_inv'",
   ``!f :: Field. !x :: field_nonzero f. !n. !y :: (f.carrier).
       field_mult f (field_exp f x n) (field_mult f (field_inv f x) y) =
       (if n = 0 then field_mult f (field_inv f x) y
        else field_mult f (field_exp f x (n - 1)) y)``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_exp_mult_inv]
   ++ RW_TAC resq_ss []
   ++ RW_TAC resq_ss []);

val context = subtypeTools.add_rewrite2'' field_exp_mult_inv' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_exp_mult_inv_exp = store_thm
  ("field_exp_mult_inv_exp",
   ``!f :: Field. !x :: field_nonzero f. !m n.
       field_mult f (field_exp f x m) (field_inv f (field_exp f x n)) =
       (if m < n then field_inv f (field_exp f x (n - m))
        else field_exp f x (m - n))``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss []
   << [Know `m <= n` >> DECIDE_TAC
       ++ POP_ASSUM (K ALL_TAC)
       ++ Induct_on `m`
       ++ RW_TAC alg_ss []
       ++ Cases_on `n = SUC m` >> RW_TAC alg_ss []
       ++ Q.PAT_ASSUM `X ==> Y` MP_TAC
       ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
       ++ CONJ_TAC >> DECIDE_TAC
       ++ RW_TAC alg_ss [field_exp_def, field_mult_assoc]
       ++ Know `n - m = SUC (n - SUC m)` >> DECIDE_TAC
       ++ RW_TAC alg_ss [field_exp_def, GSYM field_mult_assoc, field_inv_mult],
       Know `n <= m` >> DECIDE_TAC
       ++ POP_ASSUM (K ALL_TAC)
       ++ Induct_on `m`
       ++ RW_TAC alg_ss []
       ++ Cases_on `n = SUC m` >> RW_TAC alg_ss []
       ++ Q.PAT_ASSUM `X ==> Y` MP_TAC
       ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
       ++ CONJ_TAC >> DECIDE_TAC
       ++ RW_TAC alg_ss [field_exp_def, field_mult_assoc]
       ++ Know `SUC m - n = SUC (m - n)` >> DECIDE_TAC
       ++ RW_TAC alg_ss [field_exp_def, GSYM field_mult_assoc]]);

val context = subtypeTools.add_rewrite2'' field_exp_mult_inv_exp context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_exp_mult_inv_exp' = store_thm
  ("field_exp_mult_inv_exp'",
   ``!f :: Field. !x :: field_nonzero f. !m n. !y :: (f.carrier).
       field_mult f (field_exp f x m)
         (field_mult f (field_inv f (field_exp f x n)) y) =
       (if m < n then field_mult f (field_inv f (field_exp f x (n - m))) y
        else field_mult f (field_exp f x (m - n)) y)``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_exp_mult_inv_exp]
   ++ RW_TAC resq_ss []
   ++ RW_TAC resq_ss []);

val context = subtypeTools.add_rewrite2'' field_exp_mult_inv_exp' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_inv_mult_inv = store_thm
  ("field_inv_mult_inv",
   ``!f :: Field. !x :: field_nonzero f.
       field_mult f (field_inv f x) (field_inv f x) =
       field_inv f (field_exp f x 2)``,
   RW_TAC alg_ss [field_exp_small, field_inv_mult]);

val context = subtypeTools.add_rewrite2'' field_inv_mult_inv context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_inv_mult_inv' = store_thm
  ("field_inv_mult_inv'",
   ``!f :: Field. !x :: field_nonzero f. !y :: (f.carrier).
       field_mult f (field_inv f x) (field_mult f (field_inv f x) y) =
       field_mult f (field_inv f (field_exp f x 2)) y``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_inv_mult_inv]);

val context = subtypeTools.add_rewrite2'' field_inv_mult_inv' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_inv_mult_inv_exp = store_thm
  ("field_inv_mult_inv_exp",
   ``!f :: Field. !x :: field_nonzero f. !n.
       field_mult f (field_inv f x) (field_inv f (field_exp f x n)) =
       field_inv f (field_exp f x (n + 1))``,
   RW_TAC alg_ss [GSYM field_single_mult_exp]
   ++ RW_TAC alg_ss' []);

val context = subtypeTools.add_rewrite2'' field_inv_mult_inv_exp context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_inv_mult_inv_exp' = store_thm
  ("field_inv_mult_inv_exp'",
   ``!f :: Field. !x :: field_nonzero f. !n. !y :: (f.carrier).
       field_mult f (field_inv f x)
         (field_mult f (field_inv f (field_exp f x n)) y) =
       field_mult f (field_inv f (field_exp f x (n + 1))) y``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_inv_mult_inv_exp]);

val context = subtypeTools.add_rewrite2'' field_inv_mult_inv_exp' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_inv_exp_mult_inv_exp = store_thm
  ("field_inv_exp_mult_inv_exp",
   ``!f :: Field. !x :: field_nonzero f. !m n.
       field_mult f (field_inv f (field_exp f x m))
         (field_inv f (field_exp f x n)) =
       field_inv f (field_exp f x (m + n))``,
   RW_TAC resq_ss []
   ++ Induct_on `m`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_exp_def, ADD_CLAUSES, field_inv_mult]
   ++ POP_ASSUM (fn th => REWRITE_TAC [GSYM th])
   ++ RW_TAC alg_ss [field_mult_assoc]);

val context = subtypeTools.add_rewrite2'' field_inv_exp_mult_inv_exp context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_inv_exp_mult_inv_exp' = store_thm
  ("field_inv_exp_mult_inv_exp'",
   ``!f :: Field. !x :: field_nonzero f. !m n. !y :: (f.carrier).
       field_mult f (field_inv f (field_exp f x m))
         (field_mult f (field_inv f (field_exp f x n)) y) =
       field_mult f (field_inv f (field_exp f x (m + n))) y``,
   RW_TAC alg_ss [GSYM field_mult_assoc, field_inv_exp_mult_inv_exp]);

val context = subtypeTools.add_rewrite2'' field_inv_exp_mult_inv_exp' context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_one_exp = store_thm
  ("field_one_exp",
   ``!f :: Field. !n. field_exp f (field_one f) n = field_one f``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [field_exp_def, field_mult_rone, field_one_carrier]);

val context = subtypeTools.add_rewrite2 field_one_exp context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_zero_exp = store_thm
  ("field_zero_exp",
   ``!f :: Field. !n.
       field_exp f (field_zero f) n =
       (if n = 0 then field_one f else field_zero f)``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss
        [field_exp_def, field_mult_rone, field_one_carrier]
   ++ RW_TAC alg_ss []);

val context = subtypeTools.add_rewrite2 field_zero_exp context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_exp_eq_zero = store_thm
  ("field_exp_eq_zero",
   ``!f :: Field. !x :: (f.carrier). !n.
       (field_exp f x n = field_zero f) = ~(n = 0) /\ (x = field_zero f)``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss
        [field_exp_def, field_one_zero, field_entire, field_exp_carrier]
   ++ METIS_TAC []);

val context = subtypeTools.add_rewrite2 field_exp_eq_zero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_exp_neg = store_thm
  ("field_exp_neg",
   ``!f :: Field. !x :: (f.carrier). !n.
       field_exp f (field_neg f x) n =
       if EVEN n then field_exp f x n else field_neg f (field_exp f x n)``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC alg_ss [EVEN, field_exp_def]);

val context = subtypeTools.add_rewrite2'' field_exp_neg context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_exp_exp = store_thm
  ("field_exp_exp",
   ``!f :: Field. !x :: (f.carrier). !m n.
       field_exp f (field_exp f x m) n = field_exp f x (m * n)``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   >> RW_TAC alg_ss [field_exp_def]
   ++ RW_TAC alg_ss [field_exp_def, ONCE_REWRITE_RULE [MULT_COMM] MULT]
   ++ ONCE_REWRITE_TAC [ADD_COMM]
   ++ RW_TAC alg_ss [GSYM field_exp_mult_exp]);

val context = subtypeTools.add_rewrite2'' field_exp_exp context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_sub_eq_zero = store_thm
  ("field_sub_eq_zero",
   ``!f :: Field. !x y :: (f.carrier).
       (field_sub f x y = field_zero f) = (x = y)``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss' []
   ++ RW_TAC alg_ss [GSYM field_neg_eq]);

local
  val field_sub_eq_zero_conv =
      let
        val th = CONV_RULE RES_FORALL_CONV (GSYM field_sub_eq_zero)
      in
        fn f => cond_rewr_conv (ISPEC f th)
      end;

  fun left_conv solver tm =
      let
        val (x,y) = dest_eq tm
        val _ = not (is_field_zero y) orelse
                raise ERR "field_sub_eq_zero_conv (left)" "looping"
        val (f,_,_) = dest_field_add x
      in
        field_sub_eq_zero_conv f solver
      end tm;

  fun right_conv solver tm =
      let
        val (_,y) = dest_eq tm
        val (f,_,_) = dest_field_add y
(***
        val _ = print "right_conv\n";
***)
      in
        field_sub_eq_zero_conv f solver
      end tm;
in
  val field_sub_eq_zero_l_conv =
      {name = "field_sub_eq_zero_conv (left)",
       key = ``field_add (f : 'a field) x y = z``,
       conv = left_conv}
  and field_sub_eq_zero_r_conv =
      {name = "field_sub_eq_zero_conv (right)",
       key = ``x = field_add (f : 'a field) y z``,
       conv = right_conv};
end;

val context = subtypeTools.add_conversion2'' field_sub_eq_zero_r_conv context;
val context = subtypeTools.add_conversion2'' field_sub_eq_zero_l_conv context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_sub_eq_zero_imp = store_thm
  ("field_sub_eq_zero_imp",
   ``!f :: Field. !x y :: (f.carrier).
       (field_sub f x y = field_zero f) ==> (x = y)``,
   RW_TAC std_ss [field_sub_eq_zero]);

val field_inv_inv = store_thm
  ("field_inv_inv",
   ``!f :: Field. !x :: field_nonzero f. field_inv f (field_inv f x) = x``,
   RW_TAC resq_ss
     [field_inv_def, Field_def, GSPECIFICATION, AbelianGroup_def,
      field_nonzero_def]
   ++ METIS_TAC [group_inv_inv]);

val context = subtypeTools.add_rewrite2 field_inv_inv context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_sub_carrier = store_thm
  ("field_sub_carrier",
   ``!f :: Field. !x y :: (f.carrier). field_sub f x y IN f.carrier``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss' []);

val context = subtypeTools.add_reduction2 field_sub_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_neg_nonzero = store_thm
  ("field_neg_nonzero",
   ``!f :: Field. !x :: field_nonzero f. field_neg f x IN field_nonzero f``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss [GSYM field_nonzero_eq]
   ++ POP_ASSUM MP_TAC
   ++ RW_TAC alg_ss [field_nonzero_def, GSPECIFICATION, IN_DIFF, IN_SING]
   ++ STRIP_TAC
   ++ Q.PAT_ASSUM `~(X = Y)` MP_TAC
   ++ RW_TAC alg_ss []
   ++ match_tac field_add_lcancel_imp
   ++ Q.EXISTS_TAC `f`
   ++ Q.EXISTS_TAC `field_neg f x`
   ++ RW_TAC std_ss [field_lneg]
   ++ RW_TAC alg_ss []);

val context = subtypeTools.add_reduction2 field_neg_nonzero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_inv_neg = store_thm
  ("field_inv_neg",
   ``!f :: Field. !x :: field_nonzero f.
       field_inv f (field_neg f x) = field_neg f (field_inv f x)``,
   RW_TAC resq_ss []
   ++ match_tac field_mult_lcancel_imp
   ++ Q.EXISTS_TAC `f`
   ++ Q.EXISTS_TAC `field_neg f x`
   ++ SIMP_TAC bool_ss [CONJ_ASSOC]
   ++ CONJ_TAC >> RW_TAC alg_ss []
   ++ Know
      `field_mult f (field_neg f x) (field_inv f (field_neg f x)) = field_one f`
   >> (match_tac field_rinv ++ RW_TAC alg_ss [])
   ++ RW_TAC std_ss []
   ++ RW_TAC alg_ss' []);
  
val context = subtypeTools.add_rewrite2'' field_inv_neg context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_exp_mult = store_thm
  ("field_exp_mult",
   ``!f :: Field. !x y :: (f.carrier). !n.
       field_exp f (field_mult f x y) n =
       field_mult f (field_exp f x n) (field_exp f y n)``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC alg_ss [field_exp_def]
   ++ RW_TAC alg_ss [field_mult_assoc]
   ++ AP_TERM_TAC
   ++ RW_TAC alg_ss [GSYM field_mult_assoc]
   ++ AP_THM_TAC
   ++ AP_TERM_TAC
   ++ match_tac field_mult_comm
   ++ RW_TAC alg_ss []);

val context = subtypeTools.add_rewrite2'' field_exp_mult context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_exp_inv = store_thm
  ("field_exp_inv",
   ``!f :: Field. !x :: field_nonzero f. !n.
       field_exp f (field_inv f x) n = field_inv f (field_exp f x n)``,
   RW_TAC resq_ss []
   ++ Induct_on `n`
   ++ RW_TAC alg_ss []
   ++ RW_TAC alg_ss [field_exp_def]
   ++ RW_TAC alg_ss' []);

val context = subtypeTools.add_rewrite2'' field_exp_inv context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_add_ac_conv =
    {name = "field_add_ac_conv",
     key = ``field_add f x y``,
     conv =
       subtypeTools.binop_ac_conv
         {term_compare = field_compare,
          dest_binop = dest_field_add,
          dest_inv = dest_field_neg,
          dest_exp = dest_field_num_mult,
          assoc_th = field_add_assoc,
          comm_th = field_add_comm,
          comm_th' = field_add_comm',
          id_ths =
            [field_add_lzero,
             field_add_lzero',
             field_add_rzero,
             field_add_rzero'],             
          simplify_ths =
            [GSYM field_num_one,
             field_neg_zero,
             field_neg_neg,
             field_neg_add,
             field_mult_lzero,
             field_mult_lzero',
             field_mult_rzero,
             field_mult_rzero',
             field_mult_lone,
             field_mult_lone',
             field_mult_rone,
             field_mult_rone'],
          combine_ths =
            [field_single_add_single,
             field_single_add_mult,
             field_rneg,
             field_single_add_neg_mult,
             field_mult_add_mult,
             field_mult_add_neg,
             field_mult_add_neg_mult,
             field_neg_add_neg,
             field_neg_add_neg_mult,
             field_neg_mult_add_neg_mult],
          combine_ths' =
            [field_single_add_single',
             field_single_add_mult',
             field_rneg',
             field_single_add_neg_mult',
             field_mult_add_mult',
             field_mult_add_neg',
             field_mult_add_neg_mult',
             field_neg_add_neg',
             field_neg_add_neg_mult',
             field_neg_mult_add_neg_mult']}};
    
val context = subtypeTools.add_conversion2'' field_add_ac_conv context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_mult_ac_conv =
    {name = "field_mult_ac_conv",
     key = ``field_mult f x y``,
     conv =
       subtypeTools.binop_ac_conv
         {term_compare = field_compare,
          dest_binop = dest_field_mult,
          dest_inv = dest_field_inv,
          dest_exp = dest_field_exp,
          assoc_th = field_mult_assoc,
          comm_th = field_mult_comm,
          comm_th' = field_mult_comm',
          id_ths =
            [field_mult_lone,
             field_mult_lone',
             field_mult_rone,
             field_mult_rone'],
          simplify_ths =
            [field_inv_one,
             field_inv_inv,
             field_inv_mult,
             field_exp_zero,
             field_exp_one,
             field_exp_exp,
             field_exp_mult,
             field_exp_inv],
          combine_ths =
            [field_single_mult_single,
             field_single_mult_exp,
             field_rinv,
             field_single_mult_inv_exp,
             field_exp_mult_exp,
             field_exp_mult_inv,
             field_exp_mult_inv_exp,
             field_inv_mult_inv,
             field_inv_mult_inv_exp,
             field_inv_exp_mult_inv_exp],
          combine_ths' =
            [field_single_mult_single',
             field_single_mult_exp',
             field_rinv',
             field_single_mult_inv_exp',
             field_exp_mult_exp',
             field_exp_mult_inv',
             field_exp_mult_inv_exp',
             field_inv_mult_inv',
             field_inv_mult_inv_exp',
             field_inv_exp_mult_inv_exp']}};
    
val context = subtypeTools.add_conversion2'' field_mult_ac_conv context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_binomial_2 = store_thm
  ("field_binomial_2",
   ``!f :: Field. !x y :: (f.carrier).
       field_exp f (field_add f x y) 2 =
       field_add f (field_exp f x 2)
         (field_add f (field_mult f (field_num f 2) (field_mult f x y))
            (field_exp f y 2))``,
   RW_TAC alg_ss [field_exp_small]
   ++ RW_TAC alg_ss' [field_distrib]);

val field_binomial_3 = store_thm
  ("field_binomial_3",
   ``!f :: Field. !x y :: (f.carrier).
       field_exp f (field_add f x y) 3 =
       field_add f
         (field_exp f x 3)
         (field_add f
           (field_mult f (field_num f 3) (field_mult f (field_exp f x 2) y))
           (field_add f
             (field_mult f (field_num f 3) (field_mult f x (field_exp f y 2)))
             (field_exp f y 3)))``,
   RW_TAC alg_ss [field_exp_small]
   ++ RW_TAC alg_ss' [field_distrib, field_binomial_2]);

val field_binomial_4 = store_thm
  ("field_binomial_4",
   ``!f :: Field. !x y :: (f.carrier).
       field_exp f (field_add f x y) 4 =
       field_add f
         (field_exp f x 4)
         (field_add f
           (field_mult f (field_num f 4) (field_mult f (field_exp f x 3) y))
           (field_add f
             (field_mult f
               (field_num f 6)
               (field_mult f (field_exp f x 2) (field_exp f y 2)))
             (field_add f
               (field_mult f (field_num f 4) (field_mult f x (field_exp f y 3)))
               (field_exp f y 4))))``,
   RW_TAC alg_ss [field_exp_small]
   ++ RW_TAC alg_ss' [field_distrib, field_binomial_2, field_binomial_3]);

val field_div_carrier = store_thm
  ("field_div_carrier",
   ``!f :: Field. !x :: (f.carrier). !y :: field_nonzero f.
       field_div f x y IN f.carrier``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss' [field_div_def]);

val context = subtypeTools.add_reduction2 field_div_carrier context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_div_nonzero = store_thm
  ("field_div_nonzero",
   ``!f :: Field. !x y :: field_nonzero f. field_div f x y IN field_nonzero f``,
   RW_TAC resq_ss []
   ++ RW_TAC alg_ss' [field_div_def]);

val context = subtypeTools.add_reduction2 field_div_nonzero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_div_lneg = store_thm
  ("field_div_lneg",
   ``!f :: Field. !x :: (f.carrier). !y :: field_nonzero f.
       field_div f (field_neg f x) y = field_neg f (field_div f x y)``,
   RW_TAC alg_ss' [field_div_def]);

val field_div_rneg = store_thm
  ("field_div_rneg",
   ``!f :: Field. !x :: (f.carrier). !y :: field_nonzero f.
       field_div f x (field_neg f y) = field_neg f (field_div f x y)``,
   RW_TAC alg_ss' [field_inv_neg, field_div_def]);

val field_div_addl = store_thm
  ("field_div_addl",
   ``!f :: Field. !x y :: (f.carrier). !z :: field_nonzero f.
       field_add f x (field_div f y z) =
       field_div f (field_add f (field_mult f x z) y) z``,
   RW_TAC alg_ss' [field_div_def, field_distrib]);

val field_div_addr = store_thm
  ("field_div_addr",
   ``!f :: Field. !x y :: (f.carrier). !z :: field_nonzero f.
       field_add f (field_div f y z) x =
       field_div f (field_add f y (field_mult f x z)) z``,
   RW_TAC alg_ss' [field_div_def, field_distrib]);

val field_div_subl = store_thm
  ("field_div_subl",
   ``!f :: Field. !x y :: (f.carrier). !z :: field_nonzero f.
       field_sub f x (field_div f y z) =
       field_div f (field_sub f (field_mult f x z) y) z``,
   RW_TAC alg_ss' [field_div_def, field_distrib]);

val field_div_subr = store_thm
  ("field_div_subr",
   ``!f :: Field. !x y :: (f.carrier). !z :: field_nonzero f.
       field_sub f (field_div f y z) x =
       field_div f (field_sub f y (field_mult f x z)) z``,
   RW_TAC alg_ss' [field_div_def, field_distrib]);

val field_div_multl = store_thm
  ("field_div_multl",
   ``!f :: Field. !x y :: (f.carrier). !z :: field_nonzero f.
       field_mult f x (field_div f y z) =
       field_div f (field_mult f x y) z``,
   RW_TAC alg_ss' [field_div_def]);

val field_div_multr = store_thm
  ("field_div_multr",
   ``!f :: Field. !x y :: (f.carrier). !z :: field_nonzero f.
       field_mult f (field_div f y z) x =
       field_div f (field_mult f y x) z``,
   RW_TAC alg_ss' [field_div_def]);

val field_div_exp = store_thm
  ("field_div_exp",
   ``!f :: Field. !x :: (f.carrier). !y :: field_nonzero f. !n.
       field_exp f (field_div f x y) n =
       field_div f (field_exp f x n) (field_exp f y n)``,
   RW_TAC alg_ss' [field_div_def, field_exp_mult, field_exp_inv]);

val field_div_divl = store_thm
  ("field_div_divl",
   ``!f :: Field. !x :: (f.carrier). !y z :: field_nonzero f.
       field_div f (field_div f x y) z =
       field_div f x (field_mult f y z)``,
   RW_TAC alg_ss' [field_div_def]);

val field_div_divr = store_thm
  ("field_div_divr",
   ``!f :: Field. !x :: (f.carrier). !y z :: field_nonzero f.
       field_div f x (field_div f y z) =
       field_div f (field_mult f x z) y``,
   RW_TAC alg_ss' [field_div_def]);

val field_add_divl = store_thm
  ("field_add_divl",
   ``!f :: Field. !x y :: (f.carrier). !z :: field_nonzero f.
       field_add f (field_div f y z) x =
       field_div f (field_add f y (field_mult f z x)) z``,
   RW_TAC alg_ss [field_div_def]
   ++ RW_TAC alg_ss' [field_distrib]);

val field_add_divl' = store_thm
  ("field_add_divl'",
   ``!f :: Field. !x y t :: (f.carrier). !z :: field_nonzero f.
       field_add f (field_div f y z) (field_add f x t) =
       field_add f (field_div f (field_add f y (field_mult f z x)) z) t``,
   RW_TAC alg_ss [GSYM field_add_assoc]
   ++ RW_TAC resq_ss []
   ++ match_tac field_add_divl
   ++ RW_TAC alg_ss []);

val field_add_divr = store_thm
  ("field_add_divr",
   ``!f :: Field. !x y :: (f.carrier). !z :: field_nonzero f.
       field_add f x (field_div f y z) =
       field_div f (field_add f (field_mult f z x) y) z``,
   RW_TAC alg_ss [field_div_def]
   ++ RW_TAC alg_ss' [field_distrib]);

val field_add_divr' = store_thm
  ("field_add_divr'",
   ``!f :: Field. !x y t :: (f.carrier). !z :: field_nonzero f.
       field_add f x (field_add f (field_div f y z) t) =
       field_add f (field_div f (field_add f (field_mult f z x) y) z) t``,
   RW_TAC alg_ss [GSYM field_add_assoc]
   ++ RW_TAC resq_ss []
   ++ match_tac field_add_divr
   ++ RW_TAC alg_ss []);

val field_add_div = store_thm
  ("field_add_div",
   ``!f :: Field. !v w :: (f.carrier). !x y z :: field_nonzero f.
       field_add f
         (field_div f v (field_mult f x y))
         (field_div f w (field_mult f x z)) =
       field_div f
         (field_add f (field_mult f z v) (field_mult f y w))
         (field_mult f x (field_mult f y z))``,
   RW_TAC alg_ss [field_div_def]
   ++ RW_TAC alg_ss' [field_distrib]);

val field_add_div' = store_thm
  ("field_add_div'",
   ``!f :: Field. !v w t :: (f.carrier). !x y z :: field_nonzero f.
       field_add f
         (field_div f v (field_mult f x y))
         (field_add f (field_div f w (field_mult f x z)) t) =
       field_add f
         (field_div f
           (field_add f (field_mult f z v) (field_mult f y w))
           (field_mult f x (field_mult f y z))) t``,
   RW_TAC alg_ss [GSYM field_add_assoc]
   ++ RW_TAC resq_ss []
   ++ match_tac field_add_div
   ++ RW_TAC alg_ss []);

val field_div_cancel = store_thm
  ("field_div_cancel",
   ``!f :: Field. !x z :: field_nonzero f. !y :: (f.carrier).
       (field_div f (field_mult f x y) (field_mult f x z) = field_div f y z)``,
   RW_TAC resq_ss [field_div_def]
   ++ RW_TAC alg_ss' []);

val field_inv_eq_zero = store_thm
  ("field_inv_eq_zero",
   ``!f :: Field. !x :: field_nonzero f. ~(field_inv f x = field_zero f)``,
   RW_TAC resq_ss []
   ++ STRIP_TAC
   ++ Know `field_inv f x IN field_nonzero f` >> METIS_TAC [field_inv_nonzero]
   ++ RW_TAC alg_ss [field_nonzero_def, IN_DIFF, IN_SING]);

val context = subtypeTools.add_rewrite2 field_inv_eq_zero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val field_div_eq_zero = store_thm
  ("field_div_eq_zero",
   ``!f :: Field. !x :: (f.carrier). !y :: field_nonzero f.
       (field_div f x y = field_zero f) = (x = field_zero f)``,
   RW_TAC resq_ss [field_div_def]
   ++ RW_TAC alg_ss [field_entire]);

val context = subtypeTools.add_rewrite2 field_div_eq_zero context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

(* ------------------------------------------------------------------------- *)
(* Homomorphisms, isomorphisms, endomorphisms, automorphisms and subfields.  *)
(* ------------------------------------------------------------------------- *)

val FieldHom_def = Define
  `FieldHom g h =
   { f |
     (!x :: (g.carrier). f x IN h.carrier) /\
     f IN GroupHom (g.sum) (h.sum) /\
     f IN GroupHom (g.prod) (h.prod) }`;

val FieldIso_def = Define
  `FieldIso g h =
   { f |
     f IN FieldHom g h /\
     (!y :: (h.carrier). ?!x :: (g.carrier). f x = y) }`;

val FieldEndo_def = Define `FieldEndo g = FieldHom g g`;

val FieldAuto_def = Define `FieldAuto g = FieldIso g g`;

val subfield_def = Define `subfield g h = I IN FieldHom g h`;

(* ------------------------------------------------------------------------- *)
(* Polynomials over fields.                                                  *)
(* ------------------------------------------------------------------------- *)

val () = type_abbrev ("poly", Type `:'a list`);

val poly_zero_def = Define `poly_zero = ([] : 'a poly)`;

val Poly_def = Define
  `Poly (f : 'a field) =
   { (p : 'a poly) |
     (p = poly_zero) \/
     (EVERY (\c. c IN f.carrier) p /\ ~(LAST p = field_zero f)) }`;

val poly_degree_def = Define
  `poly_degree (p : 'a poly) = if (p = poly_zero) then 0 else LENGTH p - 1`;

val poly_eval_def = Define
  `(poly_eval (f : 'a field) [] x = field_zero f) /\
   (poly_eval (f : 'a field) (c :: cs) x =
    field_add f c (field_mult f x (poly_eval f cs x)))`;

val AlgebraicallyClosedField_def = Define
  `AlgebraicallyClosedField =
   { (f : 'a field) |
     f IN Field /\ 
     !p :: Poly f.
       (poly_degree p = 0) \/
       ?z :: (f.carrier). poly_eval f p z = field_zero f }`;

(* ------------------------------------------------------------------------- *)
(* The trivial field.                                                        *)
(* ------------------------------------------------------------------------- *)

val trivial_field_def = Define
  `(trivial_field zero_elt one_elt) : 'a field =
   <| carrier := {zero_elt; one_elt};
      sum := <| carrier := {zero_elt; one_elt};
                id := zero_elt;
                inv := (\x. x);
                mult := (\x y. if x = zero_elt then y
                               else if y = zero_elt then x
                               else zero_elt) |>;
      prod := <| carrier := {one_elt};
                 id := one_elt;
                 inv := (\x. x);
                 mult := (\x y. if x = zero_elt then zero_elt
                                else if y = zero_elt then zero_elt
                                else one_elt) |> |>`;

val trivial_field = store_thm
  ("trivial_field",
   ``!zero_elt one_elt.
       ~(zero_elt = one_elt) ==>
       trivial_field zero_elt one_elt IN FiniteField``,
   RW_TAC resq_ss
     [trivial_field_def, FiniteField_def, Field_def, GSPECIFICATION,
      combinTheory.K_THM, field_add_def, field_mult_def, field_zero_def,
      AbelianGroup_def, Group_def, IN_INSERT, NOT_IN_EMPTY, EXTENSION,
      FINITE_INSERT, FINITE_EMPTY, IN_DIFF, field_nonzero_def]
   ++ RW_TAC std_ss []
   ++ METIS_TAC []);  

(* ------------------------------------------------------------------------- *)
(* GF(p).                                                                    *)
(* ------------------------------------------------------------------------- *)

val (modexp_def, modexp_ind) = Defn.tstore_defn
  (Hol_defn "modexp"
   `modexp a n m =
    if n = 0 then 1
    else if n MOD 2 = 0 then modexp ((a * a) MOD m) (n DIV 2) m
    else (a * modexp ((a * a) MOD m) (n DIV 2) m) MOD m`,
   WF_REL_TAC `measure (\(x,y,z). y)`
   ++ RW_TAC arith_ss []
   ++ Know `2 * (n DIV 2) <= n`
   >> PROVE_TAC [TWO, DIV_THEN_MULT]
   ++ DECIDE_TAC)

val GF_def = Define
  `GF p = 
   <| carrier := { n | n < p };
      sum := add_mod p;
      prod := mult_mod p |>`;

val modexp = store_thm
  ("modexp",
   ``!a n m. 1 < m ==> (modexp a n m = (a ** n) MOD m)``,
   recInduct modexp_ind
   ++ RW_TAC std_ss []
   ++ ONCE_REWRITE_TAC [modexp_def]
   ++ Cases_on `n = 0` >> RW_TAC arith_ss [EXP]
   ++ ASM_SIMP_TAC bool_ss []
   ++ REPEAT (Q.PAT_ASSUM `X ==> Y` (K ALL_TAC))
   ++ Know `0 < m` >> DECIDE_TAC
   ++ STRIP_TAC
   ++ MP_TAC (Q.SPEC `m` MOD_TIMES2)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (MP_TAC o Q.SPECL [`a`,`a`])
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ ASM_SIMP_TAC bool_ss [MOD_MOD, MOD_EXP]
   ++ Know `a MOD m * a MOD m = (a MOD m) ** 2`
   >> RW_TAC bool_ss [TWO, ONE, EXP, REWRITE_RULE [ONE] MULT_CLAUSES]
   ++ DISCH_THEN (fn th => ASM_SIMP_TAC bool_ss [th])
   ++ ASM_SIMP_TAC bool_ss [EXP_EXP]
   ++ MP_TAC (Q.SPEC `m` MOD_TIMES2)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ MP_TAC (Q.SPECL [`a`,`n`,`m`] MOD_EXP)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ Q.SPEC_TAC (`a MOD m`,`a`)
   ++ MP_TAC (Q.SPEC `m` MOD_TIMES2)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ ASM_SIMP_TAC bool_ss [MOD_MOD]
   ++ ASM_SIMP_TAC bool_ss [MOD_TIMES2, GSYM EXP]
   ++ Know `(n MOD 2 = 0) \/ (n MOD 2 = 1)`
   >> (Suff `n MOD 2 < 2` >> DECIDE_TAC
       ++ RW_TAC std_ss [DIVISION])
   ++ ASM_SIMP_TAC bool_ss [ADD1]
   ++ Suff `n = 2 * (n DIV 2) + n MOD 2`
   >> METIS_TAC [ADD_CLAUSES]
   ++ METIS_TAC [DIVISION, DECIDE ``0 < 2``, MULT_COMM]);

val GF_carrier = store_thm
  ("GF_carrier",
   ``!p. (GF p).carrier = { n | n < p}``,
   RW_TAC std_ss [GF_def, field_accessors]);

val GF_in_carrier = store_thm
  ("GF_in_carrier",
   ``!p x. x IN (GF p).carrier = x < p``,
   RW_TAC std_ss [GF_carrier, GSPECIFICATION]);

val GF_in_carrier_imp = store_thm
  ("GF_in_carrier_imp",
   ``!p x. x < p ==> x IN (GF p).carrier``,
   METIS_TAC [GF_in_carrier]);

val context = subtypeTools.add_judgement2 GF_in_carrier_imp context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val GF_zero = store_thm
  ("GF_zero",
   ``!p. field_zero (GF p) = 0``,
   RW_TAC std_ss [GF_def, field_accessors, field_zero_def, add_mod_def]);

val GF_one = store_thm
  ("GF_one",
   ``!p. field_one (GF p) = 1``,
   RW_TAC std_ss [GF_def, field_accessors, field_one_def, mult_mod_def]);

val GF_neg = store_thm
  ("GF_neg",
   ``!p x. field_neg (GF p) x = (p - x) MOD p``,
   RW_TAC std_ss [GF_def, field_accessors, field_neg_def, add_mod_def]);

val GF_add = store_thm
  ("GF_add",
   ``!p x y. field_add (GF p) x y = (x + y) MOD p``,
   RW_TAC std_ss [GF_def, field_accessors, field_add_def, add_mod_def]);

val GF_sub = store_thm
  ("GF_sub",
   ``!p :: Prime. !x y. field_sub (GF p) x y = (x + (p - y)) MOD p``,
   RW_TAC resq_ss [GF_add, GF_neg, field_sub_def, Prime_def, GSPECIFICATION]
   ++ Know `~(p = 0)` >> METIS_TAC [NOT_PRIME_0]
   ++ STRIP_TAC
   ++ MP_TAC (Q.SPEC `p` MOD_PLUS)
   ++ MATCH_MP_TAC (PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``)
   ++ CONJ_TAC >> DECIDE_TAC
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ RW_TAC arith_ss [MOD_MOD]);

val GF_inv = store_thm
  ("GF_inv",
   ``!p :: Prime. !x y. field_inv (GF p) x = modexp x (p - 2) p``,
  RW_TAC resq_ss
    [GF_def, field_accessors, field_inv_def, mult_mod_def,
     combinTheory.K_THM, Prime_def, GSPECIFICATION]
  ++ match_tac (GSYM modexp)
  ++ Suff `~(p = 0) /\ ~(p = 1)` >> DECIDE_TAC
  ++ METIS_TAC [NOT_PRIME_0, NOT_PRIME_1]);

val GF_mult = store_thm
  ("GF_mult",
   ``!p x y. field_mult (GF p) x y = (x * y) MOD p``,
  RW_TAC std_ss [GF_def, field_accessors, field_mult_def, mult_mod_def]);

val GF_div = store_thm
  ("GF_div",
   ``!p x y. field_div (GF p) x y = field_mult (GF p) x (field_inv (GF p) y)``,
  RW_TAC std_ss [field_div_def]);

val GF_exp = store_thm
  ("GF_exp",
   ``!p :: Prime. !x n. field_exp (GF p) x n = modexp x n p``,
   RW_TAC resq_ss [Prime_def, GSPECIFICATION]
   ++ Know `1 < p`
   >> (Suff `~(p = 0) /\ ~(p = 1)` >> DECIDE_TAC
       ++ METIS_TAC [NOT_PRIME_0, NOT_PRIME_1])
   ++ STRIP_TAC
   ++ Know `0 < p` >> DECIDE_TAC
   ++ STRIP_TAC
   ++ RW_TAC bool_ss [modexp]
   ++ (Induct_on `n`
       ++ RW_TAC bool_ss [field_exp_def, GF_one, GF_mult, EXP])
   >> METIS_TAC [LESS_MOD]
   ++ METIS_TAC [MOD_MOD, MOD_TIMES2]);

val GF_num = store_thm
  ("GF_num",
   ``!p :: Prime. !n. field_num (GF p) n = n MOD p``,
   RW_TAC resq_ss []
   ++ Know `p IN Nonzero` >> RW_TAC alg_ss []
   ++ RW_TAC std_ss [Nonzero_def, GSPECIFICATION]
   ++ Know `0 < p` >> DECIDE_TAC
   ++ POP_ASSUM_LIST (K ALL_TAC)
   ++ RW_TAC std_ss []
   ++ Induct_on `n`
   ++ RW_TAC std_ss [field_num_def, GF_zero, ZERO_MOD, GF_add, GF_one]
   ++ REWRITE_TAC [ADD1]
   ++ MP_TAC (Q.SPEC `p` MOD_PLUS)
   ++ ASM_REWRITE_TAC []
   ++ DISCH_THEN (fn th => ONCE_REWRITE_TAC [GSYM th])
   ++ RW_TAC arith_ss [MOD_MOD]);

val GF_alt = store_thm
  ("GF_alt",
   ``!p :: Prime. !x y n.
       (field_zero (GF p) = 0) /\
       (field_one (GF p) = 1) /\
       (field_neg (GF p) x = (p - x) MOD p) /\
       (field_add (GF p) x y = (x + y) MOD p) /\
       (field_sub (GF p) x y = (x + (p - y)) MOD p) /\
       (field_inv (GF p) x = modexp x (p - 2) p) /\
       (field_mult (GF p) x y = (x * y) MOD p) /\
       (field_div (GF p) x y = field_mult (GF p) x (field_inv (GF p) y)) /\
       (field_exp (GF p) x n = modexp x n p) /\
       (field_num (GF p) x = x MOD p)``,
   RW_TAC std_ss
     [GF_zero, GF_one, GF_neg, GF_add, GF_sub, GF_inv, GF_mult, GF_div,
      GF_exp, GF_num]);

val GF = store_thm
  ("GF",
   ``!p :: Prime. GF p IN FiniteField``,
   RW_TAC resq_ss [FiniteField_def, GSPECIFICATION, Field_def]
   << [RW_TAC alg_ss [GF_def, combinTheory.K_THM],
       RW_TAC alg_ss [GF_def, combinTheory.K_THM],
       RW_TAC alg_ss [GF_def, combinTheory.K_THM, add_mod_def],
       RW_TAC alg_ss [GF_alt]
       ++ RW_TAC alg_ss
            [GF_def, combinTheory.K_THM, mult_mod_def,
             EXTENSION, IN_DIFF, GSPECIFICATION, IN_SING, field_nonzero_def,
             field_zero_def, add_mod_def]
       ++ METIS_TAC [],
       RW_TAC std_ss [GF_alt, MULT]
       ++ MATCH_MP_TAC ZERO_MOD
       ++ Suff `p IN Nonzero` >> RW_TAC arith_ss [Nonzero_def, GSPECIFICATION]
       ++ RW_TAC alg_ss [],
       RW_TAC std_ss [GF_alt]
       ++ Know `0 < p`
       >> (Suff `p IN Nonzero` >> RW_TAC arith_ss [Nonzero_def, GSPECIFICATION]
           ++ RW_TAC alg_ss [])
       ++ STRIP_TAC
       ++ RW_TAC std_ss [Once (GSYM MOD_TIMES2), MOD_MOD]
       ++ RW_TAC std_ss [MOD_TIMES2, LEFT_ADD_DISTRIB, MOD_PLUS],
       RW_TAC std_ss [GF_def, finite_num, GSPECIFICATION]
       ++ METIS_TAC []]);

val context = subtypeTools.add_reduction2 GF context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

(* ------------------------------------------------------------------------- *)
(* GF(2^n).                                                                  *)
(* ------------------------------------------------------------------------- *)

(* GF(2^n) = polynomials over GF(2) modulo an irreducible degree n poly *)

(***
val GF_2_def = Define
  `GF_2 n = 
   <| carrier := ;
      sum := ;
      prod :=  |>`;
***)

val () = export_theory ();
