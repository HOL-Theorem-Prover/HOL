open HolKernel boolLib Parse pairSyntax numSyntax listSyntax
  combinSyntax arithmeticTheory mesonLib simpLib boolSimps numLib
  optionTheory oneTheory listTheory combinTheory state_transformerTheory
  pairTheory;

val _ = new_theory "Boolify";

infix 0 THEN |->;
infixr 1 --> by;

val arith_ss = bool_ss ++ numSimps.ARITH_ss;

(*---------------------------------------------------------------------------
     Constructor encodings 
 ---------------------------------------------------------------------------*)

val encNone  = Term `[F]`;   (* options *)
val encSome  = Term `[T]`;
val encZ     = Term `[T;T]`; (* numbers *)
val encB1    = Term `[T;F]`;
val encB2    = Term `[F]`;
val encNil   = Term `[F]`;   (* lists *)
val encCons  = Term `[T]`;
val encInl   = Term `[T]`;   (* sums *)
val encInr   = Term `[F]`;

(*---------------------------------------------------------------------------
     Fixed size encodings---necessary for boolifying variables.
 ---------------------------------------------------------------------------*)

val fixed_width_const_exists = prove
  (``?fixed_width. !(bx : bool list -> 'a # bool list) n x.
       x IN fixed_width bx n = ?w. (LENGTH w = n) /\ (FST (bx w) = x)``,
   EXISTS_TAC
   ``\ (bx : bool list -> 'a # bool list) n x.
       ?w. (LENGTH w = n) /\ (FST (bx w) = x)`` THEN
   SIMP_TAC bool_ss [IN_DEF]);

val fixed_width_def =
  Definition.new_specification
  ("fixed_width_def", ["fixed_width"], fixed_width_const_exists);

val _ = add_const "fixed_width";

val of_length_const_exists = prove
  (``?of_length. !(l : 'a list) n. l IN of_length n = (LENGTH l = n)``,
   EXISTS_TAC ``\n (l : 'a list). LENGTH l = n`` THEN
   SIMP_TAC bool_ss [IN_DEF]);

val of_length_def =
  Definition.new_specification
  ("of_length_def", ["of_length"], of_length_const_exists);

val _ = add_const "of_length";

val fixed_width_univ = store_thm
  ("fixed_width_univ",
   ``!(phi : 'a -> bool) bx n.
       (!x :: fixed_width bx n. phi x) = !w :: of_length n. phi (FST (bx w))``,
   SIMP_TAC bool_ss [RES_FORALL_DEF, fixed_width_def, of_length_def] THEN
   REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
   ASM_MESON_TAC []);

val of_length_univ_suc = store_thm
  ("of_length_univ_suc",
   ``!phi n.
       (!w :: of_length (SUC n). phi (w : 'a list)) =
       (!x. !w :: of_length n. phi (x :: w))``,
   SIMP_TAC bool_ss [RES_FORALL_DEF, of_length_def] THEN
   REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
   [Q.PAT_ASSUM `!x. Q x` MATCH_MP_TAC THEN
    ASM_SIMP_TAC arith_ss [LENGTH],
    MP_TAC (ISPEC ``x : 'a list`` list_CASES) THEN
    STRIP_TAC THENL
    [FULL_SIMP_TAC arith_ss [LENGTH],
     FULL_SIMP_TAC arith_ss [LENGTH]]]);

val of_length_univ_zero = store_thm
  ("of_length_univ_zero",
   ``!phi. (!w :: of_length 0. phi w) = phi ([] : 'a list)``,
   SIMP_TAC bool_ss [RES_FORALL_DEF, of_length_def, LENGTH_NIL]);

val fixed_width_exists = store_thm
  ("fixed_width_exists",
   ``!(phi : 'a -> bool) bx n.
       (?x :: fixed_width bx n. phi x) = ?w :: of_length n. phi (FST (bx w))``,
   SIMP_TAC bool_ss [RES_EXISTS_DEF, fixed_width_def, of_length_def] THEN
   REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
   ASM_MESON_TAC []);

val of_length_exists_suc = store_thm
  ("of_length_exists_suc",
   ``!phi n.
       (?w :: of_length (SUC n). phi (w : 'a list)) =
       (?x. ?w :: of_length n. phi (x :: w))``,
   SIMP_TAC bool_ss [RES_EXISTS_DEF, of_length_def, UNIT_DEF] THEN
   REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
   [MP_TAC (ISPEC ``x:'a list`` list_CASES) THEN
    (STRIP_TAC THEN1 FULL_SIMP_TAC arith_ss [LENGTH]) THEN
    FULL_SIMP_TAC arith_ss [LENGTH] THEN
    EXISTS_TAC ``h : 'a`` THEN
    EXISTS_TAC ``t : 'a list`` THEN
    ASM_SIMP_TAC bool_ss [],
    EXISTS_TAC ``(x : 'a) :: x'`` THEN
    ASM_SIMP_TAC arith_ss [LENGTH]]);

val of_length_exists_zero = store_thm
  ("of_length_exists_zero",
   ``!phi. (?w :: of_length 0. phi w) = phi ([] : 'a list)``,
   SIMP_TAC bool_ss [RES_EXISTS_DEF, of_length_def, LENGTH_NIL]);

(*---------------------------------------------------------------------------
        Booleans
 ---------------------------------------------------------------------------*)

val bool_to_bool_def = TotalDefn.Define
  `bool_to_bool (x : bool) = [x]`;

val bool_from_bool_def = TotalDefn.Define
  `bool_from_bool (x :: l) = (x : bool, l)`;

(* Don't know exactly what this should be...
val bool_fixed_width = prove
  (``!x. x IN fixed_width bool_from_bool 1``,
   GEN_TAC THEN
   ASM_CASES_TAC ``x:bool`` THEN
   ASM_SIMP_TAC arith_ss [fixed_width_def, LENGTH, bool_to_bool_def]);
*)

(*---------------------------------------------------------------------------
        Pairs
 ---------------------------------------------------------------------------*)

val prod_to_bool_def =
  TotalDefn.Define
  `prod_to_bool xb yb (x : 'a, y : 'b) : bool list = APPEND (xb x) (yb y)`;

(* Don't know exactly what this should be...
val prod_fixed_width = prove
  (``!xb yb m n x y.
       x IN fixed_width xb m /\ y IN fixed_width yb n ==>
       (x, y) IN fixed_width (prod_to_bool xb yb) (m + n)``,
   SIMP_TAC arith_ss [fixed_width_def, LENGTH_APPEND, prod_to_bool_def]);
*)

(*---------------------------------------------------------------------------
        Sums
 ---------------------------------------------------------------------------*)

val sum_to_bool_def =
  TotalDefn.Define
  `(sum_to_bool xb yb (INL (x : 'a)) : bool list = APPEND ^encInl (xb x)) /\
   (sum_to_bool xb yb (INR (y : 'b)) = APPEND ^encInr (yb y))`;

(* Don't know exactly what this should be...
val sum_fixed_width = prove
  (``!xb yb n x y.
       x IN fixed_width xb n /\ y IN fixed_width yb n ==>
       (x, y) IN fixed_width (prod_to_bool xb yb) (m + n)``,
   SIMP_TAC arith_ss [fixed_width_def, LENGTH_APPEND, prod_to_bool_def]);
*)

(*---------------------------------------------------------------------------
        Options
 ---------------------------------------------------------------------------*)

val option_to_bool_def =
  TotalDefn.Define
  `(option_to_bool xb NONE = ^encNone) /\
   (option_to_bool xb (SOME x) = APPEND ^encSome (xb x))`;

(*---------------------------------------------------------------------------
        Lists
 ---------------------------------------------------------------------------*)

val list_to_bool_def = 
  TotalDefn.Define
  `(list_to_bool xb [] = ^encNil) /\
   (list_to_bool xb (x::xs) =
    APPEND ^encCons (APPEND (xb x) (list_to_bool xb xs)))`;

(*---------------------------------------------------------------------------
        Nums (Norrish numeral encoding)
 ---------------------------------------------------------------------------*)

val (num_to_bool_def, num_to_bool_ind) =
  Defn.tprove
  (Defn.Hol_defn "num_to_bool"
   `num_to_bool (n:num) = 
    if n = 0 then ^encZ
    else if EVEN n then APPEND ^encB2 (num_to_bool ((n-2) DIV 2))
    else APPEND ^encB1 (num_to_bool ((n-1) DIV 2))`,
   TotalDefn.WF_REL_TAC `$<` THEN
   REPEAT STRIP_TAC THEN
   (KNOW_TAC (Term`?j. n = SUC j`) THEN1 ASM_MESON_TAC [num_CASES]) THEN
   STRIP_TAC THEN
   IMP_RES_TAC EVEN_EXISTS THEN
   ASM_SIMP_TAC arith_ss
   [SUC_SUB1,MULT_DIV,DIV_LESS_EQ,
    EQT_ELIM (ARITH_CONV (Term `2n*m - 2n = (m-1n)*2n`)),
    EQT_ELIM (ARITH_CONV (Term `x < SUC y = x <= y`))]);

val _ = save_thm ("num_to_bool_def", num_to_bool_def);
val _ = save_thm ("num_to_bool_ind", num_to_bool_ind);
  
  (*--------------------------------------------------------------------
       Termination proof can also go: 

           WF_REL_TAC `$<` THEN intLib.COOPER_TAC

       but then we'd need integers.
   ----------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
      The unit type is cool because it consumes no space in the
      target list: the type has all the information!
 ---------------------------------------------------------------------------*)

val one_to_bool_def =
  TotalDefn.Define `one_to_bool (_ : one) : bool list = []`;

val _ = export_theory ();
