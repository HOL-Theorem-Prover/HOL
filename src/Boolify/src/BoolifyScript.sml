open HolKernel boolLib Parse pairSyntax numSyntax listSyntax
  combinSyntax arithmeticTheory mesonLib simpLib boolSimps numLib
  optionTheory oneTheory;

val _ = new_theory "Boolify";

infix 0 THEN |->;
infixr 1 --> by;

val arith_ss = bool_ss ++ numSimps.ARITH_ss;

(*---------------------------------------------------------------------------
     Constructor encodings 
 ---------------------------------------------------------------------------*)

val encT     = Term `[T]`   (* booleans *)
val encF     = Term `[F]`
val encNone  = Term `[F]`   (* options *)
val encSome  = Term `[T]`
val encB2    = Term `[F]`   (* numbers *)
val encB1    = Term `[T;F]`
val encZ     = Term `[T;T]`
val encNil   = Term `[F]`   (* lists *)
val encCons  = Term `[T]`
val encInl   = Term `[T]`   (* sums *)
val encInr   = Term `[F]`

(*---------------------------------------------------------------------------
        Booleans
 ---------------------------------------------------------------------------*)

val bool_to_bool_def =
  TotalDefn.Define `(bool_to_bool T = ^encT) /\ (bool_to_bool F = ^encF)`;

(*---------------------------------------------------------------------------
        Pairs
 ---------------------------------------------------------------------------*)

val prod_to_bool_def =
  TotalDefn.Define
  `prod_to_bool xb yb (x : 'a, y : 'b) : bool list = APPEND (xb x) (yb y)`;

(*---------------------------------------------------------------------------
        Sums
 ---------------------------------------------------------------------------*)

val sum_to_bool_def =
  TotalDefn.Define
  `(sum_to_bool xb yb (INL (x : 'a)) : bool list = APPEND ^encInl (xb x)) /\
   (sum_to_bool xb yb (INR (y : 'b)) = APPEND ^encInr (yb y))`;

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
