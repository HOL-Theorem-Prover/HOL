(* ========================================================================= *)
(* Create "elliptic_exampleTheory" compiling elliptic curve operations.      *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Load and open relevant theories.                                          *)
(* (Comment out "load"s and "quietdec"s for compilation.)                    *)
(* ------------------------------------------------------------------------- *)
(*
val () = loadPath := [] @ !loadPath;
val () = app load ["bossLib", "metisLib", "wordsLib",
                   "primalityTools", "ellipticTools"];
val () = quietdec := true;
*)

open HolKernel Parse boolLib bossLib metisLib
     arithmeticTheory pred_setTheory wordsTheory
     primalityTools
     groupTheory groupTools
     fieldTheory fieldTools
     ellipticTheory ellipticTools;

(*
val () = quietdec := false;
*)

(* ------------------------------------------------------------------------- *)
(* Start a new theory called "elliptic".                                     *)
(* ------------------------------------------------------------------------- *)

val _ = new_theory "elliptic_example";

(* ------------------------------------------------------------------------- *)
(* Sort out the parser.                                                      *)
(* ------------------------------------------------------------------------- *)

val () = Parse.add_infix ("/", 600, HOLgrammars.LEFT);

(* ------------------------------------------------------------------------- *)
(* The subtype context.                                                      *)
(* ------------------------------------------------------------------------- *)

val context = elliptic_context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

(* ------------------------------------------------------------------------- *)
(* Helper proof tools.                                                       *)
(* ------------------------------------------------------------------------- *)

infixr 0 <<
infixr 1 ++ || THENC ORELSEC
infix 2 >>

val op ++ = op THEN;
val op << = op THENL;
val op >> = op THEN1;
val op || = op ORELSE;
val Know = Q_TAC KNOW_TAC;
val Suff = Q_TAC SUFF_TAC;

(* ------------------------------------------------------------------------- *)
(* Extensions to HOL theories to define the ex_ constants.                   *)
(* ------------------------------------------------------------------------- *)


(* ========================================================================= *)
(* Smallest elliptic curve example to be compiled.                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* First define the parameters for the example using HOL types.              *)
(* ------------------------------------------------------------------------- *)

val example1_prime_def = Define `example1_prime = 751`;

val example1_field_def = Define `example1_field = GF example1_prime`;

val example1_curve_def = Define
  `example1_curve = curve example1_field 0 0 1 (example1_prime - 1) 0`;

val example1_elgamal_g_def = Define
  `example1_elgamal_g = affine example1_field [361; 383]`;

val example1_elgamal_x_def = Define `example1_elgamal_x = 91`;

val example1_elgamal_h_def = Define
  `example1_elgamal_h =
   curve_mult example1_curve example1_elgamal_g example1_elgamal_x`;

val example1_prime = Count.apply prove
  (``example1_prime IN Prime``,
   RW_TAC alg_ss [example1_prime_def, Prime_def, GSPECIFICATION]
   ++ CONV_TAC prime_checker_conv);

val context = subtypeTools.add_reduction2 example1_prime context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val example1_field = prove
  (``example1_field IN Field``,
   RW_TAC alg_ss [example1_field_def]);

val context = subtypeTools.add_reduction2 example1_field context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val example1_curve = prove
  (``example1_curve IN Curve``,
   RW_TAC alg_ss [example1_curve_def, Curve_def, GSPECIFICATION]
   ++ RW_TAC alg_ss [example1_field_def, example1_prime_def]
   ++ RW_TAC alg_ss [non_singular_def, LET_DEF, discriminant_def]
   ++ RW_TAC alg_ss
        [LET_DEF, GF_alt, curve_b2_def, curve_b4_def,
         curve_b6_def, curve_b8_def, field_exp_small]
   ++ CONV_TAC EVAL);

val context = subtypeTools.add_reduction2 example1_curve context;
val {simplify = alg_ss, normalize = alg_ss'} = subtypeTools.simpset2 context;

val example1_curve_field = prove
  (``example1_curve.field = example1_field``,
   RW_TAC alg_ss [example1_curve_def]);

(*** Need to reduce elgamal_h before anything happens
val example1_elgamal_h_alt =
    SIMP_CONV
      (simpLib.++ (alg_ss,numSimps.SUC_FILTER_ss))
      [curve_mult_def,
       example1_elgamal_g_def,
       example1_elgamal_x_def,
       example1_elgamal_h_def]
    ``example1_elgamal_h``;
***)

(* ------------------------------------------------------------------------- *)
(* Converting HOL types to words.                                            *)
(* ------------------------------------------------------------------------- *)

val ex1_prime_def = Define `ex1_prime : word32 = n2w example1_prime`;

val ex1_field_elt_def = Define
  `ex1_field_elt (n : num) : word32 = n2w n`;

val ex1_field_num_def = Define
  `ex1_field_num (n : num) : word32 = ex1_field_elt (n MOD example1_prime)`;

val ex1_curve_point_def = Define
  `ex1_curve_point =
   affine_case example1_curve
     (0w,0w) (\x y. (ex1_field_elt x, ex1_field_elt y))`;

val ex1_elgamal_g_x = Define
  `ex1_elgamal_g_x = FST (ex1_curve_point example1_elgamal_g)`;

val ex1_elgamal_g_y = Define
  `ex1_elgamal_g_y = SND (ex1_curve_point example1_elgamal_g)`;

val ex1_elgamal_h_x = Define
  `ex1_elgamal_h_x = FST (ex1_curve_point example1_elgamal_h)`;

val ex1_elgamal_h_y = Define
  `ex1_elgamal_h_y = SND (ex1_curve_point example1_elgamal_h)`;

val ex1_elgamal_x = Define `ex1_elgamal_x = n2w example1_elgamal_x`;

(* ------------------------------------------------------------------------- *)
(* Representing GF(p) field elements with words.                             *)
(* ------------------------------------------------------------------------- *)

val ex1_field_zero_def = Define
  `ex1_field_zero = ex1_field_num 0`;

val ex1_field_neg_def = Define
  `ex1_field_neg (x : word32) =
   if x = 0w then 0w else ex1_prime - x`;

val ex1_field_add_def = Define
  `ex1_field_add (x : word32, y : word32) =
   let z = x + y in
   if z < ex1_prime then z else z - ex1_prime`;

val ex1_field_sub_def = Define
  `ex1_field_sub (x : word32, y : word32) =
   ex1_field_add (x, ex1_field_neg y)`;

val ex1_field_mult_aux_def = 
 Define 
   `ex1_field_mult_aux (x : word32, y : word32, acc : word32) =
     if y = 0w then acc
     else 
       let x' = ex1_field_add (x,x) in
       let y' = y >>> 1 in
       let acc' = if y && 1w = 0w then acc else ex1_field_add (acc,x) 
       in
         ex1_field_mult_aux (x',y',acc')`;


val ex1_field_mult_def = Define
   `ex1_field_mult (x : word32, y : word32) = ex1_field_mult_aux (x,y,0w)`;

val ex1_field_exp_aux_def = 
 Define
   `ex1_field_exp_aux (x : word32, n : word32, acc : word32) =
      if n = 0w then acc
      else
        let x' = ex1_field_mult (x,x) in
        let n' = n >>> 1 in
        let acc' = if n && 1w = 0w then acc else ex1_field_mult (acc,x) 
        in ex1_field_exp_aux (x',n',acc')`;

val ex1_field_exp_def = Define
   `ex1_field_exp (x : word32, n : word32) = ex1_field_exp_aux (x,n,1w)`;

val ex1_field_inv_def = Define
   `ex1_field_inv (x : word32) = ex1_field_exp (x, n2w (example1_prime - 2))`;

val ex1_field_div_def = Define
   `ex1_field_div (x:word32, y:word32) = ex1_field_mult (x, ex1_field_inv y)`;

(* ------------------------------------------------------------------------- *)
(* Elliptic curve operations in terms of the above field operations.         *)
(* ------------------------------------------------------------------------- *)

val ex1_curve_zero_def = Define
  `ex1_curve_zero = ex1_curve_point (curve_zero example1_curve)`;

val ex1_curve_neg_def = Define
  `ex1_curve_neg (x1,y1) =
   let $~ = ex1_field_neg in
   let $- = CURRY ex1_field_sub in
   let $* = CURRY ex1_field_mult in
   let a1 = ex1_field_elt example1_curve.a1 in
   let a3 = ex1_field_elt example1_curve.a3 
   in
     if (x1,y1) = ex1_curve_zero 
       then ex1_curve_zero
       else let x = x1 in
            let y = ~y1 - a1 * x1 - a3 
            in (x,y)`;

val ex1_curve_double_def = Define
  `ex1_curve_double (x1,y1) =
   let $& = ex1_field_num in
   let $~ = ex1_field_neg in
   let $+ = CURRY ex1_field_add in
   let $- = CURRY ex1_field_sub in
   let $* = CURRY ex1_field_mult in
   let $/ = CURRY ex1_field_div in
   let $** = CURRY ex1_field_exp in
   let a1 = ex1_field_elt example1_curve.a1 in
   let a2 = ex1_field_elt example1_curve.a2 in
   let a3 = ex1_field_elt example1_curve.a3 in
   let a4 = ex1_field_elt example1_curve.a4 in
   let a6 = ex1_field_elt example1_curve.a6 
   in
     if (x1,y1) = ex1_curve_zero then ex1_curve_zero
     else
       let d = & 2 * y1 + a1 * x1 + a3 
       in if d = ex1_field_zero then ex1_curve_zero
          else
            let l = (& 3 * x1 ** 2w + & 2 * a2 * x1 + a4 - a1 * y1) / d in
            let m = (~(x1 ** 3w) + a4 * x1 + & 2 * a6 - a3 * y1) / d in
            let x = l ** 2w + a1 * l - a2 - &2 * x1 in
            let y = ~(l + a1) * x - m - a3 
            in (x,y)`;

val ex1_curve_add_def = Define
  `ex1_curve_add (x1,y1,x2,y2) =
   if (x1 = x2) /\ (y1 = y2) then ex1_curve_double (x1,y1)
   else
     let $& = ex1_field_num in
     let $~ = ex1_field_neg in
     let $+ = CURRY ex1_field_add in
     let $- = CURRY ex1_field_sub in
     let $* = CURRY ex1_field_mult in
     let $/ = CURRY ex1_field_div in
     let $** = CURRY ex1_field_exp in
     let a1 = ex1_field_elt example1_curve.a1 in
     let a2 = ex1_field_elt example1_curve.a2 in
     let a3 = ex1_field_elt example1_curve.a3 in
     let a4 = ex1_field_elt example1_curve.a4 in
     let a6 = ex1_field_elt example1_curve.a6 in
     if (x1,y1) = ex1_curve_zero then (x2,y2)
     else if (x2,y2) = ex1_curve_zero then (x1,y1)
     else if x1 = x2 then ex1_curve_zero
     else
       let d = x2 - x1 in
       let l = (y2 - y1) / d in
       let m = (y1 * x2 - y2 * x1) / d in
       let x = l ** 2w + a1 * l - a2 - x1 - x2 in
       let y = ~(l + a1) * x - m - a3 in
       (x,y)`;

val ex1_curve_mult_aux_def = 
 Define
  `ex1_curve_mult_aux (x : word32, y : word32, n : word32,
                       acc_x : word32, acc_y : word32) =
    if n = 0w then (acc_x,acc_y)
    else
      let (x',y') = ex1_curve_double (x,y) in
      let n' = n >>> 1 in
      let (acc_x',acc_y') = 
            if n && 1w = 0w then (acc_x,acc_y)
            else ex1_curve_add (x,y,acc_x,acc_y) 
      in 
        ex1_curve_mult_aux (x',y',n',acc_x',acc_y')`;


val ex1_curve_mult_def = 
 Define
   `ex1_curve_mult (x:word32, y:word32, n:word32) 
     = ex1_curve_mult_aux (x,y,n,0w,0w)`;

(* ------------------------------------------------------------------------- *)
(* Elliptic curve encryption and decryption functions.                       *)
(* These form the API, and need to be compiled.                              *)
(* ------------------------------------------------------------------------- *)

val ex1_elgamal_encrypt_def = Define
  `ex1_elgamal_encrypt (m_x : word32, m_y : word32, k : word32) =
   let (a_x,a_y) = ex1_curve_mult (ex1_elgamal_g_x,ex1_elgamal_g_y,k) in
   let (t_x,t_y) = ex1_curve_mult (ex1_elgamal_h_x,ex1_elgamal_h_y,k) in
   let (b_x,b_y) = ex1_curve_add (t_x,t_y,m_x,m_y) in
   (a_x,a_y,b_x,b_y)`;

val ex1_elgamal_decrypt_def = Define
  `ex1_elgamal_decrypt (a_x,a_y,b_x,b_y) =
   let (t_x,t_y) = ex1_curve_neg (ex1_curve_mult (a_x,b_x,ex1_elgamal_x)) in
   ex1_curve_add (t_x,t_y,b_x,b_y)`;

(* ------------------------------------------------------------------------- *)
(* The first stage of compiling is to propagate all constants, especially to *)
(* eliminate HOL types that are not just tuples of word32s.                  *)
(* ------------------------------------------------------------------------- *)

local
  val is_word_tuple =
      let
        fun f ty =
            if wordsSyntax.is_word_type ty then ()
            else let val (x,y) = pairLib.dest_prod ty in f x; f y end
      in
        can f
      end;

  fun blocked (f,x) =
      is_word_tuple (type_of x) andalso
      not (is_var x) andalso
      not (wordsSyntax.is_n2w x);
in
  fun constant_propagation_let_conv tm =
      if blocked (dest_let tm) then
        raise ERR "constant_propagation_let_conv" "blocked"
      else
        REWR_CONV LET_THM tm;
end;

val constant_propagation_SS =
    simpLib.SSFRAG
      {convs = [{name = "constant_propagation_let_conv",
                 key = SOME ([], ``LET f x``),
                 trace = 2,
                 conv = K (K constant_propagation_let_conv)}],
       rewrs = [curve_a1,
                curve_a2,
                curve_a3,
                curve_a4,
                curve_a6,
                affine_case,
                curve_mult_def],
       ac = [],
       filter = NONE,
       dprocs = [],
       congs = []};

val constant_propagation_ss =
    simpLib.++
      (simpLib.++ (alg_ss,numSimps.REDUCE_ss), constant_propagation_SS);

val ex1_constant_propagation =
    CONV_RULE
      (SIMP_CONV
         constant_propagation_ss
         [GSYM example1_curve_field,
          example1_elgamal_g_def,
          example1_elgamal_h_def,
          example1_elgamal_x_def,
          ex1_curve_zero_def,
          ex1_curve_point_def,
          ex1_elgamal_g_x,
          ex1_elgamal_g_y,
          ex1_elgamal_h_x,
          ex1_elgamal_h_y,
          ex1_elgamal_x] THENC
       SIMP_CONV
         constant_propagation_ss
         [example1_curve_field,
          example1_prime_def,
          example1_field_def,
          example1_curve_def,
          ex1_prime_def,
          ex1_field_elt_def,
          ex1_field_num_def,
          ex1_field_zero_def]);

val ex1_field_neg_alt = save_thm
  ("ex1_field_neg_alt",
   ex1_constant_propagation ex1_field_neg_def);

val ex1_field_add_alt = save_thm
  ("ex1_field_add_alt",
   ex1_constant_propagation ex1_field_add_def);

val ex1_field_sub_alt = save_thm
  ("ex1_field_sub_alt",
   ex1_constant_propagation ex1_field_sub_def);

val ex1_field_mult_aux_alt = save_thm
  ("ex1_field_mult_aux_alt",
   ex1_constant_propagation ex1_field_mult_aux_def);

val ex1_field_mult_alt = save_thm
  ("ex1_field_mult_alt",
   ex1_constant_propagation ex1_field_mult_def);

val ex1_field_exp_aux_alt = save_thm
  ("ex1_field_exp_aux_alt",
   ex1_constant_propagation ex1_field_exp_aux_def);

val ex1_field_exp_alt = save_thm
  ("ex1_field_exp_alt",
   ex1_constant_propagation ex1_field_exp_def);

val ex1_field_inv_alt = save_thm
  ("ex1_field_inv_alt",
   ex1_constant_propagation ex1_field_inv_def);

val ex1_field_div_alt = save_thm
  ("ex1_field_div_alt",
   ex1_constant_propagation ex1_field_div_def);

val ex1_curve_neg_alt = save_thm
  ("ex1_curve_neg_alt",
   ex1_constant_propagation ex1_curve_neg_def);

val ex1_curve_double_alt = save_thm
  ("ex1_curve_double_alt",
   ex1_constant_propagation ex1_curve_double_def);

val ex1_curve_add_alt = save_thm
  ("ex1_curve_add_alt",
   ex1_constant_propagation ex1_curve_add_def);

val ex1_curve_mult_aux_alt = save_thm
  ("ex1_curve_mult_aux_alt",
   ex1_constant_propagation ex1_curve_mult_aux_def);

val ex1_curve_mult_alt = save_thm
  ("ex1_curve_mult_alt",
   ex1_constant_propagation ex1_curve_mult_def);

val ex1_elgamal_encrypt_alt = save_thm
  ("ex1_elgamal_encrypt_alt",
   ex1_constant_propagation ex1_elgamal_encrypt_def);

val ex1_elgamal_decrypt_alt = save_thm
  ("ex1_elgamal_decrypt_alt",
   ex1_constant_propagation ex1_elgamal_decrypt_def);

(* ========================================================================= *)
(* A multiword elliptic curve example to be compiled.                        *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* First define the parameters for the example using HOL types.              *)
(* ------------------------------------------------------------------------- *)

val example2_prime_def = Define `example2_prime = 751`;

val example2_field_def = Define `example2_field = GF example2_prime`;

(* ------------------------------------------------------------------------- *)
(* Converting HOL types to words.                                            *)
(* ------------------------------------------------------------------------- *)

val ex2_prime0 = Define
  `ex2_prime0 : word32 = n2w example2_prime`;

val ex2_prime1 = Define
  `ex2_prime1 : word32 = n2w (example2_prime DIV 2 ** 32)`;

val ex2_field_neg_def = Define
  `ex2_field_neg (x0 : word32, x1 : word32) =
   if (x0 = 0w) /\ (x1 = 0w) then (0w,0w)
   else
     let y0 = ex2_prime0 - x0 in
     let y1 = if y0 <= ex2_prime0 then ex2_prime1 - x1
              else ex2_prime1 - (x1 + 1w) in
     (y0,y1)`;

val () = export_theory ();
