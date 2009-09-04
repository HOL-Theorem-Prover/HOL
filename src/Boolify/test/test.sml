(* ========================================================================= *)
(* TEST SUITE FOR HOL BOOLIFICATION.                                         *)
(* Created by Joe Hurd, July 2002                                            *)
(* ========================================================================= *)

(*
val () =
  loadPath :=
  ["../../datatype/", "../../list/src", "../../tfl/src", "../src"] @
  !loadPath;
*)

val () = app load ["Encode", "EncodeTheory", "DecodeTheory", "CoderTheory"];

open EncodeTheory DecodeTheory CoderTheory;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun first_token (QUOTE s :: _) = hd (String.tokens Char.isSpace
                                            (Lib.deinitcomment s))
  | first_token _ = "if_you_can_read_this_then_first_token_probably_failed";
val size_of = Lib.total TypeBase.size_of;
val encode_of = Lib.total TypeBase.encode_of;

val Hol_datatype =
  fn q =>
  let
    val () = Lib.try (Count.apply Datatype.Hol_datatype) q
    val tyname = first_token q
  in
    (tyname, size_of tyname, encode_of tyname)
  end;

fun encode tm =
  let
    val db = TypeBase.theTypeBase()
    val f = TypeBasePure.type_encode db (type_of tm)
  in
    (*CONV_RULE (REDEPTH_CONV pairLib.PAIRED_BETA_CONV)*)
    (bossLib.EVAL (mk_comb (f, tm)))
  end;

(* ------------------------------------------------------------------------- *)
(* Example datatypes to test boolification.                                  *)
(* ------------------------------------------------------------------------- *)

try Hol_datatype `NumBool0 = Num0 of num | Bool0 of bool`;

try Hol_datatype `NumBoolNums = Num of num | Bool of bool | Nums of num list`;

try Hol_datatype `NTree = Tree of NTree list`;

try Hol_datatype `List = Nil | Cons of 'A => List`;

try Hol_datatype `tri = ONE | TWO | THREE`;

try Hol_datatype
  `command
       = Assignment of num list # expression list
       | Sequence   of command list
   ;
   expression
       = Numeral of num
       | Plus    of expression # expression
       | Valof   of command`;

try Hol_datatype
        `exp = VAR of 'a
             | IF  of bexp => exp => exp
             | APP of 'b => exp list
          ;
        bexp = EQ  of exp => exp
             | LEQ of exp => exp
             | AND of bexp => bexp
             | OR  of bexp => bexp
             | NOT of bexp`;

(* ------------------------------------------------------------------------- *)
(* Encoding of terms.                                                        *)
(* ------------------------------------------------------------------------- *)

val encode = encode o Term;

try encode `[(1,2,3,4) ; (5,6,7,8)]`;
try encode `(SOME F, 123, [F;T])`;
try encode `[]:num list`;
try encode `[1; 2; 3]`;
try encode `(Num 1, Nums [2; 3])`;
try encode `Tree [Tree []; Tree [Tree []; Tree []]; Tree []]`;
try encode `[INL TWO; INR (Bool0 T)]`;
try encode `Assignment ([1; 2], [Numeral 1])`;

(* ------------------------------------------------------------------------- *)
(* Decoding terms.                                                           *)
(* ------------------------------------------------------------------------- *)

val decode_numlist =
  MATCH_MP (INST_TYPE [alpha |-> Type`:num`] decode_list)
  (Q.SPEC `K T` wf_decode_num);

val () = computeLib.add_funs [decode_numlist];

val [encode_num_tm] = decls "encode_num";
val [decode_num_tm] = decls "decode_num";
val [decode_list_tm] = decls "decode_list";

fun Orelsef x [] = false
  | Orelsef x (h::t) = h(x) orelse Orelsef x t;

computeLib.monitoring :=
  SOME (fn x => Orelsef x
       (map same_const [encode_num_tm,decode_num_tm]));
      (map same_const [encode_num_tm,decode_num_tm,decode_list_tm]));

computeLib.monitoring := NONE;

fun ED tm =
 Count.apply
    EVAL (Term `decode_list (ALL_EL (K T)) (decode_num (K T))
                 (encode_list encode_num ^tm)`);

val th1 = bossLib.EVAL (Term` [1; 2; 3; 4]`);

val r = rhs (concl th1);
val M = Term`decode_list (ALL_EL (K T)) (decode_num (K T)) ^r`;

val conv = ONCE_REWRITE_CONV [decode_numlist, combinTheory.K_DEF,
                         listTheory.list_case_def, bool_case_thm]
           THENC DEPTH_CONV BETA_CONV;

fun convN 0 = ALL_CONV
  | convN n = conv THENC convN (n-1);


val th2 = bossLib.EVAL (Term`decode_list (ALL_EL (K T)) (decode_num (K T)) ^r`);

val th1 = bossLib.EVAL (Term`encode_list encode_num [1]`);

Count.apply EVAL (Term`decode_num (K T) (encode_num 4)`);

val N = Term`decode_list (ALL_EL (K T)) (decode_num (K T))
             ^(rhs(concl (EVAL (Term`encode_list encode_num [1; 2]`))))`;


EVAL (Term `decode_num (K T) [T; F; T; T; T; F; T; T; F]`);


(*---------------------------------------------------------------------------*)
(* Currently, the decoders installed for basic types are not efficient,      *)
(* mainly because they use case statements on the rhs, and that is not       *)
(* efficiently supported. The following two versions of decode_num and       *)
(* decode_list are far better.                                               *)
(*---------------------------------------------------------------------------*)

val decode_num_thm =
 mk_thm ([], Term
 `(decode_num P [] = NONE) /\
  (decode_num P [x] = NONE) /\
  (decode_num P (T::T::t) = SOME (0,t)) /\
  (decode_num P (T::F::t) =
     let x = decode_num P t
     in if IS_SOME x then (let (m,t') = THE(x) in SOME (2*m + 1, t'))
        else NONE) /\
  (decode_num P (F::t) =
     let x = decode_num P t
     in if IS_SOME x then (let (m,t') = THE(x) in SOME (2*m + 2, t'))
        else NONE)`);

val decode_list_thm =
 mk_thm ([],Term
  `(decode_list (ALL_EL (K T)) (decode_num (K T)) [] = NONE) /\
   (decode_list (ALL_EL (K T)) (decode_num (K T)) (F::t) = SOME([],t)) /\
   (decode_list (ALL_EL (K T)) (decode_num (K T)) (T::t) =
       let x = decode_num (K T) t
       in if IS_SOME x
            then let (y,t') = THE(x)
                 in let z = decode_list (ALL_EL (K T)) (decode_num (K T)) t'
                    in if IS_SOME z
                        then (let (u,w) = THE(z) in SOME (y::u,w))
                        else NONE
            else NONE)`);

computeLib.add_funs [decode_num_thm,decode_list_thm];
