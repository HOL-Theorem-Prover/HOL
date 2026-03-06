(* ========================================================================= *)
(* TEST SUITE FOR HOL BOOLIFICATION.                                         *)
(* Created by Joe Hurd, July 2002                                            *)
(* ========================================================================= *)

open EncodeTheory DecodeTheory CoderTheory;

local open Encode in end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun mkTy nm =
  let val thy = current_theory()
      val kid = {Thy = thy, Tyop = nm}
      val n = valOf (Type.op_arity kid)
    in
      mk_thy_type {
        Thy = thy, Tyop = nm,
         Args = List.tabulate(n, fn i => mk_vartype ("'a" ^ Int.toString i))
      }
    end

val size_of = Lib.total (TypeBase.size_of o mkTy)
val encode_of = Lib.total (TypeBase.encode_of o mkTy)

fun Hol_datatype q =
  let
    val asts = ParseDatatype.parse (Parse.type_grammar()) q
    val tyname = fst(hd asts)
    val () = Datatype.Hol_datatype q

  in
    (tyname, size_of tyname, encode_of tyname)
  end;

(* ------------------------------------------------------------------------- *)
(* Example datatypes to test auto-definition of encoders.                    *)
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
(* Test synthesis of encoders.                                               *)
(* ------------------------------------------------------------------------- *)

fun encode tm =
  let
    val db = TypeBase.theTypeBase()
    val f = TypeBasePure.type_encode db (type_of tm)
  in
    bossLib.EVAL (mk_comb (f, tm))
  end;

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
(* Decoding terms. Only num lists at present                                 *)
(* ------------------------------------------------------------------------- *)

val decode_numlist =
  MATCH_MP (INST_TYPE [alpha |-> Type`:num`] decode_list)
  (Q.SPEC `K T` wf_decode_num);

val () = computeLib.add_funs [decode_numlist];

fun Enc_Dec tm =
 Count.apply
    EVAL ``decode_list (EVERY (K T)) (decode_num (K T))
                 (encode_list encode_num ^tm)``;

val th1 = Enc_Dec ``[1; 2; 3; 4]``;

Definition enc_dec_checker_def:
  checker nlist <=>
    decode_list (EVERY (K T)) (decode_num (K T))
       (encode_list encode_num nlist) = SOME(nlist,[])
End

EVAL ``checker ([]:num list)``;
EVAL ``checker [1]``;

(* Check Encode-Decode on lists upto first 50 numbers *)

let val thm = EVAL ``EVERY checker (MAP (GENLIST I) (GENLIST I 50))``
in if same_const T (rhs(concl thm))
    then print "num list encode/decode tests PASS\n"
    else raise mk_HOL_ERR "encode/decode test" "FAIL" ""
end
