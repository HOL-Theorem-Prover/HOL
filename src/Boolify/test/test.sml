(* ========================================================================= *)
(* TEST SUITE FOR HOL BOOLIFICATION.                                         *)
(* Created by Joe Hurd, July 2002                                            *)
(* ========================================================================= *)

val () =
  loadPath :=
  ["../../datatype/", "../../list/src", "../../tfl/src", "../src"] @
  !loadPath;

app load
["sumTheory", "Datatype", "listTheory", "Encode", "bossLib"];

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun first_token (QUOTE s :: _) = hd (String.tokens Char.isSpace (Lib.deinitcomment s))
  | first_token _ = "if_you_can_read_this_then_first_token_probably_failed";
val size_of = Lib.total TypeBase.size_of;
val boolify_of = Lib.total TypeBase.boolify_of;

val Hol_datatype =
  fn q =>
  let
    val () = Lib.try (Count.apply Datatype.Hol_datatype) q
    val tyname = first_token q
  in
    (tyname, size_of tyname, boolify_of tyname)
  end;

fun boolify tm = 
  let
    val db = TypeBase.theTypeBase()
    val f = TypeBasePure.type_boolify db (type_of tm)
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
(* Boolification of terms.                                                   *)
(* ------------------------------------------------------------------------- *)

try boolify (Term `[(1,2,3,4) ; (5,6,7,8)]`);
try boolify (Term `(SOME F, 123, [F;T])`);
try boolify (Term `[]:num list`);
try boolify (Term `[1; 2; 3]`);
try boolify (Term `(Num 1, Nums [2; 3])`);
try boolify (Term `Tree [Tree []; Tree [Tree []; Tree []]; Tree []]`);
try boolify (Term `[INL TWO; INR (Bool0 T)]`);
try boolify (Term `Assignment ([1; 2], [Numeral 1])`);
