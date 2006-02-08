(* ========================================================================= *)
(* FILLING IN "BOOLIFY" ENTRIES IN THE TYPEBASE FOR TYPES BUILT BEFORE LISTS *)
(* Created by Joe Hurd and Konrad Slind, July 2002                           *)
(* ========================================================================= *)

(*
val () = loadPath := ["../../list/src"] @ !loadPath;
*)

(*
*)
structure PreListEncode :> PreListEncode =
struct

open HolKernel boolLib Parse pairSyntax numSyntax listSyntax
  combinSyntax arithmeticTheory mesonLib simpLib boolSimps numLib
  optionTheory EncodeTheory;

infix 0 THEN |->;
infixr 1 --> by;

val ERR = mk_HOL_ERR "PreListEncode";

(*---------------------------------------------------------------------------
        Booleans
 ---------------------------------------------------------------------------*)

val bool_info = Option.valOf (TypeBase.read {Thy= "min", Tyop="bool"});
val bool_boolify_info =
  (Term`encode_bool`, TypeBasePure.ORIG encode_bool_def);
val bool_info' = TypeBasePure.put_encode bool_boolify_info bool_info;

(*---------------------------------------------------------------------------
        Pairs
 ---------------------------------------------------------------------------*)

val prod_info = Option.valOf (TypeBase.read {Thy="pair", Tyop="prod"});
val prod_boolify_info =
  (Term`encode_prod:('a->bool list)->('b->bool list)-> 'a # 'b -> bool list`,
   TypeBasePure.ORIG encode_prod_def);
val prod_info' = TypeBasePure.put_encode prod_boolify_info prod_info;

(*---------------------------------------------------------------------------
        Sums
 ---------------------------------------------------------------------------*)

val sum_info = Option.valOf (TypeBase.read {Thy = "sum", Tyop = "sum"});
val sum_boolify_info =
  (Term`encode_sum:('a->bool list)->('b->bool list)-> 'a + 'b -> bool list`,
   TypeBasePure.ORIG encode_sum_def);
val sum_info' = TypeBasePure.put_encode sum_boolify_info sum_info;

(*---------------------------------------------------------------------------
        Options
 ---------------------------------------------------------------------------*)

val option_info =
    Option.valOf (TypeBase.read {Thy = "option", Tyop = "option"});
val option_boolify_info =
  (Term`encode_option : ('a -> bool list) -> 'a option -> bool list`,
   TypeBasePure.ORIG encode_option_def);
val option_info' = TypeBasePure.put_encode option_boolify_info option_info;

(*---------------------------------------------------------------------------
        Lists
 ---------------------------------------------------------------------------*)

val list_info = Option.valOf (TypeBase.read {Thy = "list", Tyop = "list"});
val list_boolify_info =
  (Term`encode_list : ('a -> bool list) -> 'a list -> bool list`,
   TypeBasePure.ORIG encode_list_def);
val list_info' = TypeBasePure.put_encode list_boolify_info list_info;

(*---------------------------------------------------------------------------
        Nums (Norrish numeral encoding)
 ---------------------------------------------------------------------------*)

val num_info = Option.valOf (TypeBase.read {Thy = "num", Tyop = "num"});
val num_boolify_info =
  (Term`encode_num`, TypeBasePure.ORIG encode_num_primitive_def);
val num_info' = TypeBasePure.put_encode num_boolify_info num_info;

(*---------------------------------------------------------------------------
      Units
 ---------------------------------------------------------------------------*)

val one_info = Option.valOf (TypeBase.read {Thy = "one", Tyop = "one"});
val one_boolify_info =
  (Term`encode_unit`, TypeBasePure.ORIG encode_unit_def);
val one_info' = TypeBasePure.put_encode one_boolify_info one_info;

(*---------------------------------------------------------------------------
      Writing all the boolification information to the typebase.
 ---------------------------------------------------------------------------*)

val _ = TypeBase.write [bool_info']
val _ = TypeBase.write [prod_info']
val _ = TypeBase.write [sum_info']
val _ = TypeBase.write [option_info']
val _ = TypeBase.write [list_info']
val _ = TypeBase.write [num_info']
val _ = TypeBase.write [one_info']


val () = computeLib.add_funs
  [encode_bool_def, encode_prod_def, encode_sum_def, encode_option_def,
   encode_list_def, encode_num_def, encode_unit_def];

end
