(* ========================================================================= *)
(* FILLING IN "BOOLIFY" ENTRIES IN THE TYPEBASE FOR TYPES BUILT BEFORE LISTS *)
(* Created by Joe Hurd and Konrad Slind, July 2002                           *)
(* ========================================================================= *)

(*
val () = loadPath := ["../../list/src"] @ !loadPath;
*)

(*
*)
structure PreListBoolify :> PreListBoolify =
struct

open HolKernel boolLib Parse pairSyntax numSyntax listSyntax
  combinSyntax arithmeticTheory mesonLib simpLib boolSimps numLib
  optionTheory BoolifyTheory;
  
infix 0 THEN |->;
infixr 1 --> by;

val ERR = mk_HOL_ERR "PreListBoolify";

(*---------------------------------------------------------------------------
        Booleans
 ---------------------------------------------------------------------------*)
  
val bool_info = Option.valOf (TypeBase.read "bool");
val bool_boolify_info =
  (Term`bool_to_bool`, TypeBasePure.ORIG bool_to_bool_def);
val bool_info' = TypeBasePure.put_boolify bool_boolify_info bool_info;

(*---------------------------------------------------------------------------
        Pairs
 ---------------------------------------------------------------------------*)

val prod_info = Option.valOf (TypeBase.read "prod");
val prod_boolify_info =
  (Term`prod_to_bool:('a->bool list)->('b->bool list)-> 'a # 'b ->bool list`,
   TypeBasePure.ORIG prod_to_bool_def);
val prod_info' = TypeBasePure.put_boolify prod_boolify_info prod_info;

(*---------------------------------------------------------------------------
        Sums
 ---------------------------------------------------------------------------*)

val sum_info = Option.valOf (TypeBase.read "sum");
val sum_boolify_info =
  (Term`sum_to_bool:('a->bool list)->('b->bool list)-> 'a + 'b ->bool list`,
   TypeBasePure.ORIG sum_to_bool_def);
val sum_info' = TypeBasePure.put_boolify sum_boolify_info sum_info;

(*---------------------------------------------------------------------------
        Options
 ---------------------------------------------------------------------------*)

val option_info = Option.valOf (TypeBase.read "option");
val option_boolify_info =
  (Term`option_to_bool : ('a -> bool list) -> 'a option -> bool list`,
   TypeBasePure.ORIG option_to_bool_def);
val option_info' = TypeBasePure.put_boolify option_boolify_info option_info;

(*---------------------------------------------------------------------------
        Lists
 ---------------------------------------------------------------------------*)

val list_info = Option.valOf (TypeBase.read "list");
val list_boolify_info =
  (Term`list_to_bool : ('a -> bool list) -> 'a list -> bool list`,
   TypeBasePure.ORIG list_to_bool_def);
val list_info' = TypeBasePure.put_boolify list_boolify_info list_info;

(*---------------------------------------------------------------------------
        Nums (Norrish numeral encoding)
 ---------------------------------------------------------------------------*)

val num_info = Option.valOf (TypeBase.read "num");
val num_boolify_info =
  (Term`num_to_bool`, TypeBasePure.ORIG num_to_bool_primitive_def);
val num_info' = TypeBasePure.put_boolify num_boolify_info num_info;

(*---------------------------------------------------------------------------
      Units
 ---------------------------------------------------------------------------*)

(* This is waiting to spring into action when there's a proper TypeBase
   entry for units.
val one_info = Option.valOf (TypeBase.read "one");
val one_boolify_info =
  (Term`one_to_bool`, TypeBasePure.ORIG one_to_bool_def);
val one_info' = TypeBasePure.put_boolify one_boolify_info one_info;
*)

(*---------------------------------------------------------------------------
      Writing all the boolification information to the typebase.
 ---------------------------------------------------------------------------*)

val _ = TypeBase.write [bool_info']
val _ = TypeBase.write [prod_info']
val _ = TypeBase.write [sum_info']
val _ = TypeBase.write [option_info']
val _ = TypeBase.write [list_info']
val _ = TypeBase.write [num_info']
(* See comment in unit section
val _ = TypeBase.write [one_info']
*)

val () = computeLib.add_funs
  [bool_to_bool_def, prod_to_bool_def, sum_to_bool_def, option_to_bool_def,
   list_to_bool_def, num_to_bool_def, one_to_bool_def];

end