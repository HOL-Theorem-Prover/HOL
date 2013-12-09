(*---------------------------------------------------------------------------*
 * Setting information for types.                                            *
 *                                                                           *
 * Here we fill in the "size" entries in theTypeBase for some types that     *
 * are non-recursive and built before numbers. Also add some lifters.        *
 *---------------------------------------------------------------------------*)

structure basicSize =
struct

local
  open HolKernel boolLib Parse basicSizeTheory basicSizeSyntax

  (*----------------------------------------------------------------------*)
  (* Booleans                                                             *)
  (*----------------------------------------------------------------------*)

  val bool_info = Option.valOf (TypeBase.read {Thy="min", Tyop = "bool"});
  val bool_size_info = (bool_size_tm,TypeBasePure.ORIG bool_size_def)
  val ty = mk_vartype "'type"
  val tm = mk_vartype "'term"
  val lift_bool_var = mk_var("boolSyntax.lift_bool",ty --> bool --> tm)
  val bool_info' = TypeBasePure.put_lift lift_bool_var
                      (TypeBasePure.put_size bool_size_info bool_info);

  (*----------------------------------------------------------------------*)
  (* Products                                                             *)
  (*----------------------------------------------------------------------*)

  val prod_size_info = (pair_size_tm,TypeBasePure.ORIG pair_size_def)
  val prod_info' = TypeBasePure.put_size prod_size_info
                     (Option.valOf (TypeBase.read {Tyop="prod", Thy="pair"}))

  (*----------------------------------------------------------------------*)
  (* Sums                                                                 *)
  (*----------------------------------------------------------------------*)

  val sum_size_info = (sum_size_tm,TypeBasePure.ORIG sum_size_def)
  val sum_info' = TypeBasePure.put_size sum_size_info
                    (Option.valOf(TypeBase.read {Tyop="sum", Thy="sum"}));

  (*----------------------------------------------------------------------*)
  (* Unit type                                                            *)
  (*----------------------------------------------------------------------*)

  val one_info = Option.valOf (TypeBase.read {Tyop="one",Thy="one"})
  val one_size_info = (one_size_tm,TypeBasePure.ORIG one_size_def)
  val ty = mk_vartype "'type"
  val tm = mk_vartype "'term"
  val lift_one_var = mk_var("oneSyntax.lift_one", ty --> oneSyntax.one_ty --> tm)
  val one_info' = TypeBasePure.put_lift lift_one_var
                     (TypeBasePure.put_size one_size_info one_info)

  (*----------------------------------------------------------------------*)
  (* Options                                                              *)
  (*----------------------------------------------------------------------*)

  val option_info = Option.valOf (TypeBase.read {Tyop="option", Thy="option"})
  val option_size_info = (option_size_tm,TypeBasePure.ORIG option_size_def)
  val option_info' = TypeBasePure.put_size option_size_info option_info

in
   val _ = TypeBase.write [bool_info']
   val _ = TypeBase.write [prod_info']
   val _ = TypeBase.write [sum_info']
   val _ = TypeBase.write [one_info']
   val _ = TypeBase.write [option_info']
end

end
