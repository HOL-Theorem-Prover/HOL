(*---------------------------------------------------------------------------*
 * Setting information for types.                                            *
 *                                                                           *
 * Here we fill in the "size" entries in theTypeBase for some types that     *
 * are non-recursive and built before numbers. Also add some lifters.        *
 *---------------------------------------------------------------------------*)

structure NonRecSize =
struct

local open pairTheory sumTheory optionTheory arithmeticTheory in end;

local
  open HolKernel boolLib Parse pairSyntax numSyntax

  (*----------------------------------------------------------------------*)
  (* Booleans                                                             *)
  (*----------------------------------------------------------------------*)

  val bool_info = Option.valOf (TypeBase.read {Thy="min", Tyop = "bool"});
  val bool_size_info = (mk_abs(mk_var("b",bool),zero_tm),
                        TypeBasePure.ORIG boolTheory.REFL_CLAUSE)
  val ty = mk_vartype "'type"
  val tm = mk_vartype "'term"
  val lift_bool_var = mk_var("boolSyntax.lift_bool",ty --> bool --> tm)
  val bool_info' = TypeBasePure.put_lift lift_bool_var
                      (TypeBasePure.put_size bool_size_info bool_info);

  (*----------------------------------------------------------------------*)
  (* Products                                                             *)
  (*----------------------------------------------------------------------*)

  val prod_size_info =
    (let val f = mk_var("f", alpha --> num)
         val g = mk_var("g", beta --> num)
         val x = mk_var("x", alpha)
         val y = mk_var("y", beta)
     in list_mk_abs([f,g],
          mk_pabs(mk_pair(x,y),mk_plus(mk_comb(f,x),mk_comb(g,y))))
     end,
     TypeBasePure.ORIG pairTheory.UNCURRY_DEF)

  val prod_info' = TypeBasePure.put_size prod_size_info
                     (Option.valOf (TypeBase.read {Tyop="prod", Thy="pair"}))

  (*----------------------------------------------------------------------*)
  (* Sums                                                                 *)
  (*----------------------------------------------------------------------*)

  val sum_info = Option.valOf(TypeBase.read {Tyop="sum", Thy="sum"});
  val sum_case = prim_mk_const{Name="sum_case", Thy="sum"}
  val num = numSyntax.num
  val sum_case_into_num = inst [alpha |-> num] sum_case
  val f = mk_var("f",beta --> num)
  val g = mk_var("g",gamma --> num)
  val s = mk_var("s",mk_thy_type{Tyop="sum",Thy="sum",Args=[beta, gamma]})
  val tm = list_mk_abs ([f,g,s], list_mk_comb(sum_case_into_num,[f,g,s]))
  val sum_size_info = (tm,TypeBasePure.ORIG sumTheory.sum_case_def)
  val sum_info' = TypeBasePure.put_size sum_size_info sum_info

  (*----------------------------------------------------------------------*)
  (* Unit type                                                            *)
  (*----------------------------------------------------------------------*)

  val one_info = Option.valOf (TypeBase.read {Tyop="one",Thy="one"})
  val one_size_info = (rator(oneSyntax.mk_one_case zero_tm),
                        TypeBasePure.ORIG oneTheory.one_case_rw)
  val ty = mk_vartype "'type"
  val tm = mk_vartype "'term"
  val lift_one_var = mk_var("oneSyntax.lift_one", ty --> oneSyntax.one_ty --> tm)
  val one_info' = TypeBasePure.put_lift lift_one_var
                     (TypeBasePure.put_size one_size_info one_info)

  (*----------------------------------------------------------------------*)
  (* Options                                                              *)
  (*----------------------------------------------------------------------*)

  val option_info = Option.valOf (TypeBase.read {Tyop="option", Thy="option"})
  val option_case_tm = prim_mk_const{Name="option_case",Thy="option"}
  val option_size_info =
       (let val f = mk_var("f",alpha --> num)
            val x = mk_var("x",alpha)
        in mk_abs(f,list_mk_comb(inst [beta|->num] option_case_tm,
                    [zero_tm,mk_abs(x,mk_suc(mk_comb(f,x)))]))
        end,
        TypeBasePure.ORIG optionTheory.option_case_def)
  val option_info' = TypeBasePure.put_size option_size_info option_info

in
   val _ = TypeBase.write [bool_info']
   val _ = TypeBase.write [prod_info']
   val _ = TypeBase.write [sum_info']
   val _ = TypeBase.write [one_info']
   val _ = TypeBase.write [option_info']
end

end
