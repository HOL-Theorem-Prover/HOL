(*---------------------------------------------------------------------------*
 * Setting information for types.                                            *
 *                                                                           *
 * Here we fill in the "size" entries in theTypeBase for some types that     *
 * are non-recursive and built before numbers.                               *
 *---------------------------------------------------------------------------*)

structure NonRecSize =
struct



local
  open HolKernel boolLib Parse Rsyntax

  val (Type,Term) = parse_from_grammars arithmeticTheory.arithmetic_grammars
  fun -- q x = Term q
  fun == q x = Type q

  local open pairTheory sumTheory optionTheory arithmeticTheory in
  end;

  infix THEN THENC THENL |-> ORELSE;
  infixr -->;
  val prod_size_info =
    (Term`\f g. UNCURRY(\(x:'a) (y:'b). f x + g y)`,
     TypeBase.ORIG pairTheory.UNCURRY_DEF)
  val prod_info' =
    TypeBase.put_size prod_size_info
    (Option.valOf(TypeBase.read"prod"))

  val bool_info = Option.valOf(TypeBase.read "bool")
  val bool_case_rw = prove(Term`!x y. bool_case x x y = (x:'a)`,
    REPEAT GEN_TAC
      THEN BOOL_CASES_TAC (Term`y:bool`)
     THEN Rewrite.ASM_REWRITE_TAC[boolTheory.bool_case_DEF]);
  val bool_size_info = (Term`bool_case 0 0`, TypeBase.ORIG bool_case_rw)
  val bool_info' = TypeBase.put_size bool_size_info bool_info

  val sum_info = Option.valOf(TypeBase.read "sum")
  val sum_case = Term`sum$sum_case`
  val num = numSyntax.num_ty
  val sum_case_into_num = Rsyntax.inst [alpha |-> num] sum_case
  val f = mk_var{Name="f",Ty=beta-->num}
  val g = mk_var{Name="g",Ty=mk_vartype"'c" --> num}
  val s = mk_var{Name="s",Ty=mk_type{Tyop="sum",Args=[beta, mk_vartype "'c"]}}
  val tm = list_mk_abs ([f,g,s], list_mk_comb(sum_case_into_num,[f,g,s]))
  val sum_size_info = (tm,TypeBase.ORIG sumTheory.sum_case_def)
  val sum_info' = TypeBase.put_size sum_size_info sum_info

  val option_info = Option.valOf(TypeBase.read "option")
  val option_size_info =
       (Term`\f. option_case 0 (\x:'a. SUC (f x))`,
        TypeBase.ORIG optionTheory.option_case_def)
  val option_info' = TypeBase.put_size option_size_info option_info

in
   val _ = TypeBase.write bool_info'
   val _ = TypeBase.write prod_info'
   val _ = TypeBase.write option_info'
   val _ = TypeBase.write sum_info'
end

end;
