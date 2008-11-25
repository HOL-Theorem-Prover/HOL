structure stringLib :> stringLib =
struct

open HolKernel boolLib numSyntax reduceLib
     stringTheory stringSyntax;

val ERR = mk_HOL_ERR "stringLib";


(*---------------------------------------------------------------------------
     Conversions.
 ---------------------------------------------------------------------------*)

local val bound = mk_numeral(Arbnum.fromInt 256)
      fun cond m = EQT_ELIM(REDUCE_CONV (mk_less(m,bound)))
in
fun lemma m = EQ_MP (SPEC m ORD_CHR) (cond m)
end;

val ORD_CHR_CONV = lemma o dest_chr o dest_ord;

val char_eq_thms   = [CHR_ORD,CHAR_EQ_THM,ORD_11];

val char_EQ_CONV =
 let open computeLib reduceLib boolTheory
     val compset = num_compset ()
     val _ = add_conv (ord_tm, 1, ORD_CHR_CONV) compset
     val _ = add_thms char_eq_thms compset
     val conv = CBV_CONV compset
     val REFL_CLAUSE_char = INST_TYPE [alpha |-> char_ty] REFL_CLAUSE
     val is_char_lit = Lib.can fromHOLchar
 in
   fn tm =>
    case total dest_eq tm
     of NONE => raise ERR "char_EQ_CONV" "not a char equality"
      | SOME(c1,c2) =>
          if is_char_lit c1 andalso is_char_lit c2
          then if c1=c2 then SPEC c1 REFL_CLAUSE_char else conv tm
          else raise ERR "char_EQ_CONV" "not a char equality"
 end;


val string_EQ_CONV =
 let open computeLib reduceLib boolTheory
     val compset = listLib.list_compset ()
     val _ = add_conv (ord_tm, 1, ORD_CHR_CONV) compset
     val _ = add_thms char_eq_thms compset
     val conv = CBV_CONV compset
     val REFL_CLAUSE_string = INST_TYPE [alpha |-> string_ty] REFL_CLAUSE
 in
   fn tm =>
    case total dest_eq tm
     of NONE => raise ERR "string_EQ_CONV" "not a string equality"
      | SOME(s1,s2) =>
          if is_string_literal s1 andalso is_string_literal s2
          then if s1=s2 then SPEC s1 REFL_CLAUSE_string else conv tm
          else raise ERR "string_EQ_CONV" "not a string equality"
 end;

val string_rewrites = [EXPLODE_EQNS, IMPLODE_EQNS]

val _ = computeLib.add_funs string_rewrites;
val _ = computeLib.add_convs [(ord_tm, 1, ORD_CHR_CONV)];

val _ = Defn.const_eq_ref :=
          (!Defn.const_eq_ref ORELSEC char_EQ_CONV ORELSEC string_EQ_CONV);

(*---------------------------------------------------------------------------
      Examples.

  val test = Count.apply (string_EQ_CONV o Term);

  test`"" = ""`;
  test`"a" = ""`;
  test`"" = "a"`;
  test`"" = "abc"`;
  test`"abcdefghijklmnopqrstuvwxyz" = "abcdefghijklmnopqrstuvwxyz"`;
  test`"abcdefghijklmnopqrstuvwxyz" = "abcdefghijklmnopqrstuvwxyzA"`;


 ---------------------------------------------------------------------------*)

end
