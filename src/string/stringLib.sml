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
val string_eq_thms = TypeBase.one_one_of ``:string`` ::
                     TypeBase.distinct_of ``:string`` ::
                     GSYM (TypeBase.distinct_of ``:string``) :: char_eq_thms


val dest_char_eq = (dest_chr ## dest_chr) o dest_eq;
val is_char_eq = can dest_char_eq;

val char_EQ_CONV =
   let open computeLib reduceLib
       val compset = num_compset ()
       val _ = add_conv (ord_tm, 1, ORD_CHR_CONV) compset
       val _ = add_thms char_eq_thms compset
       val conv = CBV_CONV compset
   in
     fn tm =>
     if is_char_eq tm then conv tm
     else raise ERR "char_EQ_CONV" "not a char eq"
   end;


val dest_string_eq = (fromHOLstring ## fromHOLstring) o dest_eq;
val is_string_eq = can dest_string_eq;

val string_EQ_CONV =
   let open computeLib reduceLib
       val compset = num_compset ()
       val _ = add_conv (ord_tm, 1, ORD_CHR_CONV) compset
       val _ = add_thms string_eq_thms compset
       val conv = CBV_CONV compset
   in
     fn tm =>
     if is_string_eq tm then conv tm
     else raise ERR "string_EQ_CONV" "not a string eq"
   end;

val string_rewrites = STRLEN_DEF::TypeBase.case_def_of ``:string``::
                      EXPLODE_EQNS::IMPLODE_EQNS::string_eq_thms;

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

  fun triv tm =
    let val thm = REFL (lhs tm)
    in if concl thm = tm then EQT_INTRO thm
       else string_EQ_CONV tm
    end;

  val test1 = Count.apply (triv o Term);

  test1`"" = ""`;
  test1`"a" = ""`;
  test1`"" = "a"`;
  test1`"" = "abc"`;
  test1`"abcdefghijklmnopqrstuvwxyz" = "abcdefghijklmnopqrstuvwxyz"`;
  test1`"abcdefghijklmnopqrstuvwxyz" = "abcdefghijklmnopqrstuvwxyzA"`;

  This shows that the reflexivity rewrite should be applied first, when
  dealing with equality sub-terms. How do I teach the system to apply
  it first?

 ---------------------------------------------------------------------------*)

end
