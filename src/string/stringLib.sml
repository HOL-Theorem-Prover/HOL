structure stringLib :> stringLib =
struct

open HolKernel boolLib numSyntax reduceLib stringTheory stringSyntax;

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

val char_thms   = [CHR_ORD,CHAR_EQ_THM,ORD_11];
val string_thms = STRING_11::STRING_DISTINCT::char_thms


val char_EQ_CONV = 
   let open computeLib reduceLib
       val compset = num_compset ()
       val _ = add_conv (ord_tm, 1, ORD_CHR_CONV) compset
       val _ = add_thms char_thms compset
   in 
      CBV_CONV compset
   end;


val string_EQ_CONV = 
   let open computeLib reduceLib
       val compset = num_compset ()
       val _ = add_conv (ord_tm, 1, ORD_CHR_CONV) compset
       val _ = add_thms string_thms compset
   in 
      CBV_CONV compset
   end;


val _ = computeLib.add_funs string_thms;
val _ = computeLib.add_convs [(ord_tm, 1, ORD_CHR_CONV)];

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
