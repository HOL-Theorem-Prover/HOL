open HolKernel Drule Conv
open Exception

fun ERR f msg = HOL_ERR {origin_structure = "Prim_rec_Compat",
                         origin_function = f, message = msg};

fun old2new thm = let
  (* thm of form !f1.. fn.  ?! f.   .... *)
  val LIST_MK_FORALL = C (foldr (uncurry FORALL_EQ))
  val fvs = #1 (strip_forall (concl thm))
  val thm' = SPEC_ALL thm
  val thm'' = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV thm')
in
  LIST_MK_FORALL fvs thm''
end

val old_style_to_new = old2new

fun prove_constructors_one_one thm0 = let
  val thm = old2new thm0
in
  valOf (hd (Prim_rec.prove_constructors_one_one thm))
  handle Option.Option =>
    raise ERR "prove_constructors_one_one" "No constructor has arguments"
end

fun prove_constructors_distinct thm0 = let
  val thm = old2new thm0
in
  valOf (hd (Prim_rec.prove_constructors_distinct thm))
  handle Option.Option =>
    raise ERR "prove_constructors_distinct" "Only one constructor to type"
end

fun prove_cases_thm thm = hd (Prim_rec.prove_cases_thm thm)
