open HolKernel Drule Conv
open Exception

fun ERR f msg = HOL_ERR {origin_structure = "Prim_rec_Compat",
                         origin_function = f, message = msg};

(* old style list axiom:
     |- !x f. ?!fn1. (fn1 [] = x) /\ !h t. fn1 (h::t) = f (fn1 t) h t
   new style list axiom:
     |- !f0 f1. ?fn. (fn [] = f0) /\ !a0 a1. fn (a0::a1) = f1 a0 a1 (fn a1)

   In addition to turning the ?! into an ?, we need to switch the arguments
   on the RHS of each equation around so that the recursive calls come last
*)

fun EUE_RULE thm = CONJUNCT1 (CONV_RULE EXISTS_UNIQUE_CONV thm)


fun old2new thm = let
  val (uvs, ubody) = strip_forall (concl thm)
  val {Rator, Rand} = dest_comb ubody
  val _ = #Name (dest_const Rator) = "?!" orelse
    raise ERR "pull_old_apart" "Not a ?!"
  val eqns = strip_conj (#Body (dest_abs Rand))
  fun process tm = let
    (* take an equation and return a pair consisting of
       the head variable on the rhs, and an abstraction of the form
       \a b c ..  x y z ... . f x y z ... a b c ...
       Where f shares the name of the head variable (though not the type)
       and where the abstraction does have the same type as the head
       variable such that it swaps the recursive call arguments to be
       at the end of the list *)
    val (f, args) = strip_comb (rhs (#2 (strip_forall tm)))
    fun mysplit acc [] = (List.rev acc, [])
      | mysplit acc (all as x::xs) = if is_comb x then mysplit (x::acc) xs
                                     else (List.rev acc, all)
    val (recursive, nonrecursive) = mysplit [] args
    val rectypes = map type_of recursive
    val nonrectypes = map type_of nonrecursive
    val recgvars = map genvar rectypes
    val nonrecgvars = map genvar nonrectypes
    val new_domtys = nonrectypes @ rectypes
    val (_, rngty) = strip_fun_ty (type_of f)
    val newftype = list_mk_fun_ty (new_domtys, rngty)
    val abs = list_mk_abs (recgvars @ nonrecgvars,
                           list_mk_comb(mk_var{Name = #Name (dest_var f),
                                               Ty = newftype},
                                        nonrecgvars @ recgvars))
  in
    (f, abs)
  end
  val fabs_alist = map process eqns
  fun specfn thm =
    if is_forall (concl thm) then
      specfn
      (SPEC (Lib.assoc (#Bvar (dest_forall (concl thm))) fabs_alist) thm)
    else
      thm
in
  GEN_ALL (EUE_RULE (BETA_RULE (specfn thm)))
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
