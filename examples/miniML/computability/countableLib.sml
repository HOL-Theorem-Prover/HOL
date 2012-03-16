open HolKernel pred_setTheory countableTheory lcsymtacs numSyntax pairSyntax

fun count_datatype ty = let
  val axiom = TypeBase.axiom_of ty
  val (name,args) = dest_type ty
  val count_name = "count_"^name
  val count_name_aux = count_name^"_aux"
  val count_ty_tm = mk_var(count_name,ty --> num)
  val helpers = map (fn a => genvar(a --> num)) args
  val count_ty_aux_tm = mk_var(count_name_aux, foldl (fn (h,ty) => type_of h --> ty) (ty --> num) helpers)
  val lhs0 = list_mk_comb (count_ty_aux_tm, helpers)
  val constructors = TypeBase.constructors_of ty
  fun args cty = let
    val (d,r) = dom_rng cty
  in genvar d :: args r end handle HOL_ERR _ => []
  fun counter t = if t = ty then lhs0 else
    Lib.first (fn h => fst(dom_rng(type_of h)) = t) helpers
  val count_num2 = ``count_num2``
  fun count_args [] = term_of_int 0
    | count_args [a] = mk_comb(counter (type_of a), a)
    | count_args (a::xs) = mk_comb(count_num2,mk_pair(mk_comb(counter (type_of a), a),count_args xs))
  fun mk_eqn (c,(n,eqs)) = let
    val ars = args (type_of c)
    val lhs = mk_comb(lhs0, list_mk_comb (c,ars))
    val rhs = mk_comb(count_num2,mk_pair(term_of_int n,count_args ars))
    val eq = mk_eq (lhs, rhs)
    in (n+1,eq::eqs) end
  val (n,eqs) = foldl mk_eqn (0,[]) constructors
  val count_ty_aux_def = new_recursive_definition
                         {name=count_name_aux, rec_axiom=axiom,
                          def=list_mk_conj eqs}
in (count_ty_aux_def) end

val count_list_aux_def = count_datatype ``:α list``

val list_countable = store_thm(
"list_countable",
``countable (UNIV:α set) ⇒ countable (UNIV:α list set)``,
rw[countable_def] >>
qexists_tac `count_list_aux f` >>
fs[INJ_DEF] >>
Induct >| [qx_gen_tac`y`,gen_tac >> qx_gen_tac`y`] >>
rw[count_list_aux_def] >>
ASSUME_TAC INJ_count_num2 >>
Cases_on`y`>>fs[count_list_aux_def,INJ_DEF] >>
res_tac >> fs[] >>
res_tac >> fs[])

val count_list_def = Define`
  count_list = @f. INJ f (UNIV:α list set) (UNIV:num set)`

val INJ_count_list = store_thm(
"INJ_count_list",
``countable (UNIV:α set) ⇒ INJ count_list (UNIV:α list set) UNIV``,
rw[count_list_def] >>
SELECT_ELIM_TAC >> rw[] >>
metis_tac [list_countable,countable_def])

open MiniMLTheory
val count_error_aux_def = count_datatype ``:error``

(*
val exp_countable = store_thm(
"exp_countable",
``countable (UNIV:exp set)``

val count_v_def = Define`
  (count_v (Lit l) = count_num2 (0, count_lit l))
∧ (count_v (Conv cn vs) = count_num2 (1, count_num2(count_option cn, count_list count

val v_countable = store_thm(
"v_countable",
``countable (UNIV:v set)``,
rw[countable_def,INJ_DEF] >>
qexists_tac `λv. case v of
                 | Lit l => count_num2 (0,count_lit l)
                 | Conv cn vs => count_num2 (1,count_num2(count_option cn, count_list vs))
                 | Closure e n b => count_num2 (2,count_num2(count_list e,count_num2(count_string n,count_exp b)))
                 | Recclosure
*)
