open HolKernel pred_setTheory countableTheory lcsymtacs
open boolSyntax numSyntax pairSyntax pred_setSyntax

val count_datatype = let
  val count_num2 = ``count_num2``
  fun mk_countable a = ``countable ^(mk_univ a)``
  fun count_args ctr = let
    fun f [] = term_of_int 0
      | f [a] = mk_comb(ctr (type_of a), a)
      | f (a::xs) = mk_comb(count_num2,mk_pair(mk_comb(ctr (type_of a), a),f xs))
  in f end
  fun mk_eqn ctr lhs0 (c,(n,eqs)) = let
    val lhs = mk_comb(lhs0, c)
    val (_,ars) = strip_comb c
    val rhs = mk_comb(count_num2,mk_pair(term_of_int n,count_args ctr ars))
    val eq = mk_eq (lhs, rhs)
  in (n+1,eq::eqs) end
  fun counter0 t = raise Fail "no memocache"
in fn ty => let
  val axiom = TypeBase.axiom_of ty
  val (name,args) = dest_type ty
  val count_name = "count_"^name
  val count_ty_var = mk_var(count_name,ty --> num)
  val nchotomy = SPEC_ALL (TypeBase.nchotomy_of ty)
  val constructors = map (rhs o snd o strip_exists) (strip_disj (concl nchotomy))
in
  if args = [] then let
    val lhs0 = count_ty_var
    fun counter t = if t = ty then lhs0 else counter0 t
    val (_,eqs) = foldl (mk_eqn counter lhs0) (0,[]) constructors
    val count_ty_def = new_recursive_definition
                       {name=count_name, rec_axiom=axiom,
                        def=list_mk_conj eqs}
    val count_ty_tm = mk_const(count_name,ty --> num)
    val count_ty_inj = prove(mk_inj(count_ty_tm,mk_univ ty,mk_univ num),
      fs[INJ_DEF] >> Induct >> Cases >> fs[count_ty_def])
    val countable_ty = prove(mk_countable ty,PROVE_TAC[count_ty_inj,countable_def])
  in (count_ty_inj,countable_ty) end
  else let
    val helpers = map (fn a => genvar(a --> num)) args
    val count_name_aux = count_name^"_aux"
    val count_ty_aux_var = mk_var(count_name_aux,
          foldl (fn (h,ty) => type_of h --> ty) (ty --> num) helpers)
    val lhs0 = list_mk_comb (count_ty_aux_var, helpers)
    fun counter t = if t = ty then lhs0 else
      Lib.first (fn h => fst(dom_rng(type_of h)) = t) helpers
      handle HOL_ERR _ => counter0 t
    val (_,eqs) = foldl (mk_eqn counter lhs0) (0,[]) constructors
    val count_ty_aux_def = new_recursive_definition
                           {name=count_name_aux, rec_axiom=axiom,
                            def=list_mk_conj eqs}
    val count_ty_aux_tm = mk_const(count_name_aux, type_of count_ty_aux_var)
    val count_ty_def = new_definition (count_name, mk_eq(count_ty_var,
      mk_select(count_ty_var,mk_inj(count_ty_var,mk_univ ty,mk_univ num))))
    val count_ty_tm = mk_const(count_name,ty --> num)
    val hyps = map mk_countable args
    val count_ty_inj = prove(
      list_mk_imp(hyps,mk_inj(count_ty_tm,mk_univ ty,mk_univ num)),
      simp_tac pure_ss [countable_def,count_ty_def] >>
      foldl (fn (h,_) => disch_then (X_CHOOSE_THEN h assume_tac)) ALL_TAC helpers >>
      SELECT_ELIM_TAC >> rw[] >>
      exists_tac (list_mk_comb(count_ty_aux_tm,helpers)) >>
      fs[INJ_DEF] >>
      Induct >> rw[count_ty_aux_def] >>
      qmatch_assum_rename_tac `X = (^count_ty_aux_tm Y) y` ["X","Y"] >>
      Cases_on `y` >> fs[count_ty_aux_def])
    val countable_ty = prove(list_mk_imp(hyps,mk_countable ty),
                             PROVE_TAC[count_ty_inj,countable_def])
  in (count_ty_inj,countable_ty) end
end
end

val (count_list_inj, countable_list) = count_datatype ``:α list``

open MiniMLTheory
val (count_error_inj, countable_error) = count_datatype ``:error``

(*
val (count_lit_inj, countable_lit) = count_datatype ``:lit``
val (count_result_inj, countable_result) = count_datatype ``:α result``
val (count_exp_inj, countable_exp) = count_datatype ``:exp``
*)
