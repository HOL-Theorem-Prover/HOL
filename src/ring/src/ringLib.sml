(*
load "ringNormTheory";
load "quote";
load "computeLib";
*)
local open HolKernel Parse basicHol90Lib prelimTheory quoteTheory
           quote computeLib
in

infix ORELSE THEN THENL THENC o |->;


fun RING_ERR function message =
    HOL_ERR{origin_structure = "ringLib",
		      origin_function = function,
		      message = message};


(* reify ring expressions *)


fun inst_ty ty = inst [==`:'a`== |-> ty];
local val pvar = (--`Pvar`--)
      val pcst = (--`Pconst`--)
      val pplus = (--`Pplus`--)
      val pmult = (--`Pmult`--)
      val popp = (--`Popp`--)
in
fun polynom_cst ty =
  { Vars=inst_ty ty pvar,
    Csts=inst_ty ty pcst,
    Plus=inst_ty ty pplus,
    Mult=inst_ty ty pmult,
    Opp=inst_ty ty popp }
end;
local val pvar = (--`SPvar`--)
      val pcst = (--`SPconst`--)
      val pplus = (--`SPplus`--)
      val pmult = (--`SPmult`--)
in
fun spolynom_cst ty =
  { Vars=inst_ty ty pvar,
    Csts=inst_ty ty pcst,
    Plus=inst_ty ty pplus,
    Mult=inst_ty ty pmult }
end;


fun ring_field q = 
  rhs(concl(REWRITE_CONV[ringTheory.ring_accessors] (--q--)));

fun hring_field q = 
  rhs(concl(REWRITE_CONV[semi_ringTheory.semi_ring_accessors] (--q--)));

(* name is a prefix for the new constant names. *)
fun import_ring name ty ring th =
  let val [P,M,N] = map ring_field [`RP ^ring`,`RM ^ring`,`RN ^ring`]
      val {Vars,Csts,Plus,Mult,Opp} = polynom_cst ty
      val { ics_aux_def, interp_cs_def, interp_m_def, interp_vl_def,
	    ivl_aux_def, interp_p_def,
	    canonical_sum_merge_def, monom_insert_def,
	    varlist_insert_def, canonical_sum_scalar_def,
	    canonical_sum_scalar2_def, canonical_sum_scalar3_def,
	    canonical_sum_prod_def, canonical_sum_simplify_def,
	    polynom_normalize_def, polynom_simplify_def,
	    polynom_simplify_ok,... } =
	ringNormTheory.IMPORT
	  { Vals = [ring],
	    Inst = [th],
	    Rule = REWRITE_RULE[ringTheory.ring_accessors ],
	    Rename = fn s => SOME(name^s) }
  in { Ty=ty,
       Thm = GSYM polynom_simplify_ok,
       LhsThm = [ interp_p_def, varmap_find_def ],
       RhsThm =
       [ canonical_sum_merge_def, monom_insert_def,
	 varlist_insert_def, canonical_sum_scalar_def,
	 canonical_sum_scalar2_def, canonical_sum_scalar3_def,
	 canonical_sum_prod_def, canonical_sum_simplify_def,
	 ivl_aux_def, interp_vl_def, interp_m_def, ics_aux_def, interp_cs_def,
	 polynom_normalize_def, polynom_simplify_def ],
       Meta = { Vars=Vars, Csts=Csts, Op1=[(N,Opp)], Op2=[(P,Plus),(M,Mult)] }
     }
  end
;
(* (without instantiation of ringNormTheory, less efficient!)
local open ringNormTheory in
fun import_ring ty ring th =
  let val [P,M,N] = map ring_field [`RP ^ring`,`RM ^ring`,`RN ^ring`]
      val {Vars,Csts,Plus,Mult,Opp} = polynom_cst ty
  in { Ty=ty,
       Thm = GSYM (MATCH_MP polynom_simplify_ok th),
       LhsThm =
       [ interp_p_def, interp_var_def, varmap_find_def,
	 ringTheory.ring_accessors ],
       RhsThm =
       [ canonical_sum_merge_def, monom_insert_def,
	 varlist_insert_def, canonical_sum_scalar_def,
	 canonical_sum_scalar2_def, canonical_sum_scalar3_def,
	 canonical_sum_prod_def, canonical_sum_simplify_def,
	 ivl_aux_def, interp_vl_def, interp_m_def, ics_aux_def,
	 interp_cs_def, polynom_normalize_def,
	 polynom_simplify_def ],
       Vars=Vars,
       Csts=Csts,
       Op1=[(N,Opp)],
       Op2=[(P,Plus), (M,Mult)] }
  end
end;
*)
fun import_semi_ring name ty hring th =
  let val [P,M] = map hring_field [`SRP ^hring`,`SRM ^hring`]
      val {Vars,Csts,Plus,Mult} = spolynom_cst ty
      val { ics_aux_def, interp_cs_def, interp_m_def, interp_vl_def,
	    ivl_aux_def, interp_sp_def,
	    canonical_sum_merge_def, monom_insert_def,
	    varlist_insert_def, canonical_sum_scalar_def,
	    canonical_sum_scalar2_def, canonical_sum_scalar3_def,
	    canonical_sum_prod_def, canonical_sum_simplify_def,
	    spolynom_normalize_def, spolynom_simplify_def,
	    spolynomial_simplify_ok, ... } =
	canonicalTheory.IMPORT
	  { Vals = [hring],
	    Inst = [th],
	    Rule = REWRITE_RULE[semi_ringTheory.semi_ring_accessors ],
	    Rename = fn s => SOME(name^s) }
  in { Ty=ty,
       Thm = GSYM spolynomial_simplify_ok,
       LhsThm =
       [ interp_sp_def, varmap_find_def ],
       RhsThm =
       [ canonical_sum_merge_def, monom_insert_def,
	 varlist_insert_def, canonical_sum_scalar_def,
	 canonical_sum_scalar2_def, canonical_sum_scalar3_def,
	 canonical_sum_prod_def, canonical_sum_simplify_def,
	 ivl_aux_def, interp_vl_def, interp_m_def, ics_aux_def, interp_cs_def,
	 spolynom_normalize_def, spolynom_simplify_def ],
       Meta = { Vars=Vars, Csts=Csts, Op1=[], Op2=[(P,Plus), (M,Mult)] }
     } 
  end
;

(* TODO: find a prefix name, instead of toto titi! *)
fun dest_ring th =
  let val {Rator,Rand} = dest_comb (concl th)
      val {Name=c,Ty} = dest_const Rator in
  (case (c, dest_type (fst (dom_rng Ty))) of
    ("is_ring", {Tyop="ring", Args=[ty]}) =>
      import_ring "toto_" ty Rand th 
  | ("is_semi_ring", {Tyop="semi_ring", Args=[ty]}) =>
      import_semi_ring "titi_" ty Rand th
  | _ => raise RING_ERR "" "")
  handle HOL_ERR _ => raise RING_ERR "dest_ring" "mal-formed thm"
  end
;
(*
dest_ring(ASSUME(--`is_ring(ring int_0 int_1 $+_ $*_ --)`--))
dest_ring(ASSUME(--`is_semi_ring(semi_ring 0 1 $+ $* )`--))
*)


val initial_thms = [ COND_CLAUSES, AND_CLAUSES, NOT_CLAUSES, compare_def ];


val lib_thms =
  [ list_compare_def, index_compare_def, list_merge_def,
    index_lt_def, ordering_eq_dec ];


fun comp_rws cst_rws lhs_thms rhs_thms =
  let val rw_lhs = from_list (true,lhs_thms)
      val rw_rhs = from_list (false,initial_thms)
      val _ = add_thms (true, cst_rws@lhs_thms@lib_thms@rhs_thms) rw_rhs in
  (rw_lhs, rw_rhs)
  end;

fun binop_eq ty =
  let val eq = inst_ty ty (--`$=`--)
      fun mk_eq th1 th2 =
        CONV_RULE(RAND_CONV(REWRITE_CONV []))
          (MK_COMB(AP_TERM eq th1, th2))
  in mk_eq
  end;


fun compile_ring_infos { Theory=thm, Const=is_cst, Rewrites=rws } =
  let val ring_elts = dest_ring thm
      val reify_fun = meta_expr (#Ty ring_elts) is_cst (#Meta ring_elts)
      val (lhs_rws,rhs_rws) =
 	comp_rws rws (#LhsThm ring_elts) (#RhsThm ring_elts)
      val simp_rule =
	CONV_RULE(CBV_CONV lhs_rws THENC RAND_CONV (CBV_CONV rhs_rws))
      val mk_eq = binop_eq (#Ty ring_elts)
  in
  { Reify_fun=reify_fun,
    Ring_rule=simp_rule,
    Thm= #Thm ring_elts,
    Ty= #Ty ring_elts,
    Mk_eq=mk_eq }
  end;


(* This function builds conversions to normalize expressions and equations of
 * the ring components given as argument.
 *)
fun declare_ring ring =
  let val {Reify_fun, Ring_rule, Thm, Ty, Mk_eq} = compile_ring_infos ring

      fun norm_conv t =
        let val _ =
	      if type_of t = Ty then ()
	      else raise RING_ERR "norm_conv" "wrong type"
	    val {Metamap,Poly=[p]} = Reify_fun [t]
            val thm = SPECL[Metamap,p] Thm
  	in Ring_rule thm
  	end

      fun eq_conv t = 
  	let val {lhs,rhs,ty} = dest_eq_ty t 
            val _ =
	      if ty = Ty then ()
	      else raise RING_ERR "ring_conv" "wrong type"  
	    val {Metamap,Poly=[p1,p2]} = Reify_fun [lhs,rhs]
	    val mthm = SPEC Metamap Thm
            val th1 = Ring_rule (SPEC p1 mthm)
            val th2 = Ring_rule (SPEC p2 mthm)
  	in Mk_eq th1 th2
	end

  in { NormConv=norm_conv, EqConv=eq_conv, Reify=Reify_fun }
  end
;

end;
