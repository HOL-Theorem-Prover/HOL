structure ringLib :> ringLib =
struct

(*
  app load ["ringNormTheory", "quote", "computeLib"];
*)

open HolKernel Parse boolLib prelimTheory quoteTheory quote computeLib;

infix ORELSE THEN THENL THENC o |->;
infixr -->;

fun RING_ERR function message =
    HOL_ERR{origin_structure = "ringLib",
		      origin_function = function,
		      message = message};


(* reify ring expressions: building a signature, which is the correspondence
   between the semantic level operators and the syntactic level ones. *)

fun ring_field q =
  rhs(concl(REWRITE_CONV[ringTheory.ring_accessors] (--q--)));

fun sring_field q =
  rhs(concl(REWRITE_CONV[semi_ringTheory.semi_ring_accessors] (--q--)));

fun inst_ty ty = inst [alpha |-> ty];
local fun pmc s = prim_mk_const {Name = s, Thy = "ringNorm"}
      fun canon_pmc s = prim_mk_const {Name = s, Thy = "canonical"}
      val pvar = pmc "Pvar"
      val pcst = pmc "Pconst"
      val pplus = pmc "Pplus"
      val pmult = pmc "Pmult"
      val popp = pmc "Popp"
      val spvar = canon_pmc "SPvar"
      val spcst = canon_pmc "SPconst"
      val spplus = canon_pmc "SPplus"
      val spmult = canon_pmc "SPmult"
in
fun polynom_sign ty ring =
  let val [P,M,N] = map ring_field [`RP ^ring`,`RM ^ring`,`RN ^ring`] in
  { Vars=inst_ty ty pvar,
    Csts=inst_ty ty pcst,
    Op1=[(N,inst_ty ty popp)],
    Op2=[(P,inst_ty ty pplus),(M,inst_ty ty pmult)] }
  end

fun spolynom_sign ty sring =
  let val [P,M] = map sring_field [`SRP ^sring`,`SRM ^sring`] in
  { Vars=inst_ty ty spvar,
    Csts=inst_ty ty spcst,
    Op1=[],
    Op2=[(P,inst_ty ty spplus), (M,inst_ty ty spmult)] }
  end
end;



(* Get the type of (semi-)ring values from the correctness lemma *)
val find_type =
  snd o dom_rng o snd o dom_rng o snd o dest_const o
    fst o strip_comb o rhs o snd o strip_forall o concl;

fun is_ring_thm th =
  let val (Rator,Rand) = dest_comb (concl th) in
  case dest_thy_const Rator of
    {Name="is_ring",Thy="ring",...} => true
  | {Name="is_semi_ring", Thy="semi_ring",...} => false
  | _ => raise RING_ERR "" ""
  end
  handle HOL_ERR _ => raise RING_ERR "is_ring" "mal-formed thm"
;

(* name is a prefix for the new constant names. *)
fun import_ring name th =
  let val ring = rand (concl th)
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
	    Rename = fn s => SOME(name^"_"^s) }
  in LIST_CONJ
    [ th,
      GSYM polynom_simplify_ok,
      LIST_CONJ [ interp_p_def, varmap_find_def ],
      LIST_CONJ
       	[ canonical_sum_merge_def, monom_insert_def,
	  varlist_insert_def, canonical_sum_scalar_def,
	  canonical_sum_scalar2_def, canonical_sum_scalar3_def,
	  canonical_sum_prod_def, canonical_sum_simplify_def,
	  ivl_aux_def, interp_vl_def, interp_m_def, ics_aux_def, interp_cs_def,
	  polynom_normalize_def, polynom_simplify_def ] ]
  end;

fun import_semi_ring name th =
  let val sring = rand (concl th)
      val { ics_aux_def, interp_cs_def, interp_m_def, interp_vl_def,
	    ivl_aux_def, interp_sp_def,
	    canonical_sum_merge_def, monom_insert_def,
	    varlist_insert_def, canonical_sum_scalar_def,
	    canonical_sum_scalar2_def, canonical_sum_scalar3_def,
	    canonical_sum_prod_def, canonical_sum_simplify_def,
	    spolynom_normalize_def, spolynom_simplify_def,
	    spolynomial_simplify_ok, ... } =
	canonicalTheory.IMPORT
	  { Vals = [sring],
	    Inst = [th],
	    Rule = REWRITE_RULE[semi_ringTheory.semi_ring_accessors ],
	    Rename = fn s => SOME(name^"_"^s) }
  in LIST_CONJ
    [ th,
      GSYM spolynomial_simplify_ok,
      LIST_CONJ [ interp_sp_def, varmap_find_def ],
      LIST_CONJ
       	[ canonical_sum_merge_def, monom_insert_def,
	  varlist_insert_def, canonical_sum_scalar_def,
	  canonical_sum_scalar2_def, canonical_sum_scalar3_def,
	  canonical_sum_prod_def, canonical_sum_simplify_def,
	  ivl_aux_def, interp_vl_def, interp_m_def, ics_aux_def, interp_cs_def,
	  spolynom_normalize_def, spolynom_simplify_def ] ]
  end;

fun mk_ring_thm nm th =
  let val b = is_ring_thm th in
  (if b then import_ring nm th else import_semi_ring nm th)
  handle HOL_ERR _ =>
    raise RING_ERR "mk_ring_thm" "Error while importing ring definitions"
  end;
(*
mk_ring_thm "int" (ASSUME(--`is_ring(ring int_0 int_1 $+ $* $~)`--))
mk_ring_thm "num"
  (ASSUME(--`is_semi_ring (semi_ring 0 1 $+ $* :num semi_ring)`--))
*)

fun store_ring {Name, Theory} =
  let val thm_nm = Name^"_ring_thms"
      val ring_thm = mk_ring_thm Name Theory in
  save_thm(thm_nm, ring_thm)
  end;


fun dest_ring_thm thm =
  (case CONJ_LIST 4 thm of
    [th1,th2,th3,th4] =>
      let val ring = rand (concl th1)
   	  val ty = find_type th2
      	  val sign =
	    if is_ring_thm th1 then polynom_sign ty ring
	    else spolynom_sign ty ring in
      {Ty=ty,OpSign=sign,SoundThm=th2,LhsThm=th3,RhsThm=th4}
      end
  | _ => raise RING_ERR "" "")
  handle HOL_ERR _ => raise RING_ERR "dest_ring_thm" "ill-formed ring thm";



(* Building and storing the conversions *)

val initial_thms =
  map lazyfy_thm [ COND_CLAUSES, AND_CLAUSES, NOT_CLAUSES, compare_def ];


val lib_thms =
  [ list_compare_def, index_compare_def, list_merge_def,
    index_lt_def, ordering_eq_dec ];


fun comp_rws cst_rws lhs_thms rhs_thms =
  let val rw_lhs = new_compset lhs_thms
      val rw_rhs = new_compset initial_thms
      val _ = add_thms (rhs_thms@lhs_thms@lib_thms@cst_rws) rw_rhs in
  (rw_lhs, rw_rhs)
  end;

fun binop_eq ty =
  let val eq = inst [alpha  |-> ty] boolSyntax.equality
      fun mk_eq th1 th2 =
        CONV_RULE(RAND_CONV(REWRITE_CONV []))
          (MK_COMB(AP_TERM eq th1, th2))
  in mk_eq
  end;

(* Ring Database *)
type convs = { NormConv : conv, EqConv : conv,
 	       Reify : term list -> {Metamap : term, Poly : term list} }

val no_such_ring = RING_ERR "" "No ring declared on that type"

val rings = 
  ref (Redblackmap.mkDict Type.compare) : (hol_type, convs) Redblackmap.dict ref; 

fun add_ring ty rng = 
  rings := Redblackmap.insert (!rings, ty,rng);

fun RING_NORM_CONV tm = #NormConv (Redblackmap.find (!rings, type_of tm)) tm;
fun RING_CONV tm      = #EqConv (Redblackmap.find (!rings, #3 (dest_eq_ty tm))) tm;
fun reify tml         = #Reify (Redblackmap.find (!rings, type_of (hd tml))) tml;


fun declare_ring {RingThm,IsConst,Rewrites} =
  let val {Ty,OpSign,SoundThm,LhsThm,RhsThm} = dest_ring_thm RingThm
      val reify_fun = meta_expr Ty IsConst OpSign
      val (lhs_rws,rhs_rws) =
 	comp_rws Rewrites (CONJUNCTS LhsThm) (CONJUNCTS RhsThm)
      val simp_rule =
	CONV_RULE(CBV_CONV lhs_rws THENC RAND_CONV (CBV_CONV rhs_rws))
      val mk_eq = binop_eq Ty

      fun norm_conv t =
        let val {Metamap,Poly=[p]} = reify_fun [t]
            val thm = SPECL[Metamap,p] SoundThm
  	in simp_rule thm
  	end
        handle HOL_ERR _ => raise RING_ERR "norm_conv" ""

      fun eq_conv t =
  	let val (lhs,rhs) = dest_eq t
            val {Metamap,Poly=[p1,p2]} = reify_fun [lhs,rhs]
	    val mthm = SPEC Metamap SoundThm
            val th1 = simp_rule (SPEC p1 mthm)
            val th2 = simp_rule (SPEC p2 mthm)
  	in mk_eq th1 th2
	end
        handle HOL_ERR _ => raise RING_ERR "eq_conv" ""

  in add_ring Ty { NormConv=norm_conv, EqConv=eq_conv, Reify=reify_fun }
  end;

end;
