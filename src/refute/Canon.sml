structure Canon :> Canon =
struct

open HolKernel Parse boolLib liteLib AC Ho_Rewrite Abbrev tautLib;

infixr 5 |-> -->
infix THEN THENL THENC THENCQC THENQC

fun ERR x = STRUCT_ERR "Canon" x;
fun WRAP_ERR x = STRUCT_WRAP "Canon" x;

(* Fix the grammar used by this file *)
val ambient_grammars = Parse.current_grammars();
val _ = Parse.temp_set_grammars combinTheory.combin_grammars

val INST  = HolKernel.INST;
val subst = HolKernel.subst;

val conj_tm = boolSyntax.conjunction;
val disj_tm = boolSyntax.disjunction;
val false_tm = boolSyntax.F

val EXISTS_DEF           = boolTheory.EXISTS_DEF
val EXISTS_UNIQUE_DEF    = boolTheory.EXISTS_UNIQUE_DEF
val LEFT_AND_EXISTS_THM  = GSYM LEFT_EXISTS_AND_THM
val AND_FORALL_THM       = GSYM FORALL_AND_THM
val LEFT_OR_FORALL_THM   = GSYM LEFT_FORALL_OR_THM
val RIGHT_OR_FORALL_THM  = GSYM RIGHT_FORALL_OR_THM
val LEFT_IMP_FORALL_THM  = GSYM LEFT_EXISTS_IMP_THM
val RIGHT_IMP_FORALL_THM = GSYM boolTheory.RIGHT_FORALL_IMP_THM
val RIGHT_AND_EXISTS_THM = GSYM RIGHT_EXISTS_AND_THM
val OR_EXISTS_THM        = GSYM EXISTS_OR_THM
val LEFT_IMP_EXISTS_THM  = boolTheory.LEFT_EXISTS_IMP_THM
val RIGHT_IMP_EXISTS_THM = GSYM RIGHT_EXISTS_IMP_THM;

(* -------------------------------------------------------------------------
 * Sometimes useful: a 1-way Skolemization conversion, introducing defs for
 * epsilon-terms.
 *
 * Taken directly from GTT.
 * ------------------------------------------------------------------------- *)
val (args,ONEWAY_SKOLEM_CONV) =
  let val args = ref []
      val P = ``P:'a->bool``
      and z = ``z:'a``
      and aty = Type.alpha
  and pth1 = prove
   (``(?x:'a. P) = P``,
    REWRITE_TAC[EXISTS_SIMP])
  and pth2 = prove
   (``(z:'a = $@ P) ==> ($? P = P z)``,
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [BETA_THM,EXISTS_DEF])
  in (args,fn gvs => fn tm =>
    let val _ = args := (gvs,tm)::(!args)
	val (eq,atm) = dest_comb tm
	val (v,bod) = dest_abs atm
	val fvs = free_vars bod
    in if op_mem aconv v fvs then
	let val nfvs = op_intersect aconv fvs gvs
	    val eps = mk_thy_const{Name="@",Thy="min",
                         Ty=(type_of v --> Type.bool) --> type_of v}
	    val etm = mk_comb(eps,atm)
	    val stm = list_mk_abs(nfvs,etm)
	    val gv = genvar(type_of stm)
	    val th1 = ASSUME(mk_eq(gv,stm))
	    val th2 = RIGHT_BETAS nfvs th1
	    val th3 = PINST [aty |-> type_of v]
                            [P |-> atm, z |-> lhs(concl th2)] pth2
	in
	    CONV_RULE (RAND_CONV BETA_CONV) (MP th3 th2)
	end
       else
	   let val th1 = PINST  [aty |-> type_of v] [P |-> atm] pth1
	   in CONV_RULE (LAND_CONV(RAND_CONV(ALPHA_CONV v))) th1
	   end
    end
    handle e as (HOL_ERR _) => WRAP_ERR("ONEWAY_SKOLEM_CONV",e))
  end
  ;;


(* -------------------------------------------------------------------------
  Conversion for negation normal form. The user has the option of
  performing one-way Skolemization too, and of angling for a short
  CNF (cnflag = true) or a short DNF (cnflag = false). The user can give
  a conversion to be applied at literals (can always use REFL).

  This is exponential on equations; we could produce a linear version
  by recursively doing NNF_CONV_P and NNF_CONV_N in parallel, but it
  hardly seems worth it for practical cases. (It also makes keeping
  track of bound variables to use as args to Skolem functions harder.)

  This code comes directly from JRH's GTT.  Ported by DRS.

   val x = NNF_CONV NO_CONV false (--`p ==> q = ~q ==> ~p`--);
   val x = NNF_CONV NO_CONV false (--`~(p ==> q) ==> q ==> p`--);
   val x = NNF_CONV NO_CONV false (--`?y:'a. !x. P y ==> P x`--);
   val x = NNF_CONV NO_CONV false
      (--`(!x y. ?z. !w. P x /\ Q y ==> R z /\ U w)
           ==> (?x y. P x /\ Q y) ==> (?z. R z)`--);

   val ths = ASSUME (mk_neg ERIC);
   CONV_RULE (NNF_SKOLEM_CONV NO_CONV true) ths;
   CONV_RULE (NNF_CONV NO_CONV true) ths;
  |- ?P. ~(!Q R x'. ?v w. !y z. P x' /\ Q y ==> (P v \/ R w) /\ (R z ==> Q v))

 *-------------------------------------------------------------------------- *)

val (NNF_CONV,NNF_SKOLEM_CONV) =
    let val p = ``p:bool`` and q = ``q:bool`` and q' = ``q':bool``
	val P = ``P:'a->bool`` and aty = ``:'a``
	val pth_pimp = TAUT`(p ==> q) = q \/ ~p`
	val pth_peq1 = TAUT`(p = q) = (p \/ ~q) /\ (~p \/ q)`
	val pth_peq2 = TAUT`(p = q) = (p /\ q) \/ (~p /\ ~q)`
	val pth_pcond1 =
          TAUT`(if p then q else q') = (p \/ q') /\ (~p \/ q)`
	val pth_pcond2 =
          TAUT`(if p then q else q') = (p /\ q) \/ (~p /\ q')`
	val pth_nnot = TAUT`~~p:bool = p`
	val pth_nand = TAUT`~(p /\ q) = ~p \/ ~q`
	val pth_nor = TAUT`~(p \/ q) = ~p /\ ~q`
	val pth_nimp = TAUT`~(p ==> q) = ~q /\ p`
	val pth_neq1 = TAUT`~(p = q) = (p \/ q) /\ (~p \/ ~q)`
	val pth_neq2 = TAUT`~(p = q) = (p /\ ~q) \/ (~p /\ q)`
	val pth_ncond1 =
          TAUT`~(if p then q else q') = (p \/ ~q') /\ (~p \/ ~q)`
	val pth_ncond2 =
          TAUT`~(if p then q else q') = (p /\ ~q) \/ (~p /\ ~q')`
	val EXISTS_UNIQUE_THM2 = prove
	    (``!P. (?!x:'a. P x) = (?x. P x /\ !y. P y ==> (y = x))``,
		GEN_TAC THEN REWRITE_TAC [EXISTS_UNIQUE_DEF,
					  LEFT_AND_EXISTS_THM,BETA_THM] THEN
		EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN ``x:'a`` STRIP_ASSUME_TAC)
                THEN
		EXISTS_TAC ``x:'a`` THEN
		ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
		[ALL_TAC, MATCH_MP_TAC EQ_TRANS THEN
		 EXISTS_TAC ``x:'a`` THEN
		 CONJ_TAC THENL [ALL_TAC, CONV_TAC SYM_CONV]] THEN
		FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[])
	val TRIVIALIZE_CONV = GEN_REWRITE_CONV TOP_DEPTH_CONV
	    [NOT_CLAUSES, AND_CLAUSES, OR_CLAUSES, IMP_CLAUSES, EQ_CLAUSES,
	     COND_CLAUSES, COND_ID, FORALL_SIMP, EXISTS_SIMP,
	     EXISTS_UNIQUE_THM2]
	fun LOCAL_QUANT_CONV pth tm =
	    let val (uq,atm) = dest_comb tm
		val (v,bod) = dest_abs atm
		val th0 = PINST [aty |-> (type_of v)] [P |-> atm] pth
		val (eq,rtm) = dest_comb(rand(concl th0))
		val (vv,bod) = dest_abs rtm
		val (nt,red) = dest_comb bod
		val th1 = ABS vv (AP_TERM nt (BETA_CONV red))
		val th2 = ALPHA_CONV v (rand(concl th1))
	    in TRANS th0 (AP_TERM eq (TRANS th1 th2))
	    end
	val eta =  CONV_RULE ((LAND_CONV o RAND_CONV o RAND_CONV) ETA_CONV)
	val LOCAL_NOT_FORALL_CONV =
	    let val pth = eta (ISPEC P NOT_FORALL_THM)
	    in LOCAL_QUANT_CONV pth
	    end
	val LOCAL_NOT_EXISTS_CONV =
	    let val pth = eta (ISPEC P NOT_EXISTS_THM)
	    in LOCAL_QUANT_CONV pth
	    end
	val LOCAL_COND_ELIM_THM1 = prove
	    (``!P:'a->bool.
                   P(if a then b else c) = (~a \/ P(b)) /\ (a \/ P(c))``,
		GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[])
	val LOCAL_COND_ELIM_CONV1 =
	    HIGHER_REWRITE_CONV[LOCAL_COND_ELIM_THM1]
	val LOCAL_COND_ELIM_THM2 = prove
	    (``!P:'a->bool.
                   P(if a then b else c) = a /\ P(b) \/ ~a /\ P(c)``,
		GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[])
	val LOCAL_COND_ELIM_CONV2 = HIGHER_REWRITE_CONV[LOCAL_COND_ELIM_THM2]
	fun NNF_CONV_OPT baseconv skolemize cnflag =
	    let fun NNF_CONV_P emb bvs tm =
		let val (ll,r) = dest_comb tm
		in let val s = name_of_const ll
		   in if s = ("~","bool") then NNF_CONV_N emb bvs r
		      else if s = ("?","bool") then
			  if skolemize then
			      RIGHT_NNF emb bvs (ONEWAY_SKOLEM_CONV bvs tm)
			  else
			      let val (v,bod) = dest_abs r
			      in AP_TERM ll (ABS v (NNF_CONV_P emb bvs bod))
			      end
		      else if s = ("!","bool") then
			  let val (v,bod) = dest_abs r
			  in AP_TERM ll (ABS v (NNF_CONV_P true (v::bvs) bod))
			  end
		      else NNF_CONV_TERMINAL emb bvs tm
		   end
	           handle HOL_ERR _ =>
		   let val (oper,l) = dest_comb ll
		   in let val s = name_of_const oper
		       in if s = ("/\\","bool") orelse s = ("\\/","bool") then
			   MK_COMB(AP_TERM oper (NNF_CONV_P emb bvs l),
				   NNF_CONV_P emb bvs r)
			  else if s = ("==>","min") then
		           RIGHT_NNF emb bvs (INST [p |-> l, q |-> r] pth_pimp)
			  else if s = ("=","min") then
			      let val pth =
				  if cnflag andalso emb then
				      INST [p |-> l, q |-> r] pth_peq1
				  else INST [p |-> l, q |-> r] pth_peq2
			      in RIGHT_NNF emb bvs pth
			      end
			  else NNF_CONV_TERMINAL emb bvs tm
		       end
  		       handle HOL_ERR _ =>
		       let val (b,c) = dest_comb oper
		       in if name_of_const b = ("COND","bool") then
			   if cnflag andalso emb then
			       INST [p |-> b, q |-> l, q' |-> r] pth_pcond1
			   else INST [p |-> b, q |-> l, q' |-> r] pth_pcond2
			  else fail()
		       end
		       handle HOL_ERR _ => NNF_CONV_TERMINAL emb bvs tm
		   end
		end
	        handle HOL_ERR _ => NNF_CONV_TERMINAL emb bvs tm
		and NNF_CONV_N emb bvs tm =
		    let val (ll,r) = dest_comb tm
		    in let val s = name_of_const ll
		       in if s = ("~","bool") then
			   RIGHT_NNF emb bvs (INST [p |-> r] pth_nnot)
		       else if s = ("?","bool") then
			   RIGHT_NNF emb bvs (LOCAL_NOT_EXISTS_CONV tm)
		       else if s = ("!","bool") then
			   RIGHT_NNF emb bvs (LOCAL_NOT_FORALL_CONV tm)
		       else NNF_CONV_TERMINAL emb bvs(mk_neg tm)
		       end
		       handle HOL_ERR _ =>
		       let val (oper,l) = dest_comb ll
		       in let val s = name_of_const oper
			  in if s = ("/\\","bool") then
			      RIGHT_NNF emb bvs (INST [p|->l, q|-> r] pth_nand)
			     else if s = ("\\/","bool") then
				 RIGHT_NNF emb bvs (INST [p|->l,q|->r] pth_nor)
			     else if s = ("==>","min") then
				RIGHT_NNF emb bvs (INST [p|->l,q|->r] pth_nimp)
			     else if s = ("=","min") then
				 let val pth =
				     if cnflag andalso emb then
					 INST [p |-> l, q |-> r] pth_neq1
				     else INST [p |-> l, q |-> r] pth_neq2
				 in RIGHT_NNF emb bvs pth
				 end
			     else NNF_CONV_TERMINAL emb bvs (mk_neg tm)
			  end
		          handle HOL_ERR _ =>
			  let val (b,c) = dest_comb oper
			  in if name_of_const b = ("COND","bool") then
			      if cnflag andalso emb then
				  INST [p |-> b, q |-> l, q' |-> r] pth_ncond1
			      else INST [p |-> b, q |-> l, q' |-> r] pth_ncond2
			     else fail()
			  end handle HOL_ERR _
                          => NNF_CONV_TERMINAL emb bvs (mk_neg tm)
		       end
		    end
		    handle HOL_ERR _ => NNF_CONV_TERMINAL emb bvs (mk_neg tm)
		and RIGHT_NNF emb bvs th =
		    TRANS th (NNF_CONV_P emb bvs (rand(concl th)))
		and NNF_CONV_TERMINAL emb bvs tm =
		    let val th =
			if cnflag andalso emb then
			    LOCAL_COND_ELIM_CONV1 tm
			else LOCAL_COND_ELIM_CONV2 tm
			val tm' = rand(concl th)
		    in TRANS th (NNF_CONV_P emb bvs tm')
		    end
  		    handle HOL_ERR _ =>
			let val th = baseconv tm
			    val tm' = rand(concl th)
			in TRANS th (NNF_CONV_P emb bvs tm')
			end
		    handle HOL_ERR _ => REFL tm
	    in NNF_CONV_P false
	    end
            handle e as HOL_ERR _ => WRAP_ERR("NNF_CONV_P",e);
    in ((fn baseconv => fn cnflag =>
	 TRIVIALIZE_CONV THENC
	 NNF_CONV_OPT baseconv false cnflag []),
	(fn baseconv => fn cnflag =>
	 TRIVIALIZE_CONV THENC
	 NNF_CONV_OPT baseconv true cnflag []))
    end;;


(*---------------------------------------------------------------------------*
 * Put a term formula not containing equivalences or conds into prenex form. *
 *  PRENEX_CONV (--`P /\ Q`--) handle e => Raise e;                          *
 *  PRENEX_CONV (--`P (x:'a) ==> P y /\ Q`--) handle e => Raise e;           *
 *  PRENEX_CONV (--`!x:'a. P x ==> P y /\ Q`--) handle e => Raise e;         *
 *  PRENEX_CONV `(!x:'a. P x) /\ Q`;;                                        *
 *  PRENEX_CONV (--`(!x:'a. P x) /\ Q`--);;                                  *
 *  PRENEX_CONV (--`(?x. P x) ==> P y /\ Q`--) handle e => Raise e;          *
 *  PRENEX_CONV (--`(?x. P x) ==> (!y. P y /\ Q)`--) handle e => Raise e;    *
 * ------------------------------------------------------------------------- *)

val PRENEX_CONV = let
  val PRENEX1_QCONV =
    GEN_REWRITE_CONV I
    [NOT_FORALL_THM, NOT_EXISTS_THM,
     AND_FORALL_THM, LEFT_AND_FORALL_THM, RIGHT_AND_FORALL_THM,
     LEFT_OR_FORALL_THM, RIGHT_OR_FORALL_THM,
     LEFT_IMP_FORALL_THM, RIGHT_IMP_FORALL_THM,
     LEFT_AND_EXISTS_THM, RIGHT_AND_EXISTS_THM,
     OR_EXISTS_THM, LEFT_OR_EXISTS_THM, RIGHT_OR_EXISTS_THM,
     LEFT_IMP_EXISTS_THM, RIGHT_IMP_EXISTS_THM]
  fun PRENEX2_QCONV tm =
    (PRENEX1_QCONV THENCQC (BINDER_CONV PRENEX2_QCONV)) tm
  fun PRENEX_QCONV tm = let
    val (lop,r) = dest_comb tm
	  exception DEST_CONST
  in
    let
      val cname = name_of_const lop
                handle HOL_ERR _ => raise DEST_CONST
    in
      if cname = ("!","bool") orelse cname = ("?","bool")
        then AP_TERM lop (Conv.ABS_CONV PRENEX_QCONV r)
      else if cname = ("~","bool")
             then (RAND_CONV PRENEX_QCONV THENQC PRENEX2_QCONV) tm
           else failwith "unchanged"
    end
    handle DEST_CONST => let
      val (oper,l) = dest_comb lop
      val cname = name_of_const oper
    in
      if cname = ("/\\","bool") orelse
         cname = ("\\/","bool") orelse
         cname = ("==>","min")
        then
          let
            val th =
              let
                val lth = PRENEX_QCONV l
              in
                let
                  val rth = PRENEX_QCONV r
                in
                  MK_COMB(AP_TERM oper lth,rth)
                end
                handle HOL_ERR _ => AP_THM (AP_TERM oper lth) r
              end
              handle HOL_ERR _ => AP_TERM lop (PRENEX_QCONV r)
            val tm' = rand(concl th)
            val th' = PRENEX2_QCONV tm'
          in
            TRANS th th'
          end
          handle HOL_ERR _ => PRENEX2_QCONV tm
		  else failwith "unchanged"
    end
	end
  in
     fn tm => TRY_CONV PRENEX_QCONV tm
  end;


(* -------------------------------------------------------------------------
 * Put a propositional term in NNF into CNF.
 *
 * PROP_CNF_CONV (--`P /\ Q \/ SS /\ R`--);
 * ------------------------------------------------------------------------- *)

val PROP_CNF_CONV =
  let val th1 = TAUT`a \/ (b /\ c) = (a \/ b) /\ (a \/ c)`
      and th2 = TAUT`(a /\ b) \/ c = (a \/ c) /\ (b \/ c)`
      val f =  DISTRIB_CONV(th1,th2) THENC
	  DEPTH_BINOP_CONV conj_tm (ASSOC_CONV DISJ_ASSOC) THENC
	  ASSOC_CONV CONJ_ASSOC
  in fn tm => f tm
      handle e => WRAP_ERR("PROP_CNF_CONV",e)
  end;


(* -------------------------------------------------------------------------
 * Likewise DNF.
 * ------------------------------------------------------------------------- *)

val PROP_DNF_CONV =
    let val th1 = TAUT`a /\ (b \/ c) = (a /\ b) \/ (a /\ c)`
	and th2 = TAUT`(a \/ b) /\ c = (a /\ c) \/ (b /\ c)`
	val f =  DISTRIB_CONV(th1,th2) THENC
	    DEPTH_BINOP_CONV disj_tm (ASSOC_CONV CONJ_ASSOC) THENC
	    ASSOC_CONV DISJ_ASSOC
    in fn tm => f tm
	handle e => WRAP_ERR("PROP_DNF_CONV",e)
    end;


(* -------------------------------------------------------------------------
 * Put a formula in NNF into prenex CNF.
 *
 * CNF_CONV (--`P /\ Q \/ SS /\ R`--);
 * CNF_CONV (--`!x. P /\ (?y. Q y) \/ SS /\ R`--);
 * ------------------------------------------------------------------------- *)

val CNF_CONV =
  let val f =
      PRENEX_CONV THENC
      BODY_CONV (PROP_CNF_CONV THENC
		 DEPTH_BINOP_CONV conj_tm (ASSOC_CONV DISJ_ASSOC) THENC
		 ASSOC_CONV CONJ_ASSOC)
  in fn tm => f tm
      handle e => WRAP_ERR("CNF_CONV",e)
  end;;

(* ------------------------------------------------------------------------- *)
(* Put a formula in NNF into prenex DNF.                                     *)
(* ------------------------------------------------------------------------- *)

val DNF_CONV =
  let val f =
      PRENEX_CONV THENC
      BODY_CONV (PROP_DNF_CONV THENC
		 DEPTH_BINOP_CONV disj_tm (ASSOC_CONV CONJ_ASSOC) THENC
		 ASSOC_CONV DISJ_ASSOC)
  in fn tm => f tm
      handle e => WRAP_ERR("DNF_CONV",e)
  end;;


(* ------------------------------------------------------------------------- *)
(* Reassociate an NNF to put the disjuncts with the lowest disjunctive       *)
(* paths first (useful as input to tableaux provers).                       *)
(* ------------------------------------------------------------------------- *)
val DISJPATH_CONV =
    let val DISJ_AC = EQT_ELIM o AC_CONV(DISJ_ASSOC,DISJ_SYM)
	fun DISJPATH_CONV tm =
	    if is_disj tm then
		let val djs = strip_disj tm
		    val dnths = map DISJPATH_CONV djs
		    val sdths = sort (fn (_,m) => fn (_,n) => m <= n) dnths
		    val th1 = end_itlist MK_DISJ (map fst sdths)
		    val th2 = DISJ_AC(mk_eq(tm,lhand(concl th1)))
		in (TRANS th2 th1,itlist (fn x => fn y => y + snd x) dnths 0)
		end
	    else if is_conj tm then
		let val (l,r) = dest_conj tm
		    val (lth,ln) = DISJPATH_CONV l
		    and (rth,rn) = DISJPATH_CONV r
		in (MK_CONJ lth rth,ln * rn)
		end

	     else if is_forall tm then
		let val (v,bod) = dest_forall tm
		    val (th,n) = DISJPATH_CONV bod
		in (MK_FORALL v th,n)
		end
	     else (REFL tm,1)
    in fn tm => fst(DISJPATH_CONV tm)
                handle e as (HOL_ERR _) => WRAP_ERR("DISJPATH_CONV",e)
    end;;

(* ------------------------------------------------------------------------- *)
(* Attempt to combine alpha-equivalent Skolem functions.                     *)
(* ------------------------------------------------------------------------- *)

val RATSKOL =
    let fun findreps skols th =
	case skols of
	    [] => th
	  | (sk::sks) =>
		let val rsk = rand sk
		    val sk' = first (fn sk' => aconv (rand sk') rsk) sks
		    val th1 = TRANS (ASSUME sk') (SYM(ASSUME sk))
		in findreps sks (SUBS[th1] th)
		end
	    handle HOL_ERR _ => findreps sks th
    in fn th => findreps (hyp th) th
	handle e => WRAP_ERR("RATSKOL",e)
    end;;

(* ------------------------------------------------------------------------- *)
(* Eliminate Skolem functions definitions from a theorem.                    *)
(* ------------------------------------------------------------------------- *)

val SKELIM =
    let fun skelim eq th =
	let val (l,r) = dest_eq eq
	in MP (INST [l |-> r] (DISCH eq th)) (REFL r)
	end
    in fn skols => fn th =>
	let val vars = map lhand skols
	    val markup =
                map (fn skol =>
			(skol,lhand skol,
			 op_intersect aconv vars (free_vars(rand skol))))
                    skols
	    fun take sofar l =
		let val ((skol,v,var),rest) =
                        Lib.pluck (fn (skol,v,vars) =>
                                      null (op_set_diff aconv vars sofar)) l
		in
                   skol::take (v::sofar) rest
		end
                handle HOL_ERR _ => []
	    val sskols = take [] markup
	in itlist skelim sskols th
	end
    handle e => WRAP_ERR("SKELIM",e)
    end;

(* ------------------------------------------------------------------------- *)
(* Wrapper to apply conversion then a refutation procedure.                  *)
(* ------------------------------------------------------------------------- *)

fun CONV_THEN_REFUTE (conv:conv) refuter tm =
    let val th1 = conv tm
	val tm' = rand(concl th1)
	val th2 = refuter tm'
    in PROVE_HYP (EQ_MP th1 (ASSUME tm)) th2
    end;;


(* -------------------------------------------------------------------------
 * Wrapper for a refuter which takes a list of theorems in CNF.
 * ------------------------------------------------------------------------- *)

fun thm_eq th1 th2 =
  let
    val hyps1 = hypset th1 and c1 = concl th1
    val hyps2 = hypset th2 and c2 = concl th2
  in
    HOLset.equal(hyps1,hyps2) andalso aconv c1 c2
  end

local fun split_thms [] dun = dun
        | split_thms (th::thl) dun =
           split_thms (snd(SPEC_VAR th)::thl) dun
            handle HOL_ERR _ =>
               split_thms ((CONJUNCT1 th)::(CONJUNCT2 th)::thl) dun
               handle HOL_ERR _
                => let val th' = CONV_RULE CNF_CONV th
                   in
                     if (thm_eq th th') then split_thms thl (th::dun)
                     else split_thms (th'::thl) dun
                   end
in
fun CNF_THEN_REFUTE cnfrefuter tm = cnfrefuter (split_thms [ASSUME tm] [])
	handle e => WRAP_ERR("CNF_THEN_REFUTE",e)
end;;


(* ------------------------------------------------------------------------- *)
(* Wrapper to prove a term by negating it, putting it into the user's        *)
(* chosen version of NNF, splitting up the disjuncts and calling refuter.    *)
(*                                                                           *)
(* The expectation is that "refute p" gives "p |- F".                        *)
(* ------------------------------------------------------------------------- *)
(* used for debugging refutation provers *)

val latest = ref (NONE: (thm * thm * term) option);

val REFUTE =
  let val pth = TAUT`(~p ==> F) ==> p`
      val p = Term`p:bool`
      val CONJ_AC = EQT_ELIM o AC_CONV(CONJ_ASSOC,CONJ_SYM)
      val pth_d = TAUT`(a \/ b) /\ c = (a /\ c) \/ (b /\ c)`
      fun refute refuter tm =
	  let (* val _ = trace (1,"refute -- ",tm)  *)
	      val (l,r) = dest_disj tm
	  in SIMPLE_DISJ_CASES (refute refuter l) (refute refuter r)
	  end
      handle HOL_ERR _ =>
	  let val cjs = strip_conj tm
	      val (ourdj,ocjs) = Lib.pluck is_disj cjs
	      val acth = CONJ_AC (mk_eq(tm,list_mk_conj(ourdj::ocjs)))
	      val exth = CONV_RULE (RAND_CONV(REWR_CONV pth_d)) acth
	      val tm' = rand(concl exth)
	      val rth = refute refuter tm'
	  in PROVE_HYP (EQ_MP exth (ASSUME tm)) rth
	  end
      handle HOL_ERR _ => refuter tm
    (* (trace_tm (3,"Attempting next disjunction -- ",tm); refuter tm)  *)
  in fn baseconv => fn afterconv => fn cnflag => fn refuter => fn tm =>
    let val ntm = mk_neg tm
	val th1 = (NNF_SKOLEM_CONV baseconv cnflag THENC afterconv) ntm
	val th2 = RATSKOL th1
	val (l,r) = dest_eq(concl th2)
        val _ = latest := SOME (th1,th2,r)
	val rth = if aconv r false_tm then ASSUME r else refute refuter r
	val th3 = PROVE_HYP (EQ_MP th2 (ASSUME l)) rth
	val th4 = SKELIM (hyp th1) th3
	val th5 = DISCH ntm th4 (* (itlist DISCH (subtract (hyp th4) [ntm])*)
    in MP (INST [p |-> tm] pth) th5
    end
    handle e as HOL_ERR _ => WRAP_ERR("REFUTE",e)
  end;


(* -------------------------------------------------------------------------
 * Prove formula by applying refuter to its CNF breakdown.
 * ------------------------------------------------------------------------- *)

fun CNF_REFUTE baseconv afterconv refuter tm =
  REFUTE baseconv afterconv true (CNF_THEN_REFUTE refuter) tm
  handle e => WRAP_ERR("CNF_REFUTE",e);;

(* -------------------------------------------------------------------------
 * Produce a conversion which throws theorems into a proof procedure.
 * ------------------------------------------------------------------------- *)

fun CONV_OF_PROVER prover ths tm =
    let val tms = map concl ths
	val tm' = itlist (curry mk_imp) tms tm
	val th' = prover tm'
    in EQT_INTRO (itlist (C MP) (rev ths) th')
    end
handle e => WRAP_ERR("CONV_OF_PROVER",e);;

(* ------------------------------------------------------------------------- *)
(* Equate lambda-reduced and universally quantified applied definitions.     *)
(* ------------------------------------------------------------------------- *)

val EQ_ABS_CONV =
  let val pth = prove
      (``(f:'a->'b = \x. t x) = (!x. f x = t x)``,
       REWRITE_TAC[FUN_EQ_THM, BETA_THM])
      val cnv = REWR_CONV pth
      fun EQ_ABS_CONV tm =
	  (cnv THENC BINDER_CONV EQ_ABS_CONV) tm
	  handle HOL_ERR _ => REFL tm
  in EQ_ABS_CONV
  end;

(* ------------------------------------------------------------------------- *)
(* Elimination of topmost free lambda-expressions in a formula.              *)
(* ------------------------------------------------------------------------- *)

val UNLAMB_CONV =
    let val pth = prove
	(``P (t:'a) = (!x. (x = t) ==> P x)``,
	    EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
	    FIRST_ASSUM MATCH_MP_TAC THEN REFL_TAC)
	and P_tm = ``P:'a->bool`` and t_tm = ``t:'a``
        and aty = Type.alpha
    in fn tm =>
	let val t = find_term is_abs tm
	    val gv = genvar(type_of t)
	    val abs = mk_abs(gv,subst[t |-> gv] tm)
	    val th1 = PINST [aty |-> type_of t] [P_tm |-> abs, t_tm |-> t] pth
	    val tm1 = concl th1
	    val th0 = SYM(BETA_CONV(rand(rator tm1)))
	    val th2 = CONV_RULE
		(RAND_CONV(BINDER_CONV
			   (COMB2_CONV
			    (RAND_CONV EQ_ABS_CONV) BETA_CONV))) th1
	in TRANS th0 th2
	end
    end;


(* ------------------------------------------------------------------------- *)
(* Perform a superior FOL reduction of a higher order NNF formula.           *)
(* ------------------------------------------------------------------------- *)

val I_THM = combinTheory.I_THM;
fun last [] = failwith "last"
  | last [h] = h
  | last (h::t) = last t;

val FOL_CONV =
    let val APP_CONV =
	let val th = prove
	    (``!(f:'a->'b) x. f x = I f x``, REWRITE_TAC[I_THM])
	in REWR_CONV th
	end
	fun get_heads x tm sofar =
	    let val (v,bod) = dest_forall tm
	    in if aconv x v then sofar else get_heads x bod sofar
	    end
	handle HOL_ERR _ =>
	    let val (l,r) = dest_disj tm
	    in get_heads x l (get_heads x r sofar)
	    end
	handle HOL_ERR _ =>
	    let val (l,r) = dest_conj tm
	    in get_heads x l (get_heads x r sofar)
	    end
	handle HOL_ERR _ =>
	    let val tm' = dest_neg tm
	    in get_heads x tm' sofar
	    end
	handle HOL_ERR _ =>
	    let val (hop,args) = strip_comb tm
		val sofar' =
		    if aconv hop x then insert (length args) sofar else sofar
	    in itlist (get_heads x) args sofar'
	    end

	fun FOL1_CONV v tm =
	    let val nums = get_heads v tm []
	    in if length nums <= 1 then REFL tm else
		let val snums = sort (curry op <=) nums
		    val hnum = hd snums and tnums = tl snums
		    val (atys,_) = splitlist Type.dom_rng (type_of v)
		    val otys = fst(liteLib.chop_list(last tnums) atys)
		    val args = map genvar otys
		    val maxterm = list_mk_comb(v,args)
		    fun mk_instance n t =
			if n = hnum then REFL t
                      else (APP_CONV THENC (LAND_CONV (mk_instance (n-1)))) t
		    val instances = map (fn n => mk_instance n maxterm) tnums
		    val frozen = map (ADD_ASSUM (mk_eq(v,v))) instances
		    val thm = GEN_REWRITE_CONV DEPTH_CONV frozen tm
		in PROVE_HYP (REFL v) thm
		end
	    end
	fun FOLS_CONV tm =
	    let val (v,bod) = dest_forall tm
		val th1 = FOLS_CONV bod
		val tm1 = rand(concl th1)
	    in AP_TERM(rator tm) (ABS v (TRANS th1 (FOL1_CONV v tm1)))
	    end
	handle HOL_ERR _ =>
	    let val (l,r) = dest_disj tm
	    in MK_DISJ (FOLS_CONV l) (FOLS_CONV r)
	    end
	handle HOL_ERR _ =>
	    let val (l,r) = dest_conj tm
	    in MK_CONJ (FOLS_CONV l) (FOLS_CONV r)
	    end
	handle HOL_ERR _ => REFL tm
    in fn tm =>
	let val fvs = free_vars tm
	in (EVERY_CONV (map FOL1_CONV fvs) THENC FOLS_CONV) tm
	end
    end;

val _ = Parse.temp_set_grammars ambient_grammars;

end; (* struct *)
