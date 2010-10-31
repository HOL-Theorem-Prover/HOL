structure lazyTools :> lazyTools =

struct

local

    open Globals HolKernel Parse Splaymap PrimitiveBddRules DerivedBddRules

    datatype lazy_thm = LazyThm of (term HOLset.set) * (term list) * (unit -> thm) | Thm of thm

    val lthms = ref (Splaymap.mkDict (Term.compare) : (term,lazy_thm)Splaymap.dict)
    val lzmode = ref true
    val _ = register_btrace("HolCheckLZ",lzmode);
    val dbglz = ref false
    val _ = Feedback.register_btrace("HolCheckDBGLZ",dbglz)

    fun SPECL tml th = rev_itlist Specialize tml th handle HOL_ERR _ => raise ERR"lzSPECL" ""

    val dpfx = "lzt_"

    val mp_thm = bossLib.DECIDE ``!x y. x ==> (x==>y=y)``
in

(*FIXME: if tm has free type vars, they are also free in the tm in the hyp after ASSUME and this may stump the rewriter *)
(* this is harder than it looks because we can't bind them like we do normal free_vars by doing a list_mk_forall *)
(* and really it can't be fixed directly because type vars also cannot be instantiated  in the concl if they are free in the hyp*)
(* so how do we "fix" this?
   ANS: it is possible to instantiate a tyvar in the hyp *and* the concl, so this is only a practical rather
   than theoretical obstacle  *)
(*NOTE: lthm does not need assums (except the one from ASSUME of course). See tphols2005 submission for proof and explanation *)
(* FIXME: however, add pointer_eq checks so that if I have A |- t and B|-t, then I store two jf's and fire the right one *)
(*FIXME: should I be using Susp to handle closures? No need, since a given jf fires at most once, but it might be cleaner to do so*)
fun mk_lthm ljf ejf =
    let val _ = profTools.bgt "lt_ml"(*PRF*)
	val res = if not (!lzmode)
		  then let val _ = profTools.bgt "lt_ml_eager"(*PRF*)
			   val eres = ejf()
			   val _ = profTools.ent "lt_ml_eager"(*PRF*)
		       in eres end
		  else let val _ = profTools.bgt "lt_ml_lazy"(*PRF*)
			   val (tm,jf) = ljf()
			   val _ = profTools.ent "lt_ml_lazy"(*PRF*)
			   val _ = profTools.bgt "lt_ml_admin"(*PRF*)
			   val fv = FVL [tm] empty_varset
			   val fvl = HOLset.listItems fv
			   val lt = boolSyntax.list_mk_forall (fvl,tm)
			   val _ =  (lthms := Splaymap.insert(!lthms,lt,LazyThm(fv,fvl,jf)))
			   val res = (SPECL fvl (ASSUME lt))
			   val _ = profTools.ent "lt_ml_admin"(*PRF*)
		       in res end
	val _ = profTools.ent "lt_ml"(*PRF*)
    in res end

fun get_thm (LazyThm (fv,fvl,jf)) =
    let val th'' = jf()
	val _ = profTools.bgt "lt_gt_genl"(*PRF*)
	(*val (asl,cn) = dest_thm th'' (* the commented code shows how inefficient GENL is *)
	val _ = HOLset.isEmpty(HOLset.intersection(hyp_frees th'',fv))
	val th' = mk_thm(asl,boolSyntax.list_mk_forall (fvl,cn))*)
	val th' = (GENL fvl (th'')) (* FIXME: this will fail if any fv is free in the hyp of th'' *)
	val _ = profTools.ent "lt_gt_genl"(*PRF*)
	val th = prove_lthm th'
	val _ = profTools.bgt "lt_gt_sm"(*PRF*)
	val _ = (lthms:=Splaymap.insert(!lthms,concl th',Thm th))
	val _ = profTools.ent "lt_gt_sm"(*PRF*)
    in th end
  | get_thm (Thm th) = th

and prove_lthm lthm =
    let val _ = dbgTools.DEN (dpfx^"_pl") (*DBG*)
	val res = List.foldl (fn (ass,lth) =>
				 let val _ = profTools.bgt "lt_pl_sm"(*PRF*)
				     val asslth = Splaymap.peek(!lthms,ass)
				     val _ = profTools.ent "lt_pl_sm"(*PRF*)
				 in if isSome asslth
				    then let val th = (get_thm (valOf asslth))
					     val _ = profTools.bgt "lt_pl_mpd"(*PRF*)
					     val th' = MP (DISCH ass lth) th
					     val _ = profTools.ent "lt_pl_mpd"(*PRF*)
					 in th' end
				    else lth
				 end) lthm (hyp lthm)
	    (*FIXME: if failure is caused by justifiers of some assum failing, this does not tell us which justifier failed*)
	    handle ex => (print "\n>>>lazyTools.prove_lthm failure\n"; print_thm lthm; failwith ("\n<<<lazyTools.prove_lthm failure\n"))
	val _ = dbgTools.DEX (dpfx^"_pl") (*DBG*)
    in res end

(*term_bdd analog for prove_lthm*)
fun prove_ltb ltb =
    let val _ = dbgTools.DEN (dpfx^"_pt") (*DBG*)
	val res = List.foldl (fn (ass,ltb) =>
				 let val _ = profTools.bgt "lt_pt_sm"(*PRF*)
				     val asslth = Splaymap.peek(!lthms,ass)
				     val _ = profTools.ent "lt_pt_sm"(*PRF*)
				 in if isSome asslth
				    then let val th = (get_thm (valOf asslth))
					     val _ = profTools.bgt "lt_pt_mpd"(*PRF*)
					     val tb =  BddEqMp (MP (Drule.ISPECL [concl th,getTerm ltb] mp_thm) th)
						 (BddDisch (BddExtendVarmap (getVarmap ltb) (thmToTermBdd th)) ltb)
					     val _ = profTools.ent "lt_pt_mpd"(*PRF*)
					 in tb end
				    else ltb
				 end) ltb (HOLset.listItems (getAssums ltb))
	    handle ex => (print "\n>>>lazyTools.prove_ltb failure\n"; print_term (getTerm ltb);
			  failwith ("\n<<<lazyTools.prove_ltb failure\n"))
	val _ = dbgTools.DEX (dpfx^"_pt") (*DBG*)
    in res end

(* quick check that lazification works *)
fun testlz s (jf:unit->Thm.thm) lt =
    if (!dbglz)
    then let val th = prove_lthm lt (* just calling jf may fail if jf uses tactics and lt has lazy lemmas *)
		 handle ex => (dbgTools.CBTH (s^"_lz") lt;dbgTools.DTH (s^"_lz") lt;
			       failwith("dbgTools.testlz failure 1:"^s))
	 in if (Term.compare(concl th,concl lt)=EQUAL)
	    then ()
	    else (dbgTools.CBTH s th; dbgTools.CBTH (s^"_lz") lt;dbgTools.DTH s th;dbgTools.DTH (s^"_lz") lt;
		  failwith ("dbgTools.testlz failure 2:"^s)) end
    else ()

end
end

