(*=======================================================================
 * Support for AC reasoning.
 *=====================================================================*)

structure AC :> AC =
struct

open HolKernel boolSyntax Drule Conv liteLib Ho_Rewrite Abbrev;

val INST = HolKernel.INST

infix 5 |->
infix THENCQC THENQC
fun ERR x = STRUCT_ERR "AC" x;
fun WRAP_ERR x = STRUCT_WRAP "AC" x;

fun AC thms = EQT_ELIM o AC_CONV thms;

(* ------------------------------------------------------------------------- *)
(* ACI equivalence for conjunctions.                                         *)
(* ------------------------------------------------------------------------- *)

val CONJ_ACI =
    let fun FIND_CONJS thl tm =
	let val (l,r) = dest_conj tm
	in CONJ (FIND_CONJS thl l) (FIND_CONJS thl r)
	end handle HOL_ERR _ => first (fn th => aconv (concl th) tm) thl
    in fn tm =>
	let val (l,r) = dest_eq tm
	    val thl = CONJUNCTS(ASSUME l)
	    and thr = CONJUNCTS(ASSUME r)
	in IMP_ANTISYM_RULE (DISCH_ALL (FIND_CONJS thl r))
                            (DISCH_ALL (FIND_CONJS thr l))
	end
    end;;

(* ------------------------------------------------------------------------- *)
(* AC canonicalizing under a given ordering.                                 *)
(* ------------------------------------------------------------------------- *)

fun list_mk_binop oper = end_foldr (mk_binop oper);;

fun AC_CANON_GEN_CONV acthms =
 let val oper = rator(rator(rand(repeat (body o rand) (concl (snd acthms)))))
     val AC_fn = AC acthms
 in fn order => fn tm =>
    let val op' = repeat rator tm
    in if can (ho_match_term [] empty_tmset oper) op'
       then let val op' = repeat rator tm
                val tmlist = binops op' tm
                val stmlist = Listsort.sort order tmlist
                val tm' = list_mk_binop op' stmlist
            in AC_fn(mk_eq(tm,tm'))
            end
            handle HOL_ERR _ => REFL tm
       else failwith "AC_CANON_GEN_CONV"
    end
 end;

(* ------------------------------------------------------------------------- *)
(* And under the arbitrary term ordering.                                    *)
(* ------------------------------------------------------------------------- *)

fun AC_CANON_CONV acthms = AC_CANON_GEN_CONV acthms Term.compare;


(*- -------------------------------------------------------------------------*
 * DISTRIB_CONV                                                              *
 *                                                                           *
 * Distribution conversion. This could be optimized a bit by splitting up    *
 * the toplevel product and collecting all those which aren't sums; these'd  *
 * then only need to be distributed once and for all. Hardly worth it!       *
 *                                                                           *
 * Taken directly from the GTT source code, by JRH. Translation by           *
 * Donald Syme.  Jan 96.                                                     *
 * --------------------------------------------------------------------------*)

val DISTRIB_CONV =
  let fun RAW_DISTRIB_CONV lth rth hop lop =
        let val DISTRIB0_QCONV = GEN_REWRITE_CONV I [lth, rth]
            fun DISTRIB1_QCONV tm =
                  (DISTRIB0_QCONV THENCQC
                    (COMB2_QCONV (RAND_CONV DISTRIB1_QCONV) DISTRIB1_QCONV)) tm
            fun DISTRIB2_QCONV tm =
              let val (xop,r) = dest_comb tm
                  val (oper,l) = dest_comb xop
              in if aconv oper lop
                 then COMB2_QCONV (RAND_CONV DISTRIB2_QCONV) DISTRIB2_QCONV tm
                 else if aconv oper hop
                      then ((COMB2_QCONV (RAND_CONV DISTRIB2_QCONV)
                                 DISTRIB2_QCONV) THENQC DISTRIB1_QCONV) tm
                      else ERR("DISTRIB2_QCONV","")
              end
        in
           TRY_CONV DISTRIB2_QCONV
        end
  in
  fn (lth0,rth0) =>
     case boolSyntax.strip_comb(rand(snd(strip_forall(concl lth0))))
      of (lop0,[_,htm]) =>
          (let val hop0 = rator(rator htm)
           in if type_vars_in_term hop0 = []
              then RAW_DISTRIB_CONV lth0 rth0 hop0 lop0
              else let val vty = type_of htm
                   in fn tm =>
                       let val tyins = match_type vty (type_of tm)
                           val INST_fn = INST_TYPE tyins
                           and inst_fn = inst tyins
                       in
                          RAW_DISTRIB_CONV (INST_fn lth0) (INST_fn rth0)
                                           (inst_fn hop0) (inst_fn lop0) tm
                       end
                   end
           end handle HOL_ERR _ => failwith "DISTRIB_CONV")
       | _ => failwith "DISTRIB_CONV"
  end;



(*---------------------------------------------------------------------------*
 * Efficient left-association conversion.                                    *
 *                                                                           *
 * Taken directly from the GTT source code, by JRH. Translation by           *
 * Donald Syme.  Jan 96.                                                     *
 * ------------------------------------------------------------------------- *)

val ASSOC_CONV =
  let fun MK_ASSOC_CONV oper assoc t1 t2 t3 =
      let fun ASSOC_CONV tm =
	  let val (l,r) = dest_binop oper tm
	  in ASSOC_ACC_CONV l (ASSOC_CONV r)
             handle HOL_ERR _ => ASSOC_TAC_CONV l r
	  end
	  and ASSOC_TAC_CONV tm rtm =
	      let val (l,r) = dest_binop oper tm
		  val ppth = INST [t1 |-> l,t2 |-> r, t3 |-> rtm] assoc
	      in TRANS ppth (ASSOC_ACC_CONV l (ASSOC_TAC_CONV r rtm))
		  handle HOL_ERR _ =>
		      TRANS ppth (ASSOC_TAC_CONV l (rand(rand(concl ppth))))
		      handle HOL_ERR _ => ppth
	      end
	  and ASSOC_ACC_CONV tm ath =
	      let val (l,r) = dest_binop oper tm
		  val qth = ASSOC_ACC_CONV r ath
		  val rth = ASSOC_ACC_CONV l qth
              in
               TRANS
                 (INST [t1|->l, t2|->r, t3|->rand(rator(concl ath))] assoc) rth
	      end
	  handle HOL_ERR _  => AP_TERM (mk_comb(oper,tm)) ath
      in fn tm => ASSOC_CONV tm handle HOL_ERR _ => REFL tm
      end
  in fn rassoc =>
      let val assoc = SYM(SPEC_ALL rassoc)
	  val (opt1,t23) = dest_comb(rand(concl(assoc)))
	  val (oper,t1) = dest_comb opt1
	  val t2 = rand(rator t23) and t3 = rand t23
      in
         if type_vars(type_of oper) = []
         then MK_ASSOC_CONV oper assoc t1 t2 t3
	 else fn tm =>
	     let val xop = rator(rator tm)
             in case ho_match_term [] empty_tmset oper xop
		 of ([],tyin) =>
                     (let val inst_fn = Term.inst tyin
                          val assoc' = Thm.INST_TYPE tyin assoc
                          and t1' = inst_fn t1
                          and t2' = inst_fn t2
                          and t3' = inst_fn t3
	              in
                        MK_ASSOC_CONV xop assoc' t1' t2' t3' tm
                      end handle HOL_ERR _ => REFL tm)
                  | _ => REFL tm
	     end
      end
  end

end (* struct *)
