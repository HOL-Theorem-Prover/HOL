(* ===================================================================== *)
(* FILE          : drule.sml                                             *)
(* DESCRIPTION   : Derived theorems and rules. (Proper derivations are 	 *)
(*		   given as comments.) Largely translated from hol88.    *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon and                                   *)
(*                     Tom Melham, University of Cambridge, for hol88    *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)


structure Drule :> Drule =
struct

open HolKernel Parse boolTheory;

infix 5 ## |-> -->;
val bool = Type.bool
val op--> = Type.-->;
val alpha = Type.mk_vartype"'a";

fun DRULE_ERR function message = 
      HOL_ERR{origin_structure = "Drule",
	       origin_function = function,
                       message = message};

(*---------------------------------------------------------------------------*
 *  Add an assumption                                                        *
 *                                                                           *
 *      A |- t'                                                              *
 *   -----------                                                             *
 *    A,t |- t'                                                              *
 *---------------------------------------------------------------------------*)
fun ADD_ASSUM t th = MP (DISCH t th) (ASSUME t);


(*---------------------------------------------------------------------------
 * Transitivity of ==>
 *
 *   A1 |- t1 ==> t2            A2 |- t2 ==> t3
 * ---------------------------------------------
 *           A1 u A2 |- t1 ==> t3
 *
 * fun IMP_TRANS th1 th2 =
 *    let val {ant, conseq} = dest_imp (concl th1)
 *        val {ant=ant', conseq=conseq'} = dest_imp (concl th2)
 *        val _ = thm_assert (aconv conseq ant') "" ""
 *    in
 *   make_thm Count.ImpTrans (Tag.merge (tag th1) (tag th2), 
 *                 union (hyp th1) (hyp th2), 
 *                 mk_imp{ant=ant, conseq=conseq'})
 *    end
 *   handle _ => THM_ERR "IMP_TRANS" "";
 *
 *
 *  Modified: TFM 88.10.08 to use "union A1 A1" instead of A1 @ A2 
 *---------------------------------------------------------------------------*)

fun IMP_TRANS th1 th2 =
   let val {ant,conseq} = dest_imp(concl th1)
   in
     DISCH ant (MP th2 (MP th1 (ASSUME ant)))
   end 
   handle HOL_ERR _ => raise DRULE_ERR "IMP_TRANS" "";


(*---------------------------------------------------------------------------
 *
 *   A1 |- t1 ==> t2         A2 |- t2 ==> t1
 *  -----------------------------------------
 *            A1 u A2 |- t1 = t2
 *
 * fun IMP_ANTISYM_RULE th1 th2 =
 *   let val {ant=ant1, conseq=conseq1} = dest_imp(concl th1)
 *      and {ant=ant2, conseq=conseq2} = dest_imp(concl th2)
 *     val _ = thm_assert (aconv ant1 conseq2 andalso aconv ant2 conseq1) "" ""
 *   in
 *    make_thm Count.ImpAntisymRule(Tag.merge (tag th1) (tag th2), 
 *                 union (hyp th1) (hyp th2), 
 *                 mk_eq{lhs=ant1, rhs=conseq1}) 
 *  end 
 *  handle _ => THM_ERR "IMP_ANTISYM_RULE" "";
 *  Modified: TFM 88.10.08 to use "union A1 A2" instead of A1 @ A2 
 *---------------------------------------------------------------------------*)
 fun IMP_ANTISYM_RULE th1 th2 =
    let val {ant,conseq} = dest_imp(concl th1)
    in
      MP (MP (SPEC conseq (SPEC ant IMP_ANTISYM_AX)) th1) th2
    end
    handle HOL_ERR _ => raise DRULE_ERR"IMP_ANTISYM_RULE" "";
 

(*---------------------------------------------------------------------------*
 * Introduce  =T                                                             *
 *                                                                           *
 *     A |- t                                                                *
 *   ------------                                                            *
 *     A |- t=T                                                              *
 *                                                                           *
 *  local val truth = mk_const{Name="T", Ty = Type.bool}                     *
 *  in                                                                       *
 *  fun EQT_INTRO th =                                                       *
 *    let val t = concl th                                                   *
 *    in                                                                     *
 *      MP (MP (SPEC truth (SPEC t IMP_ANTISYM_AX))                          *
 *             (DISCH t TRUTH))                                              *
 *         (DISCH truth th)                                                  *
 *    end                                                                    *
 *  end;                                                                     *
 *                                                                           *
 *---------------------------------------------------------------------------*)


local val eq_thm = 
        let val {Bvar,...} = dest_forall (concl boolTheory.EQ_CLAUSES)
            val thm = CONJUNCT1(CONJUNCT2 (SPEC Bvar boolTheory.EQ_CLAUSES))
        in
          GEN Bvar (SYM thm)
        end
in
fun EQT_INTRO th = EQ_MP (SPEC (concl th) eq_thm) th 
                   handle HOL_ERR _ => raise DRULE_ERR "EQT_INTRO" ""
end;
  
(*---------------------------------------------------------------------------
 *  |- !x. t    ---->    x', |- t[x'/x]	 
 *---------------------------------------------------------------------------*)
fun SPEC_VAR th =
   let val {Bvar,...} = dest_forall (concl th)
       val bv' = variant (free_varsl (hyp th)) Bvar
   in (bv', SPEC bv' th)
   end;

(*---------------------------------------------------------------------------
 *
 *       A |-  (!x. t1 = t2)
 *   ---------------------------
 *    A |- (?x.t1)  =  (?x.t2)
 *
 * fun MK_EXISTS bodyth =
 *    let val {Bvar,Body} = dest_forall (concl bodyth)
 *        val {lhs,rhs} = dest_eq Body 
 *    in
 *    make_thm Count.MkExists (tag bodyth, hyp bodyth, 
 *                  mk_eq{lhs=mk_exists{Bvar=Bvar, Body=lhs},
 *                        rhs=mk_exists{Bvar=Bvar, Body=rhs}})
 *    end
 *    handle _ => THM_ERR "MK_EXISTS" "";
 *---------------------------------------------------------------------------*)

 fun MK_EXISTS bodyth =
    let val (x, sth) = SPEC_VAR bodyth
        val {lhs=a, rhs=b} = dest_eq (concl sth)
        val (abimp,baimp) = EQ_IMP_RULE sth
        fun HALF (p,q) pqimp =
           let val xp = mk_exists{Bvar=x,Body=p} 
               and xq = mk_exists{Bvar=x,Body=q}
           in
           DISCH xp (CHOOSE (x, ASSUME xp)
                            (EXISTS (xq,x) 
                                    (MP pqimp (ASSUME p))))
           end
    in
      IMP_ANTISYM_RULE (HALF (a,b) abimp) (HALF (b,a) baimp)
    end
    handle HOL_ERR _ => raise DRULE_ERR "MK_EXISTS" "";


(*---------------------------------------------------------------------------
 *
 *     A1 |- t1 = u1   ...   An |- tn = un       A |- t[ti]
 *    -------------------------------------------------------
 *               A1 u ... An u A |-  t[ui]
 *
 * fun GSUBS substfn ths th =
 *    let val (oracles,h',s) = itlist (fn th => fn (O,H,L) =>
 *             let val {lhs,rhs} = dest_eq (concl th) 
 *             in (Tag.merge (tag th) O, 
 *                 union (hyp th) H, (lhs |-> rhs)::L)
 *             end) ths (tag th, hyp th,[])
 *    in make_thm Count.Gsubs (oracles, h', substfn s (concl th))
 *    end
 *---------------------------------------------------------------------------*)
local fun combine [] [] = []
        | combine (v::rst1) (t::rst2) = (v |-> t) :: combine rst1 rst2
        | combine _ _ = raise DRULE_ERR "GSUBS.combine"
                                        "Different length lists"
in
fun GSUBS substfn ths th =
   let val ls = map (lhs o concl) ths
       val vars = map (genvar o type_of) ls
       val w = substfn (combine ls vars) (concl th)
   in
     SUBST (combine vars ths) w th
   end
end;


(*---------------------------------------------------------------------------
 *       A |- ti == ui
 *    --------------------
 *     A |- t[ti] = t[ui]
 *
 * fun SUBST_CONV replacements template tm =
 *   let val (ltheta, rtheta, hyps,oracles) = itlist 
 *              (fn {redex,residue} => fn (ltheta,rtheta,hyps,O) =>
 *                let val {lhs,rhs} = dest_eq (concl residue)
 *                in ((redex |-> lhs)::ltheta, (redex |-> rhs)::rtheta, 
 *                    union (hyp residue) hyps, 
 *                    Tag.merge (tag residue) O)
 *                end) replacements ([],[],[],std_tag)
 *       val _ = thm_assert (aconv (subst ltheta template) tm) "" ""
 *   in
 *     make_thm Count.SubstConv(oracles, hyps, 
 *                              mk_eq{lhs=tm, rhs = subst rtheta template})
 *   end
 *   handle _ => THM_ERR "SUBST_CONV" "";
 *---------------------------------------------------------------------------*)
fun SUBST_CONV theta template tm = 
  let fun retheta {redex,residue} = (redex |-> genvar(type_of redex))
      val theta0 = map retheta theta
      val theta1 = map2 (curry (op |->)) 
                        (map #residue theta0) (map #residue theta)
  in
   SUBST theta1 (mk_eq{lhs=tm,rhs=subst theta0 template}) (REFL tm)
  end
  handle HOL_ERR _ => raise DRULE_ERR "SUBST_CONV" "";


(*---------------------------------------------------------------------------
 * Extensionality
 *
 *     A |- !x. t1 x = t2 x
 *    ----------------------     (x not free in A, t1 or t2)
 *        A |- t1 = t2
 *
 * fun EXT th =
 *  let val {Bvar,Body} = dest_forall(concl th)
 *      val {lhs,rhs} = dest_eq Body
 *      val {Rator=Rator1, Rand=v1} = dest_comb lhs
 *      val {Rator=Rator2, Rand=v2} = dest_comb rhs
 *      val fv = union (free_vars Rator1) (free_vars Rator2)
 *      val _ = thm_assert (not(mem Bvar fv) andalso 
 *                          (Bvar=v1) andalso (Bvar=v2))  "" ""
 *    in make_thm Count.Ext(tag th, hyp th, mk_eq{lhs=Rator1, rhs=Rator2})
 *    end
 *    handle _ => THM_ERR "EXT" "";
 *---------------------------------------------------------------------------*)
fun EXT th =
   let val {Bvar,...} = dest_forall(concl th)
       val th1 = SPEC Bvar th
       (* th1 = |- t1 x = t2 x *)
       val {lhs=t1x, rhs=t2x} = dest_eq(concl th1)
       val x = #Rand(dest_comb t1x)
       val th2 = ABS x th1
       (* th2 = |- (\x. t1 x) = (\x. t2 x) *)
   in
   TRANS (TRANS(SYM(ETA_CONV (mk_abs{Bvar=x, Body=t1x}))) th2)
         (ETA_CONV (mk_abs{Bvar=x,Body=t2x}))
   end
   handle HOL_ERR _ => raise DRULE_ERR "EXT" "";


(*---------------------------------------------------------------------------
 *       A |- !x. (t1 = t2)
 *     ----------------------
 *     A |- (\x.t1) = (\x.t2)
 *
 * fun MK_ABS th =
 *    let val {Bvar,Body} = dest_forall(concl th)
 *        val {lhs,rhs} = dest_eq Body
 *    in
 *    make_thm Count.MkAbs(tag th, hyp th, 
 *                 mk_eq{lhs=mk_abs{Bvar=Bvar, Body=lhs},
 *                       rhs=mk_abs{Bvar=Bvar, Body=rhs}})
 *    end
 *    handle _ => THM_ERR"MK_ABS" "";
 *---------------------------------------------------------------------------*)
fun MK_ABS qth =
   let val {Bvar,Body} = dest_forall (concl qth) 
       val ufun = mk_abs{Bvar=Bvar, Body=lhs Body}
       and vfun = mk_abs{Bvar=Bvar, Body=rhs Body}
       val gv = genvar (type_of Bvar) 
   in
    EXT (GEN gv
     (TRANS (TRANS (BETA_CONV (mk_comb{Rator=ufun,Rand=gv})) (SPEC gv qth))
	    (SYM (BETA_CONV (mk_comb{Rator=vfun,Rand=gv})))))
   end
   handle HOL_ERR _ => raise DRULE_ERR"MK_ABS" "";

(*---------------------------------------------------------------------------
 *  Contradiction rule
 *
 *   A |- F
 *   ------
 *   A |- t
 *
 * fun CONTR w fth =
 *    (thm_assert ((type_of w = bool) andalso 
 *                 (concl fth = mk_const{Name="F",Ty=bool})) "CONTR" "";
 *     make_thm Count.Contr(tag fth, hyp fth, w))
 *---------------------------------------------------------------------------*)
fun CONTR tm th = MP (SPEC tm FALSITY) th 
    handle HOL_ERR _ => raise DRULE_ERR "CONTR" "";

(*---------------------------------------------------------------------------
 *  Undischarging
 *
 *   A |- t1 ==> t2
 *   -------------
 *    A, t1 |- t2
 *---------------------------------------------------------------------------*)
fun UNDISCH th = MP th (ASSUME(#ant(dest_imp(concl th))))
  handle HOL_ERR  _ => raise DRULE_ERR "UNDISCH" "";

(*---------------------------------------------------------------------------
 * =T elimination
 *
 *   A |- t = T
 *  ------------
 *    A |- t
 *---------------------------------------------------------------------------*)
fun EQT_ELIM th = EQ_MP (SYM th) TRUTH
  handle HOL_ERR _ => raise DRULE_ERR "EQT_ELIM" "";


(*---------------------------------------------------------------------------
 *
 *      |- !x1 ... xn. t[xi]
 *    --------------------------	SPECL [t1; ...; tn]
 *          |-  t[ti]
 *---------------------------------------------------------------------------*)
fun SPECL tm_list th = rev_itlist SPEC tm_list th 
  handle HOL_ERR _ => raise DRULE_ERR"SPECL" "";

val GENL = itlist GEN;


(*---------------------------------------------------------------------------
 * SELECT introduction
 *
 *    A |- P t
 *  -----------------
 *   A |- P($@ P)
 *---------------------------------------------------------------------------*)
local fun alpha_subst ty = [alpha |-> ty]
in
fun SELECT_INTRO th =
 let val {Rator, Rand} = dest_comb(concl th)
     val SELECT_AX' = INST_TYPE (alpha_subst (type_of Rand)) SELECT_AX
 in
   MP (SPEC Rand (SPEC Rator SELECT_AX')) th 
 end
 handle HOL_ERR _ => raise DRULE_ERR "SELECT_INTRO" ""
end;


(*---------------------------------------------------------------------------
 * SELECT elimination (cases)
 *
 *   A1 |- P($? P)          A2, "P v" |- t
 *  ------------------------------------------ (v occurs nowhere)
 *              A1 u A2 |- t
 *---------------------------------------------------------------------------*)
fun SELECT_ELIM th1 (v,th2) =
  let val {Rator, Rand} = dest_comb(concl th1)
      val th3 = DISCH (mk_comb{Rator = Rator, Rand = v}) th2
      (* th3 = |- P v ==> t *)
  in
  MP (SPEC Rand (GEN v th3)) th1
  end
  handle HOL_ERR _ => raise DRULE_ERR "SELECT_ELIM" "";



(*---------------------------------------------------------------------------
 * SELECT introduction
 *
 *    A |- ?x. t[x]
 *  -----------------
 *   A |- t[@x.t[x]]
 *---------------------------------------------------------------------------*)
local fun alpha_subst ty = [alpha |-> ty]
in
fun SELECT_RULE th =
   let val (tm as {Bvar, Body}) = dest_exists(concl th)
       val v = genvar(type_of Bvar)
       val P = mk_abs tm
       val SELECT_AX' = INST_TYPE(alpha_subst(type_of Bvar)) SELECT_AX
       val th1 = SPEC v (SPEC P SELECT_AX')
       val {ant,conseq} = dest_imp(concl th1)
       val th2 = BETA_CONV ant 
       and th3 = BETA_CONV conseq
       val th4 = EQ_MP th3 (MP th1 (EQ_MP(SYM th2) (ASSUME (rhs(concl th2)))))
   in
     CHOOSE (v,th) th4
   end
   handle HOL_ERR _ => raise DRULE_ERR "SELECT_RULE" ""
end;


(*---------------------------------------------------------------------------
 *               A |-  t1 = t2
 *   ------------------------------------------- (xi not free in A)
 *    A |- (?x1 ... xn. t1)  =  (?x1 ... xn. t2)
 *---------------------------------------------------------------------------*)
fun LIST_MK_EXISTS l th = itlist (fn x => fn th => MK_EXISTS(GEN x th)) l th;


(*---------------------------------------------------------------------------
 * ! abstraction
 *
 *          A |- t1 = t2
 *     -----------------------
 *      A |- (!x.t1) = (!x.t2)
 *---------------------------------------------------------------------------*)

fun FORALL_EQ x =
   let val forall = AP_TERM
             (mk_const{Name="!", Ty = (type_of x --> bool) --> bool})
   in 
     fn th => forall (ABS x th)
   end 
   handle HOL_ERR _ => raise DRULE_ERR "FORALL_EQ" "";


(*---------------------------------------------------------------------------
 * ? abstraction
 *
 *          A |- t1 = t2
 *     -----------------------
 *      A |- (?x.t1) = (?x.t2)
 *---------------------------------------------------------------------------*)
fun EXISTS_EQ x =
   let val exists = AP_TERM
             (mk_const{Name="?", Ty = (type_of x --> bool) --> bool})
   in fn th => exists (ABS x th)
   end 
   handle HOL_ERR _ => raise DRULE_ERR "EXISTS_EQ" "";


(*---------------------------------------------------------------------------
 * @ abstraction
 *
 *          A |- t1 = t2
 *     -----------------------
 *      A |- (@x.t1) = (@x.t2)
 *---------------------------------------------------------------------------*)
fun SELECT_EQ x =
 let val ty = type_of x
     val choose = mk_const{Name = "@", Ty = (ty --> bool) --> ty}
 in fn th => AP_TERM choose (ABS x th)
 end 
 handle HOL_ERR _ => raise DRULE_ERR "SELECT_EQ" "";


fun SUBS ths th = 
    GSUBS subst ths th handle HOL_ERR _ => raise DRULE_ERR "SUBS" "";

fun SUBS_OCCS nlths th =
   let val (nll, ths) = unzip nlths 
   in 
      GSUBS (subst_occs nll) ths th 
   end
   handle HOL_ERR _ => raise DRULE_ERR "SUBS_OCCS" "";


(*---------------------------------------------------------------------------
 * Beta-conversion to the rhs of an equation
 *
 *   A |- t1 = (\x.t2)t3
 *  --------------------
 *   A |- t1 = t2[t3/x]
 *---------------------------------------------------------------------------*)
fun RIGHT_BETA th = TRANS th (BETA_CONV(#rhs(dest_eq(concl th))))
  handle HOL_ERR _ => raise DRULE_ERR "RIGHT_BETA" "";

(*---------------------------------------------------------------------------
 *  "(\x1 ... xn.t)t1 ... tn" --> 
 *    |- (\x1 ... xn.t)t1 ... tn = t[t1/x1] ... [tn/xn]
 *---------------------------------------------------------------------------*)
fun LIST_BETA_CONV tm =
   let val {Rator,Rand} = dest_comb tm 
   in 
      RIGHT_BETA (AP_THM (LIST_BETA_CONV Rator) Rand)
   end 
   handle HOL_ERR _ => REFL tm;


fun RIGHT_LIST_BETA th = TRANS th (LIST_BETA_CONV(#rhs(dest_eq(concl th))));


(*---------------------------------------------------------------------------
 * let CONJUNCTS_CONV (t1,t2) =
 *  letrec CONJUNCTS th =
 *   (CONJUNCTS (CONJUNCT1 th) @ CONJUNCTS (CONJUNCT2 th)) ? [th]
 *  in
 *  letrec build_conj thl t =
 *   (let l,r = dest_conj t
 *    in  CONJ (build_conj thl l) (build_conj thl r)
 *   )
 *   ? find (\th. (concl th) = t) thl
 *  in
 *   (IMP_ANTISYM_RULE
 *     (DISCH t1 (build_conj (CONJUNCTS (ASSUME t1)) t2))
 *     (DISCH t2 (build_conj (CONJUNCTS (ASSUME t2)) t1))
 *   ) ? failwith `CONJUNCTS_CONV`;;
 *---------------------------------------------------------------------------*)

fun CONJUNCTS_CONV (t1,t2) =
   let fun CONJUNCTS th = (CONJUNCTS (CONJUNCT1 th) @ CONJUNCTS (CONJUNCT2 th))
             handle HOL_ERR _ => [th]
       fun build_conj thl t =
          let val {conj1,conj2} = dest_conj t
           in  CONJ (build_conj thl conj1) (build_conj thl conj2)
          end 
          handle HOL_ERR _ => first (fn th => (concl th) = t) thl
   in
   IMP_ANTISYM_RULE (DISCH t1 (build_conj (CONJUNCTS (ASSUME t1)) t2))
                    (DISCH t2 (build_conj (CONJUNCTS (ASSUME t2)) t1))
   end
   handle HOL_ERR _ => raise DRULE_ERR "CONJUNCTS_CONV" "";

(*---------------------------------------------------------------------------*
 * let CONJ_SET_CONV l1 l2 =                                                 *
 *  CONJUNCTS_CONV (list_mk_conj l1, list_mk_conj l2)                        *
 *  ? failwith `CONJ_SET_CONV`;;                                             *
 *---------------------------------------------------------------------------*)

fun CONJ_SET_CONV l1 l2 = 
   CONJUNCTS_CONV (list_mk_conj l1, list_mk_conj l2)
   handle HOL_ERR _ => raise DRULE_ERR "CONJ_SET_CONV" "";

(*---------------------------------------------------------------------------
 * let FRONT_CONJ_CONV tml t =
 *  letrec remove x l =
 *     if ((hd l) = x)
 *     then tl l
 *     else (hd l).(remove x (tl l))
 *  in
 *  (CONJ_SET_CONV tml (t.(remove t tml)))
 *  ? failwith `FRONT_CONJ_CONV`;;
 *---------------------------------------------------------------------------*)
fun FRONT_CONJ_CONV tml t =
   let fun remove x l = if (hd l = x) then tl l else (hd l::remove x (tl l))
   in 
     CONJ_SET_CONV tml (t::remove t tml)
   end 
   handle HOL_ERR _ => raise DRULE_ERR "FRONT_CONJ_CONV" "";

(*---------------------------------------------------------------------------
 *   |- (t1 /\ ... /\ t /\ ... /\ tn) = (t /\ t1 /\ ... /\ tn)
 * 
 * local
 * val APP_AND = AP_TERM(--`/\`--)
 * in
 * fun FRONT_CONJ_CONV tml t =
 *    if (t = hd tml)
 *    then REFL(list_mk_conj tml)
 *    else if ((null(tl(tl tml)) andalso (t = hd(tl tml))))
 *         then SPECL tml CONJ_SYM
 *         else let val th1 = APP_AND (FRONT_CONJ_CONV (tl tml) t)
 *                  val {conj1,conj2} = dest_conj(rhs(concl th1))
 *                  val {conj1 = c2, conj2 = c3} = dest_conj conj2
 *                  val th2 = AP_THM(APP_AND (SPECL[conj1,c2]CONJ_SYM)) c3
 *              in
 *              TRANS (TRANS (TRANS th1 (SPECL[conj1,c2,c3]CONJ_ASSOC)) th2)
 *                    (SYM(SPECL[c2,conj1,c3]CONJ_ASSOC))
 *              end
 *              handle _ => raise DRULE_ERR{function = "FRONT_CONJ_CONV",
 *                                          message = ""}
 * end;
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * |- (t1 /\ ... /\ tn) = (t1' /\ ... /\ tn') where {t1,...,tn}={t1',...,tn'} 
 * 
 * The genuine derived rule below only works if its argument
 * lists are the same length.
 * 
 * fun CONJ_SET_CONV l1 l2 =
 *    if (l1 = l2)
 *    then REFL(list_mk_conj l1)
 *   else if (hd l1 = hd l2)
 *        then AP_TERM (--`$/\ ^(hd l1)`--) (CONJ_SET_CONV(tl l1)(tl l2))
 *        else let val th1 = SYM(FRONT_CONJ_CONV l2 (hd l1))
 *                 val l2' = conjuncts(lhs(concl th1))
 *                 val th2 = AP_TERM (--`$/\ ^(hd l1)`--)
 *                                   (CONJ_SET_CONV(tl l1)(tl l2'))
 *             in
 *             TRANS th2 th1
 *             end
 *             handle _ => raise DRULE_ERR{function = "CONJ_SET_CONV",
 * 		                        message = ""};
 * 
 * fun CONJ_SET_CONV l1 l2 =
 *   (if (set_eq l1 l2)
 *    then mk_drule_thm([],mk_eq{lhs = list_mk_conj l1, rhs = list_mk_conj l2})
 *    else raise DRULE_ERR{function = "CONJ_SET_CONV",message = ""})
 *    handle _ => raise DRULE_ERR{function = "CONJ_SET_CONV",message = ""};
 *---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
 * |- t1 = t2  if t1 and t2 are equivalent using idempotence, symmetry and 
 *                associativity of /\. I have not (yet) coded a genuine 
 *                derivation - it would be straightforward, but tedious.
 * 
 * fun CONJUNCTS_CONV(t1,t2) =
 *    if (set_eq (strip_conj t1)(strip_conj t2))
 *    then mk_drule_thm([],mk_eq{lhs = t1, rhs = t2})
 *    else raise DRULE_ERR{function = "CONJUNCTS_CONV",message = ""};
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 *           A,t |- t1 = t2
 *    -----------------------------
 *      A |- (t /\ t1) = (t /\ t2)
 *---------------------------------------------------------------------------*)
fun CONJ_DISCH t th =
   let val {lhs,rhs} = dest_eq(concl th)
       and th1 = DISCH t th
       val left_t  = mk_conj{conj1 = t, conj2 = lhs}
       val right_t = mk_conj{conj1 = t, conj2 = rhs}
       val th2 = ASSUME left_t
       and th3 = ASSUME right_t
       val th4 = DISCH left_t
                       (CONJ (CONJUNCT1 th2)
                             (EQ_MP(MP th1 (CONJUNCT1 th2))
                                   (CONJUNCT2 th2)))
       and th5 = DISCH right_t 
                       (CONJ (CONJUNCT1 th3)
                             (EQ_MP(SYM(MP th1 (CONJUNCT1 th3)))
                                   (CONJUNCT2 th3)))
   in
     IMP_ANTISYM_RULE th4 th5
   end;

(*---------------------------------------------------------------------------
 *                    A,t1,...,tn |- t = u
 *    --------------------------------------------------------
 *      A |- (t1 /\ ... /\ tn /\ t) = (t1 /\ ... /\ tn /\ u)
 *---------------------------------------------------------------------------*)
val CONJ_DISCHL = itlist CONJ_DISCH;


(*---------------------------------------------------------------------------
 *       A,t1 |- t2                A,t |- F
 *     --------------              --------
 *     A |- t1 ==> t2               A |- ~t
 *---------------------------------------------------------------------------*)
local val falsity = --`F`--
in
fun NEG_DISCH t th =
  (if (concl th = falsity) then NOT_INTRO (DISCH t th) else DISCH t th)
  handle HOL_ERR _ => raise DRULE_ERR "NEG_DISCH" ""
end;


(*---------------------------------------------------------------------------
 *    A |- ~(t1 = t2)
 *   -----------------
 *    A |- ~(t2 = t1)
 *---------------------------------------------------------------------------*)
local fun flip {lhs,rhs} = {lhs = rhs, rhs = lhs}
in
fun NOT_EQ_SYM th =
   let val t = (mk_eq o flip o dest_eq o dest_neg o concl) th
   in
   MP (SPEC t IMP_F) (DISCH t (MP th (SYM(ASSUME t))))
   end
end;


(* ---------------------------------------------------------------------*)
(* EQF_INTRO: inference rule for introducing equality with "F".		*)
(*									*)
(* 	         ~tm							*)
(*	     -----------    EQF_INTRO					*)
(*	        tm = F							*)
(*									*)
(* [TFM 90.05.08]							*)
(* ---------------------------------------------------------------------*)

local val F = Term`F`
      val Fth = ASSUME F
in
fun EQF_INTRO th = 
   IMP_ANTISYM_RULE (NOT_ELIM th) 
                    (DISCH F (CONTR (dest_neg (concl th)) Fth))
   handle HOL_ERR _ => raise DRULE_ERR "EQF_INTRO" ""
end;

(* ---------------------------------------------------------------------*)
(* EQF_ELIM: inference rule for eliminating equality with "F".		*)
(*									*)
(*	      |- tm = F							*)
(*	     -----------    EQF_ELIM					*)
(* 	       |- ~ tm							*)
(*									*)
(* [TFM 90.08.23]							*)
(* ---------------------------------------------------------------------*)
local val check = assert ((curry (op =) "F") o #Name o dest_const)
in
fun EQF_ELIM th =
   let val {lhs,rhs} = dest_eq(concl th)
       val _ = check rhs
   in
     NOT_INTRO(DISCH lhs (EQ_MP th (ASSUME lhs)))
   end
   handle HOL_ERR _ => raise DRULE_ERR "EQF_ELIM" ""
end;


(* ---------------------------------------------------------------------*)
(* ISPEC: specialization, with type instantation if necessary.		*)
(*									*)
(*     A |- !x:ty.tm							*)
(*  -----------------------   ISPEC "t:ty'" 				*)
(*      A |- tm[t/x]							*)
(*									*)
(* (where t is free for x in tm, and ty' is an instance of ty)		*)
(* ---------------------------------------------------------------------*)
fun ISPEC t th = 
   let val {Bvar,...} = 
         dest_forall(concl th) handle HOL_ERR _ 
         => raise DRULE_ERR"ISPEC" 
                 ": input theorem not universally quantified"
       val (_,inst) = Term.match_term Bvar t handle HOL_ERR _ 
         => raise DRULE_ERR "ISPEC" 
                 ": can't type-instantiate input theorem"
   in SPEC t (INST_TYPE inst th) handle HOL_ERR _ 
         => raise DRULE_ERR "ISPEC"
                ": type variable free in assumptions"
   end;
	 
(* ---------------------------------------------------------------------*)
(* ISPECL: iterated specialization, with type instantiation if necessary.*)
(*									*)
(*        A |- !x1...xn.tm						*)
(*  ---------------------------------   ISPECL ["t1",...,"tn"]		*)
(*      A |- tm[t1/x1,...,tn/xn]					*)
(*									*)
(* (where ti is free for xi in tm)					*)
(*                                                                      *)
(* Note: the following is simpler but it doesn't work.                  *)
(*                                                                      *)
(*  fun ISPECL tms th = rev_itlist ISPEC tms th                         *)
(*                                                                      *)
(* ---------------------------------------------------------------------*)

local fun strip [] _ = []     (* Returns a list of (pat,ob) pairs. *)
        | strip (tm::tml) M = 
            let val {Bvar,Body} = dest_forall M 
            in (type_of Bvar,type_of tm)::strip tml Body   end
      fun ERR s = DRULE_ERR "ISPECL" s
      fun merge [] theta = theta
        | merge ((x as {redex,residue})::rst) theta =
          (case (subst_assoc (fn ty => (ty=redex)) theta)
           of NONE      => x::merge rst theta
            | SOME rdue => if (residue=rdue) 
                            then merge rst theta else raise ERR "")
in
fun ISPECL [] = I
  | ISPECL [tm] = ISPEC tm
  | ISPECL tms = fn th => 
       let val pairs = strip tms (concl th) 
             handle HOL_ERR _ => raise ERR"list of terms too long for theorem"
           val inst = rev_itlist (fn (pat,ob) => fn ty_theta =>
                        let val theta = Type.match_type pat ob
                        in merge theta ty_theta end) pairs []
             handle HOL_ERR _ => raise ERR"can't type-instantiate input theorem"
       in SPECL tms (INST_TYPE inst th) 
          handle HOL_ERR _ => raise ERR"type variable free in assumptions"
       end
end;


(*---------------------------------------------------------------------------
 * Generalise a theorem over all variables free in conclusion but not in hyps
 *
 *         A |- t[x1,...,xn]
 *    ----------------------------
 *     A |- !x1...xn.t[x1,...,xn]
 *---------------------------------------------------------------------------*)
fun GEN_ALL th = 
   itlist GEN (set_diff (free_vars(concl th)) 
                        (free_varsl (hyp th))) th;


(*---------------------------------------------------------------------------
 *  Discharge all hypotheses 
 * 
 *       t1, ... , tn |- t
 *  -------------------------------
 *    |- t1 ==> ... ==> tn ==> t
 * 
 * You can write a simpler version using "itlist DISCH (hyp th) th", but this
 * may discharge two equivalent (alpha-convertible) assumptions.
 *---------------------------------------------------------------------------*)
fun DISCH_ALL th = 
   case (hyp th)
    of []     => th
     | (h::_) => DISCH_ALL (DISCH h th);



(*----------------------------------------------------------------------------
 *
 *    A |- t1 ==> ... ==> tn ==> t
 *  -------------------------------
 *       A, t1, ..., tn |- t
 *---------------------------------------------------------------------------*)
fun UNDISCH_ALL th =
   if (is_imp (concl th)) then UNDISCH_ALL (UNDISCH th) else th;


(* ---------------------------------------------------------------------*)
(* SPEC_ALL : thm -> thm						*)
(*									*)
(*     A |- !x1 ... xn. t[xi]						*)
(*    ------------------------   where the xi' are distinct 		*)
(*        A |- t[xi'/xi]	 and not free in the input theorem	*)
(*									*)
(* BUGFIX: added the "distinct" part and code to make the xi's not free *)
(* in the conclusion !x1...xn.t[xi].		        [TFM 90.10.04]	*)
(*									*)
(* OLD CODE:								*)
(* 									*)
(* let SPEC_ALL th =							*)
(*     let vars,() = strip_forall(concl th) in				*)
(*     SPECL (map (variant (freesl (hyp th))) vars) th;;		*)
(* ---------------------------------------------------------------------*)

local fun f v (vs,l) = 
        let val v' = variant vs v 
        in (v'::vs, v'::l) end
in
fun SPEC_ALL th =
   let val (hvs,con) = (free_varsl ## I) (hyp th, concl th)
       val fvs = free_vars con 
       and vars = fst(strip_forall con) 
   in
     SPECL (snd(itlist f vars (hvs@fvs,[]))) th
   end
end;


(*---------------------------------------------------------------------------
 * Use the conclusion of the first theorem to delete a hypothesis of
 *   the second theorem.
 *
 *    A |- t1 	B, t1 |- t2
 *    -----------------------
 *         A u B |- t2
 *---------------------------------------------------------------------------*)
fun PROVE_HYP ath bth =  MP (DISCH (concl ath) bth) ath;


(*---------------------------------------------------------------------------
 * A |- t1/\t2  ---> A |- t1, A |- t2 
 *---------------------------------------------------------------------------*)
fun CONJ_PAIR th = (CONJUNCT1 th, CONJUNCT2 th) 
  handle HOL_ERR _ => raise DRULE_ERR "CONJ_PAIR" "";


(*---------------------------------------------------------------------------
 * ["A1|-t1"; ...; "An|-tn"]  ---> "A1u...uAn|-t1 /\ ... /\ tn", where n>0  
 *---------------------------------------------------------------------------*)
val LIST_CONJ = end_itlist CONJ ;


(*---------------------------------------------------------------------------
 * "A |- t1 /\ (...(... /\ tn)...)"   
 *   --->  
 *   [ "A|-t1"; ...; "A|-tn"],  where n>0 
 *
 *Inverse of LIST_CONJ : flattens only right conjuncts.
 *You must specify n, since tn could itself be a conjunction
 *---------------------------------------------------------------------------*)
fun CONJ_LIST 1 th = [th] |
    CONJ_LIST n th =  (CONJUNCT1 th) :: (CONJ_LIST (n-1) (CONJUNCT2 th))
      handle HOL_ERR _ => raise DRULE_ERR "CONJ_LIST" "";


(*---------------------------------------------------------------------------
 * "A |- t1 /\ ... /\ tn"   --->  [ "A|-t1"; ...; "A|-tn"],  where n>0
 *
 *Flattens out all conjuncts, regardless of grouping
 *---------------------------------------------------------------------------*)
fun CONJUNCTS th = ((CONJUNCTS (CONJUNCT1 th))@(CONJUNCTS(CONJUNCT2 th)))
  handle HOL_ERR _ => [th];

(*---------------------------------------------------------------------------
 * "|- !x. (t1 /\ ...) /\ ... (!y. ... /\ tn)" 
 *   --->  [ "|-t1"; ...; "|-tn"],  where n>0 
 *
 * Flattens out conjuncts even in bodies of forall's
 *---------------------------------------------------------------------------*)
fun BODY_CONJUNCTS th =
   if (is_forall (concl th))
   then  BODY_CONJUNCTS (SPEC_ALL th)
   else if (is_conj (concl th))
        then ((BODY_CONJUNCTS (CONJUNCT1 th))@(BODY_CONJUNCTS (CONJUNCT2 th)))
        else [th];

(*---------------------------------------------------------------------------
 * Put a theorem 
 *
 *       |- !x. t1 ==> !y. t2 ==> ... ==> tm ==>  t 
 *
 * into canonical form by stripping out quantifiers and splitting
 * conjunctions apart.
 * 
 * 	t1 /\ t2	--->		t1,   t2
 *      (t1/\t2)==>t	--->		t1==> (t2==>t)
 *      (t1\/t2)==>t	--->		t1==>t, t2==>t
 *      (?x.t1)==>t2	--->		t1[x'/x] ==> t2
 *      !x.t1		--->		t1[x'/x]
 *      (?x.t1)==>t2    --->            t1[x'/x] ==> t2)
 *---------------------------------------------------------------------------*)
fun IMP_CANON th =
   let val w = concl th
   in
   if (is_conj w)
   then ((IMP_CANON (CONJUNCT1 th))@(IMP_CANON (CONJUNCT2 th)))
   else if (is_imp w)
        then let val {ant,...} = dest_imp w 
             in
             if (is_conj ant)
             then let val {conj1,conj2} = dest_conj ant
                  in
	          IMP_CANON (DISCH conj1
                               (DISCH conj2 (MP th (CONJ (ASSUME conj1) 
                                                         (ASSUME conj2)))))
                  end
	     else if (is_disj ant)
                  then let val {disj1,disj2} = dest_disj ant
                       in
                       ((IMP_CANON (DISCH disj1 
                                          (MP th (DISJ1 (ASSUME disj1)
                                                        disj2)))) @
                        (IMP_CANON (DISCH disj2
                                          (MP th (DISJ2 disj1
                                                        (ASSUME disj2))))))
                       end
	          else if (is_exists ant)
                       then let val {Bvar,Body} = dest_exists ant 
	                        val bv' = variant (thm_free_vars th) Bvar
                                val body' = subst [Bvar |-> bv'] Body
                            in
	                    IMP_CANON (DISCH body'(MP th(EXISTS(ant, bv')
                                                              (ASSUME body'))))
                            end
                        else map (DISCH ant) (IMP_CANON (UNDISCH th))
             end
        else if (is_forall w)
             then IMP_CANON (SPEC_ALL th)
             else [th]
   end;


(*---------------------------------------------------------------------------
 *  A1 |- t1   ...   An |- tn      A |- t1==>...==>tn==>t
 *   -----------------------------------------------------
 *            A u A1 u ... u An |- t
 *---------------------------------------------------------------------------*)
val LIST_MP  = rev_itlist (fn x => fn y => MP y x) ;


(*---------------------------------------------------------------------------
 *      A |-t1 ==> t2
 *    -----------------
 *    A |-  ~t2 ==> ~t1
 *
 * Rewritten by MJCG to return "~t2 ==> ~t1" rather than "~t2 ==> t1 ==>F".
 *---------------------------------------------------------------------------*)
local val imp_th = GEN_ALL (el 5 (CONJUNCTS (SPEC_ALL IMP_CLAUSES)))
in
fun CONTRAPOS impth =
   let val {ant,conseq} = dest_imp (concl impth) 
       val notb = mk_neg conseq
   in
   DISCH notb (EQ_MP (SPEC ant imp_th)
                     (DISCH ant (MP (ASSUME notb)
                                    (MP impth (ASSUME ant)))))
   end
   handle HOL_ERR _ => raise DRULE_ERR "CONTRAPOS" ""
end;


(*---------------------------------------------------------------------------
 *      A |- t1 \/ t2
 *   --------------------
 *     A |-  ~ t1 ==> t2
 *
 *---------------------------------------------------------------------------*)
fun DISJ_IMP dth =
   let val {disj1,disj2} = dest_disj (concl dth)
       val nota = mk_neg disj1
   in
   DISCH nota
        (DISJ_CASES dth (CONTR disj2 (MP (ASSUME nota) (ASSUME disj1)))
                        (ASSUME disj2))
   end
   handle HOL_ERR _ => raise DRULE_ERR "DISJ_IMP" "";


(*---------------------------------------------------------------------------
 *  A |- t1 ==> t2
 *  ---------------
 *   A |- ~t1 \/ t2
 *---------------------------------------------------------------------------*)
fun IMP_ELIM th =
   let val {ant,conseq} = dest_imp (concl th)
       val not_t1 = mk_neg ant
   in
   DISJ_CASES (SPEC ant EXCLUDED_MIDDLE)
              (DISJ2 not_t1 (MP th (ASSUME ant)))
              (DISJ1 (ASSUME not_t1) conseq)
   end
   handle HOL_ERR _ => raise DRULE_ERR "IMP_ELIM" "";


(*---------------------------------------------------------------------------
 *  A |- t1 \/ t2     A1, t1 |- t3      A2, t2 |- t4
 *   ------------------------------------------------
 *                A u A1 u A2 |- t3 \/ t4
 *---------------------------------------------------------------------------*)
fun DISJ_CASES_UNION dth ath bth =
    DISJ_CASES dth (DISJ1 ath (concl bth)) (DISJ2 (concl ath) bth);


(*---------------------------------------------------------------------------
 *
 *       |- A1 \/ ... \/ An     [A1 |- M, ..., An |- M]
 *     ---------------------------------------------------
 *                           |- M
 *
 * The order of the theorems in the list doesn't matter: an operation akin
 * to sorting lines them up with the disjuncts in the theorem.
 *---------------------------------------------------------------------------*)

local fun organize eq =    (* a bit slow - analogous to insertion sort *)
        let fun extract a alist =
              let fun ex (_,[]) = raise DRULE_ERR
                         "DISJ_CASESL.organize" "not a permutation.1"
                    | ex(left,h::t) = 
                         if (eq h a) then (h,rev left@t) else ex(h::left,t)
              in ex ([],alist) 
              end
            fun place [] [] = []
               | place (a::rst) alist =
                  let val (item,next) = extract a alist
                  in item::place rst next
                  end
               | place _ _ = raise DRULE_ERR
                    "DISJ_CASESL.organize" "not a permutation.2"
        in place
        end
in
fun DISJ_CASESL disjth thl =
 let val (_,c) = dest_thm disjth
     fun eq th atm = exists (aconv atm) (#1(dest_thm th))
     val tml = strip_disj c
     fun DL th [] = raise DRULE_ERR"DISJ_CASESL" "no cases"
       | DL th [th1] = PROVE_HYP th th1
       | DL th [th1,th2] = DISJ_CASES th th1 th2
       | DL th (th1::rst) = DISJ_CASES th th1 
                               (DL(ASSUME(#disj2(dest_disj(concl th)))) rst)
 in DL disjth (organize eq tml thl)
end end;

(*---------------------------------------------------------------------------
 * Forward chain using an inference rule on top-level sub-parts of a theorem
 * Could be extended to handle other connectives
 * Commented out.
 *
 *fun SUB_CHAIN rule th =
 *   let val w = concl th 
 *   in
 *   if (is_conj w)
 *   then CONJ (rule(CONJUNCT1 th)) (rule(CONJUNCT2 th))
 *   else if (is_disj w)
 *        then let val (a,b) = dest_disj w 
 *             in	
 *             DISJ_CASES_UNION th (rule (ASSUME a)) (rule (ASSUME b))
 *             end
 *        else if (is_imp w)
 *             then let val (a,b) = dest_imp w 
 *                  in  
 *                  DISCH a (rule (UNDISCH th))
 *                  end
 *             else if (is_forall w)
 *                  then let val (x', sth) = SPEC_VAR th 
 *                       in
 *	               GEN x' (rule sth)
 *                       end
 *                  else th
 *   end;
 *
 *infix thenf orelsef;
 *fun f thenf g = fn x => g(f x);
 *fun f orelsef g = (fn x => (f x) handle _ => (g x));
 *
 *(* Repeatedly apply the rule (looping if it never fails) *)
 *fun REDEPTH_CHAIN rule x =
 *   (SUB_CHAIN (REDEPTH_CHAIN rule) thenf
 *    ((rule thenf (REDEPTH_CHAIN rule)) orelsef I))
 *   x;
 *
 *
 *(* Apply the rule no more than once in any one place *)
 *fun ONCE_DEPTH_CHAIN rule x =
 *   (rule  orelsef  SUB_CHAIN (ONCE_DEPTH_CHAIN rule))
 *   x;
 *
 *
 *(* "depth SPEC" : Specialize a theorem whose quantifiers are buried inside *)
 *fun DSPEC x = ONCE_DEPTH_CHAIN (SPEC x);
 *val DSPECL = rev_itlist DSPEC;
 *
 *val CLOSE_UP = GEN_ALL o DISCH_ALL;
 *---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
 *     A |- !x. t1 x = t2
 *     ------------------
 *      A |-  t1 = \x.t2
 *
 *fun HALF_MK_ABS qth =
 *   let val {Bvar,Body} = dest_forall (concl qth) 
 *       val t = rhs Body
 *       and gv = genvar (type_of Bvar) 
 *       val tfun = mk_abs{Bvar = Bvar, Body = t}
 *   in
 *   EXT (GEN gv 		(* |- !gv. u gv =< (\x.t) gv  *)
 *	 (TRANS (SPEC gv qth)
 *                (SYM (BETA_CONV (mk_comb{Rator = tfun, Rand = gv})))))
 *   end
 *   handle _ => raise DRULE_ERR{function = "HALF_MK_ABS",message = ""};
 *---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
 * Rename the bound variable of a lambda-abstraction
 *
 *       "x"   "(\y.t)"   --->   |- "\y.t = \x. t[x/y]"  
 *
 *---------------------------------------------------------------------------*)

fun ALPHA_CONV x t =
   let val x' = variant (free_vars t) x
       val cmb = mk_comb{Rator = t, Rand = x'}
       val th1 = SYM(ETA_CONV(mk_abs{Bvar = x', Body = cmb}))
       and th2 = ABS x' (BETA_CONV cmb)
   in
     TRANS th1 th2
   end
   handle HOL_ERR _ => raise DRULE_ERR "ALPHA_CONV" "";


(*----------------------------------------------------------------------------
 * Version of  ALPHA_CONV that renames "x" when necessary, but then it doesn't
 * meet the specification. Is that really a problem? Notice that this version 
 * of ALPHA_CONV is more efficient.
 *
 *fun ALPHA_CONV x t = 
 *  if (Term.free_in x t)
 *  then ALPHA_CONV (variant (free_vars t) x) t
 *  else ALPHA t (mk_abs{Bvar = x,
 *                       Body = Term.beta_conv(mk_comb{Rator = t,Rand = x})});
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * Rename bound variables
 *
 *       "x"   "(\y.t)"   --->    |- "\y.t  = \x. t[x/y]"  
 *       "x"   "(!y.t)"   --->    |- "!y.t  = !x. t[x/y]"  
 *       "x"   "(?y.t)"   --->    |- "?y.t  = ?x. t[x/y]"  
 *       "x"   "(?!y.t)"  --->    |- "?!y.t = ?!x. t[x/y]"  
 *       "x"   "(@y.t)"   --->    |- "@y.t  = @x. t[x/y]"  
 *---------------------------------------------------------------------------*)
local val check = assert (Theory.is_binder o #Name o dest_const)
in
fun GEN_ALPHA_CONV x t =
   if (is_abs t) 
   then ALPHA_CONV x t 
   else let val {Rator, Rand} = dest_comb t
            val _ = check Rator
        in
          AP_TERM Rator (ALPHA_CONV x Rand)
        end
        handle HOL_ERR _ => raise DRULE_ERR "GEN_ALPHA_CONV" ""
end;


(* ---------------------------------------------------------------------*)
(* IMP_CONJ implements the following derived inference rule:		*)
(*									*)
(*  A1 |- P ==> Q    A2 |- R ==> S					*)
(* --------------------------------- IMP_CONJ				*)
(*   A1 u A2 |- P /\ R ==> Q /\ S					*)
(* ---------------------------------------------------------------------*)

fun IMP_CONJ th1 th2 = 
    let val {ant = A1, ...} = dest_imp (concl th1) 
        and {ant = A2, ...} = dest_imp (concl th2)
        val conj = mk_conj{conj1 = A1, conj2 = A2}
        val (a1,a2) = CONJ_PAIR (ASSUME conj)
    in
      DISCH conj (CONJ (MP th1 a1) (MP th2 a2))
    end;

(* ---------------------------------------------------------------------*)
(* EXISTS_IMP : existentially quantify the antecedent and conclusion 	*)
(* of an implication.							*)
(*									*)
(*        A |- P ==> Q							*)
(* -------------------------- EXISTS_IMP `x`				*)
(*   A |- (?x.P) ==> (?x.Q)						*)
(*									*)
(* ---------------------------------------------------------------------*)

fun EXISTS_IMP x th =
    if not (is_var x)
    then raise DRULE_ERR "EXISTS_IMP" "first argument not a variable"
    else let val {ant,conseq} = dest_imp(concl th)
             val th1 = EXISTS (mk_exists{Bvar=x, Body=conseq},x) (UNDISCH th) 
             val asm = mk_exists{Bvar=x, Body=ant}
         in
           DISCH asm (CHOOSE (x,ASSUME asm) th1)
         end
         handle HOL_ERR _ => raise DRULE_ERR "EXISTS_IMP"
                                 "variable free in assumptions";

end; (* Drule *)
