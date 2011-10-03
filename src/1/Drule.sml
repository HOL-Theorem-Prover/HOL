(* ===================================================================== *)
(* FILE          : Drule.sml                                             *)
(* DESCRIPTION   : Derived theorems and rules. Largely translated from   *)
(*                 hol88.                                                *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon and                                   *)
(*                     Tom Melham, University of Cambridge, for hol88    *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* ===================================================================== *)

structure Drule :> Drule =
struct

open Feedback HolKernel Parse boolTheory boolSyntax Abbrev;

val +++ = Lib.+++
val +-+ = Lib.+-+
infix +++ +-+

val ERR = mk_HOL_ERR "Drule";

(*---------------------------------------------------------------------------*
 * Aligning the ranks and kinds of type substitutions on a theorem.          *
 * INST_ALL does the instantiations in one pass through the term.            *
 *---------------------------------------------------------------------------*)

fun INST_RK_KD(Srk,Skd) = INST_ALL([],[],Skd,Srk)
fun INST_RK_KD_TY(Srk,Skd,Sty) = INST_ALL([],Sty,Skd,Srk)

(*---------------------------------------------------------------------------*
 * Eta-conversion                                                            *
 *                                                                           *
 * 	"(\x.t x)"   --->    |- (\x.t x) = t  (if x not free in t)           *
 *---------------------------------------------------------------------------*)

(* Cursory profiling indicates that an implementation of ETA_CONV as a
   primitive inference rule in Thm is about 20 times faster than this
   implementation, which instantiates ETA_AX.  The difference in overall
   HOL build time, however, is negligible. *)

fun ETA_CONV t =
  let val (var, cmb) = dest_abs t
      val tysubst = [alpha |-> type_of var, beta |-> type_of cmb]
      val th = SPEC (rator cmb) (INST_TYPE tysubst ETA_AX)
  in
    TRANS (ALPHA t (lhs (concl th))) th
  end
  handle HOL_ERR _ => raise ERR "ETA_CONV" ""

(*---------------------------------------------------------------------------*
 * Type-eta-conversion                                                       *
 *                                                                           *
 * 	"(\:a.t [:a:])"   --->    |- (\:a.t [:a:]) = t  (if a not free in t) *
 *---------------------------------------------------------------------------*)

fun TY_ETA_CONV t =
  let val (tyvar, tycmb) = dest_tyabs t
      val ty      = type_of tycmb
      val rk      = rank_of_type ty
      val uvar    = fst (dest_univ_type (type_of (fst (dest_tycomb tycmb))))
      val b_rk    = 1 (*'b*)
      val rksubst = Rank.raw_match_rank false b_rk rk (rank_of_type uvar)
      val kd      = kind_of tyvar
      val kappa'  = Kind.inst_rank rksubst kappa
      val kdsubst = if kd = kappa' then [] else [kappa' |-> kd]
      val bty     = mk_var_type("'b", kd ==> typ (Rank.promote rksubst b_rk))
      val tysubst = [bty |-> mk_abs_type(tyvar, ty)]
(* The code above essentially does the following, quickly:
      val pat = lhs (snd (dest_forall (concl TY_ETA_AX)))
      val (tmsubst, tysubst, kdsubst, rksubst) = kind_match_term pat t
*)
(* old version:
      val rk      = Int.max(rank_of ty - 1, 0)
      val kd      = kind_of tyvar
      val kdsubst = if kd = kappa then [] else [kappa |-> kd]
      val tysubst = [mk_var_type("'b", kd ==> typ, rk+1) |-> mk_abs_type(tyvar, ty)]
*)
      val th = SPEC (tyrator tycmb)
                 (INST_RK_KD_TY (rksubst,kdsubst,tysubst)  TY_ETA_AX)
              (* (PURE_INST_TYPE tysubst (INST_KIND kdsubst (INST_RANK rksubst TY_ETA_AX))) *)
  in
    TRANS (ALPHA t (lhs (concl th))) th
  end
  handle HOL_ERR _ => raise ERR "TY_ETA_CONV" "";


(*---------------------------------------------------------------------------*
 *  Beta-reduce all types within the goal                                    *
 *                                                                           *
 *      A |- t                                                               *
 *   -----------                                                             *
 *      A |- t'   (where t' is t but with all types beta-reduced)            *
 *---------------------------------------------------------------------------*)

fun BETA_TY_RULE th = let val t = concl th
                          val t' = beta_conv_ty_in_term t
                      in EQ_MP (ALPHA t t') th
                      end


(*---------------------------------------------------------------------------*
 *    A |- t = (\x.f x)                                                      *
 *  --------------------- x not free in f                                    *
 *     A |- t = f                                                            *
 *---------------------------------------------------------------------------*)

fun RIGHT_ETA thm =
  TRANS thm (ETA_CONV (rhs (concl thm)))
  handle HOL_ERR _ => raise ERR "RIGHT_ETA" ""

(*---------------------------------------------------------------------------*
 *  Add an assumption                                                        *
 *                                                                           *
 *      A |- t'                                                              *
 *   -----------                                                             *
 *    A,t |- t'                                                              *
 *---------------------------------------------------------------------------*)

fun ADD_ASSUM t th = MP (DISCH t th) (ASSUME t)

(*---------------------------------------------------------------------------*
 * Transitivity of ==>                                                       *
 *                                                                           *
 *   A1 |- t1 ==> t2            A2 |- t2 ==> t3                              *
 * ---------------------------------------------                             *
 *           A1 u A2 |- t1 ==> t3                                            *
 *---------------------------------------------------------------------------*)

fun IMP_TRANS th1 th2 =
   let val (ant,conseq) = dest_imp(concl th1)
   in DISCH ant (MP th2 (MP th1 (ASSUME ant)))
   end
   handle HOL_ERR _ => raise ERR "IMP_TRANS" ""

(*---------------------------------------------------------------------------*
 *   A1 |- t1 ==> t2         A2 |- t2 ==> t1                                 *
 *  -----------------------------------------                                *
 *            A1 u A2 |- t1 = t2                                             *
 *---------------------------------------------------------------------------*)

 fun IMP_ANTISYM_RULE th1 th2 =
    let val (ant,conseq) = dest_imp(concl th1)
    in MP (MP (SPEC conseq (SPEC ant IMP_ANTISYM_AX)) th1) th2
    end
    handle HOL_ERR _ => raise ERR "IMP_ANTISYM_RULE" ""

(*---------------------------------------------------------------------------*
 * Introduce  =T                                                             *
 *                                                                           *
 *     A |- t                                                                *
 *   ------------                                                            *
 *     A |- t=T                                                              *
 *---------------------------------------------------------------------------*)

local val eq_thm =
        let val (Bvar,_) = dest_forall (concl boolTheory.EQ_CLAUSES)
            val thm = CONJUNCT1(CONJUNCT2 (SPEC Bvar boolTheory.EQ_CLAUSES))
        in GEN Bvar (SYM thm)
        end
in
fun EQT_INTRO th = EQ_MP (SPEC (concl th) eq_thm) th
                   handle HOL_ERR _ => raise ERR "EQT_INTRO" ""
end

(*---------------------------------------------------------------------------*
 *  |- !x. t    ---->    x', |- t[x'/x]                                      *
 *---------------------------------------------------------------------------*)

fun SPEC_VAR th =
   let val (Bvar,_) = dest_forall (concl th)
       val bv' = prim_variant (HOLset.listItems (hyp_frees th)) Bvar
   in (bv', SPEC bv' th)
   end

(*---------------------------------------------------------------------------
 *  |- !:a. t    ---->    a', |- t[a'/a]
 *---------------------------------------------------------------------------*)

fun TY_SPEC_VAR th =
   let val (Bvar,_) = dest_tyforall (concl th)
       val bv' = prim_variant_type (HOLset.listItems (hyp_tyvars th)) Bvar
   in (bv', TY_SPEC bv' th)
   end;

fun TY_TM_SPEC_VAR th =
  let val (x, sth) = SPEC_VAR th
  in (inR x, sth)
  end
  handle HOL_ERR _ =>
  let val (a, sth) = TY_SPEC_VAR th
  in (inL a, sth)
  end
  handle HOL_ERR _ => raise ERR "TY_TM_SPEC_VAR" "";

(*---------------------------------------------------------------------------*
 *       A |-  (!x. t1 = t2)                                                 *
 *   ---------------------------                                             *
 *    A |- (?x.t1)  =  (?x.t2)                                               *
 *---------------------------------------------------------------------------*)

fun MK_EXISTS bodyth =
 let val (x, sth) = SPEC_VAR bodyth
     val (a,b) = dest_eq (concl sth)
     val (abimp,baimp) = EQ_IMP_RULE sth
     fun HALF (p,q) pqimp =
       let val xp = mk_exists(x,p)
           and xq = mk_exists(x,q)
       in DISCH xp (CHOOSE (x,ASSUME xp) (EXISTS (xq,x) (MP pqimp (ASSUME p))))
       end
 in
    IMP_ANTISYM_RULE (HALF (a,b) abimp) (HALF (b,a) baimp)
 end
 handle HOL_ERR _ => raise ERR "MK_EXISTS" ""

(*---------------------------------------------------------------------------*
 *       A |-  (!:a. t1 = t2)                                                *
 *   ---------------------------                                             *
 *    A |- (?:a.t1)  =  (?:a.t2)                                             *
 *---------------------------------------------------------------------------*)

fun MK_TY_EXISTS bodyth =
 let val (x, sth) = TY_SPEC_VAR bodyth
     val (a,b) = dest_eq (concl sth)
     val (abimp,baimp) = EQ_IMP_RULE sth
     fun HALF (p,q) pqimp =
       let val xp = mk_tyexists(x,p)
           and xq = mk_tyexists(x,q)
       in DISCH xp (TY_CHOOSE (x,ASSUME xp) (TY_EXISTS (xq,x) (MP pqimp (ASSUME p))))
       end
 in
    IMP_ANTISYM_RULE (HALF (a,b) abimp) (HALF (b,a) baimp)
 end
 handle HOL_ERR _ => raise ERR "MK_TY_EXISTS" "";

fun MK_TY_TM_EXISTS th = MK_EXISTS th handle HOL_ERR _ => MK_TY_EXISTS th;


(*---------------------------------------------------------------------------*
 *               A |-  t1 = t2                                               *
 *   ------------------------------------------- (xi not free in A)          *
 *    A |- (?x1 ... xn. t1)  =  (?x1 ... xn. t2)                             *
 *---------------------------------------------------------------------------*)

fun LIST_MK_EXISTS l th = itlist (fn x => fn th => MK_EXISTS(GEN x th)) l th


(*---------------------------------------------------------------------------*
 *                A |-  t1 = t2                                              *
 *   ---------------------------------------------- (ai not free in A)       *
 *    A |- (?:a1 ... an. t1)  =  (?:a1 ... an. t2)                           *
 *---------------------------------------------------------------------------*)

fun LIST_MK_TY_EXISTS l th = itlist (fn x => fn th => MK_TY_EXISTS(TY_GEN x th)) l th;

fun LIST_MK_TY_TM_EXISTS l th =
  itlist (fn (inL a) => (fn th => MK_TY_EXISTS(TY_GEN a th))
           | (inR x) => (fn th =>    MK_EXISTS(   GEN x th))) l th;


fun SIMPLE_EXISTS v th = EXISTS (mk_exists(v, concl th), v) th

fun SIMPLE_TY_EXISTS v th = TY_EXISTS (mk_tyexists(v, concl th), v) th

fun SIMPLE_TY_TM_EXISTS (inL a) th = SIMPLE_TY_EXISTS a th
  | SIMPLE_TY_TM_EXISTS (inR v) th =    SIMPLE_EXISTS v th;

fun SIMPLE_CHOOSE v th =
  case HOLset.find (fn _ => true) (Thm.hypset th) of
    SOME h => CHOOSE(v, ASSUME (boolSyntax.mk_exists(v,h))) th
  | NONE => raise ERR "SIMPLE_CHOOSE" ""

fun SIMPLE_TY_CHOOSE v th =
  case HOLset.find (fn _ => true) (Thm.hypset th) of
    SOME h => TY_CHOOSE(v, ASSUME (boolSyntax.mk_tyexists(v,h))) th
  | NONE => raise ERR "SIMPLE_TY_CHOOSE" "";

fun SIMPLE_TY_TM_CHOOSE (inL a) th = SIMPLE_TY_CHOOSE a th
  | SIMPLE_TY_TM_CHOOSE (inR v) th =    SIMPLE_CHOOSE v th;

(*---------------------------------------------------------------------------*
 *     A1 |- t1 = u1   ...   An |- tn = un       A |- t[ti]                  *
 *    -------------------------------------------------------                *
 *               A1 u ... An u A |-  t[ui]                                   *
 *---------------------------------------------------------------------------*)

local fun combine [] [] = []
        | combine (v::rst1) (t::rst2) = (v |-> t) :: combine rst1 rst2
        | combine _ _ = raise ERR "GSUBS.combine" "Different length lists"
in
fun GSUBS substfn ths th =
   let val ls = map (lhs o concl) ths
       val vars = map (genvar o type_of) ls
       val w = substfn (combine ls vars) (concl th)
   in
     SUBST (combine vars ths) w th
   end
end

fun SUBS ths th = GSUBS subst ths th handle HOL_ERR _ => raise ERR "SUBS" ""

fun SUBS_OCCS nlths th =
   let val (nll, ths) = unzip nlths
   in GSUBS (subst_occs nll) ths th
   end handle HOL_ERR _ => raise ERR "SUBS_OCCS" ""

(*---------------------------------------------------------------------------*
 *       A |- ti == ui                                                       *
 *    --------------------                                                   *
 *     A |- t[ti] = t[ui]                                                    *
 *---------------------------------------------------------------------------*)

fun SUBST_CONV theta template tm =
  let fun retheta {redex,residue} = (redex |-> genvar(type_of redex))
      val theta0 = map retheta theta
      val theta1 = map (op |-> o (#residue ## #residue)) (zip theta0 theta)
  in
   SUBST theta1 (mk_eq(tm,subst theta0 template)) (REFL tm)
  end
  handle HOL_ERR _ => raise ERR "SUBST_CONV" ""

(*---------------------------------------------------------------------------*
 * Extensionality                                                            *
 *                                                                           *
 *     A |- !x. t1 x = t2 x                                                  *
 *    ----------------------     (x not free in A, t1 or t2)                 *
 *        A |- t1 = t2                                                       *
 *---------------------------------------------------------------------------*)

fun EXT th =
   let val (Bvar,_) = dest_forall(concl th)
       val th1 = SPEC Bvar th
       (* th1 = |- t1 x = t2 x *)
       val (t1x, t2x) = dest_eq(concl th1)
       val x = rand t1x
       val th2 = ABS x th1
       (* th2 = |- (\x. t1 x) = (\x. t2 x) *)
   in
   TRANS (TRANS(SYM(ETA_CONV (mk_abs(x, t1x)))) th2)
         (ETA_CONV (mk_abs(x,t2x)))
   end
   handle HOL_ERR _ => raise ERR "EXT" ""


(*---------------------------------------------------------------------------*
 * Type extensionality                                                       *
 *                                                                           *
 *     A |- !:a. t1 [:a:] = t2 [:a:]                                         *
 *    -------------------------------     (a not free in A, t1 or t2)        *
 *             A |- t1 = t2                                                  *
 *---------------------------------------------------------------------------*)

fun TY_EXT th =
   let val (Bvar,_) = dest_tyforall(concl th)
       val th1 = TY_SPEC Bvar th
       (* th1 = |- t1 [:a:] = t2 [:a:] *)
       val (t1x, t2x) = dest_eq(concl th1)
       val x = snd(dest_tycomb t1x)
       val th2 = TY_ABS x th1
       (* th2 = |- (\:a. t1 [:a:]) = (\:a. t2 [:a:]) *)
   in
   TRANS (TRANS(SYM(TY_ETA_CONV (mk_tyabs(x, t1x)))) th2)
         (TY_ETA_CONV (mk_tyabs(x,t2x)))
   end
   handle HOL_ERR _ => raise ERR "TY_EXT" "";


(*---------------------------------------------------------------------------*
 *       A |- !x. (t1 = t2)                                                  *
 *     ----------------------                                                *
 *     A |- (\x.t1) = (\x.t2)                                                *
 *---------------------------------------------------------------------------*)

fun MK_ABS qth =
   let val (Bvar,Body) = dest_forall (concl qth)
       val ufun = mk_abs(Bvar, lhs Body)
       and vfun = mk_abs(Bvar, rhs Body)
       val gv = genvar (type_of Bvar)
   in
    EXT (GEN gv
     (TRANS (TRANS (BETA_CONV (mk_comb(ufun,gv))) (SPEC gv qth))
	    (SYM (BETA_CONV (mk_comb(vfun,gv))))))
   end
   handle HOL_ERR _ => raise ERR "MK_ABS" ""


(*---------------------------------------------------------------------------*
 *        A |- !:a. (t1 = t2)                                                *
 *     ------------------------                                              *
 *     A |- (\:a.t1) = (\:a.t2)                                              *
 *---------------------------------------------------------------------------*)

fun MK_TY_ABS qth =
   let val (Bvar,Body) = dest_tyforall (concl qth)
       val ufun = mk_tyabs(Bvar, lhs Body)
       and vfun = mk_tyabs(Bvar, rhs Body)
       val gv = gen_var_type (kind_of Bvar)
   in
    TY_EXT (TY_GEN gv
     (TRANS (TRANS (TY_BETA_CONV (mk_tycomb(ufun,gv))) (TY_SPEC gv qth))
	    (SYM (TY_BETA_CONV (mk_tycomb(vfun,gv))))))
   end
   handle HOL_ERR _ => raise ERR"MK_TY_ABS" "";


(*---------------------------------------------------------------------------*
 *  Contradiction rule                                                       *
 *                                                                           *
 *   A |- F                                                                  *
 *   ------                                                                  *
 *   A |- t                                                                  *
 *---------------------------------------------------------------------------*)

fun CONTR tm th =
  MP (SPEC tm FALSITY) th handle HOL_ERR _ => raise ERR "CONTR" ""

(*---------------------------------------------------------------------------*
 *  Undischarging                                                            *
 *                                                                           *
 *   A |- t1 ==> t2                                                          *
 *   --------------                                                          *
 *    A, t1 |- t2                                                            *
 *---------------------------------------------------------------------------*)

fun UNDISCH th =
  MP th (ASSUME(fst(dest_imp(concl th))))
  handle HOL_ERR  _ => raise ERR "UNDISCH" ""

(*---------------------------------------------------------------------------*
 * =T elimination                                                            *
 *                                                                           *
 *   A |- t = T                                                              *
 *  ------------                                                             *
 *    A |- t                                                                 *
 *---------------------------------------------------------------------------*)

fun EQT_ELIM th =
  EQ_MP (SYM th) TRUTH handle HOL_ERR _ => raise ERR "EQT_ELIM" ""

(*---------------------------------------------------------------------------*
 *      |- !x1 ... xn. t[xi]                                                 *
 *    --------------------------	SPECL [t1, ..., tn]                  *
 *          |-  t[ti]                                                        *
 *---------------------------------------------------------------------------*)

fun SPECL tml th =
  rev_itlist SPEC tml th handle HOL_ERR _ => raise ERR "SPECL" ""

(*---------------------------------------------------------------------------*
 *      |- !:a1 ... an. t[ai]                                                *
 *    --------------------------	TY_SPECL [ty1; ...; tyn]             *
 *          |-  t[tyi]                                                       *
 *---------------------------------------------------------------------------*)

fun TY_SPECL tyl th =
  rev_itlist TY_SPEC tyl th handle HOL_ERR _ => raise ERR "TY_SPECL" "";

fun TY_TM_SPEC (inL ty) = TY_SPEC ty
  | TY_TM_SPEC (inR tm) =    SPEC tm

fun TY_TM_SPECL tyml th =
  rev_itlist TY_TM_SPEC tyml th handle e => raise wrap_exn "Drule" "TY_TM_SPECL" e;

(*---------------------------------------------------------------------------*
 *          |- t[tyi]                                                        *
 *    --------------------------	TY_GENL [ty1; ...; tyn]              *
 *      |-  !:a1 ... an. t[ai]                                               *
 *---------------------------------------------------------------------------*)

fun TY_GENL tyl th =
  itlist TY_GEN tyl th handle HOL_ERR _ => raise ERR "TY_GENL" "";

fun TY_TM_GEN (inL ty) = TY_GEN ty
  | TY_TM_GEN (inR tm) =    GEN tm

fun TY_TM_GENL tyl th =
  itlist TY_TM_GEN tyl th handle e => raise wrap_exn "Drule" "TY_TM_GENL" e;


(*---------------------------------------------------------------------------*
 * SELECT introduction
 *
 *    A |- P t
 *  -----------------
 *   A |- P($@ P)
 *---------------------------------------------------------------------------*)

fun SELECT_INTRO th =
 let val (Rator, Rand) = dest_comb(concl th)
     val SELECT_AX' = INST_TYPE [alpha |-> type_of Rand] SELECT_AX
 in
   MP (SPEC Rand (SPEC Rator SELECT_AX')) th
 end
 handle HOL_ERR _ => raise ERR "SELECT_INTRO" ""

(* ----------------------------------------------------------------------
    SELECT elimination (cases)

     A1 |- P($@ P)          A2, "P v" |- t
    ------------------------------------------ (v occurs nowhere else in th2)
                A1 u A2 |- t

    In line with the documentation in REFERENCE, this function succeeds even
    if v occurs in t (giving a rather useless result).  It also succeeds no
    matter what the rand of the conclusion of th1 is.

   ---------------------------------------------------------------------- *)

fun SELECT_ELIM th1 (v,th2) =
  let val (Rator, Rand) = dest_comb(concl th1)
      val th3 = DISCH (mk_comb(Rator, v)) th2
      (* th3 = |- P v ==> t *)
  in
  MP (SPEC Rand (GEN v th3)) th1
  end
  handle HOL_ERR _ => raise ERR "SELECT_ELIM" ""

(*---------------------------------------------------------------------------
 * SELECT introduction
 *
 *    A |- ?x. t[x]
 *  -----------------
 *   A |- t[@x.t[x]]
 *---------------------------------------------------------------------------*)

fun SELECT_RULE th =
   let val (tm as (Bvar,Body)) = dest_exists(concl th)
       val v = genvar(type_of Bvar)
       val P = mk_abs (Bvar,Body)
       val SELECT_AX' = INST_TYPE [alpha |-> type_of Bvar] SELECT_AX
       val th1 = SPEC v (SPEC P SELECT_AX')
       val (ant,conseq) = dest_imp(concl th1)
       val th2 = BETA_CONV ant
       and th3 = BETA_CONV conseq
       val th4 = EQ_MP th3 (MP th1 (EQ_MP(SYM th2) (ASSUME (rhs(concl th2)))))
   in
     CHOOSE (v,th) th4
   end
   handle HOL_ERR _ => raise ERR "SELECT_RULE" ""

(*---------------------------------------------------------------------------
 * ! abstraction
 *
 *          A |- t1 = t2
 *     -----------------------
 *      A |- (!x.t1) = (!x.t2)
 *---------------------------------------------------------------------------*)

fun FORALL_EQ x =
  let val forall = AP_TERM (inst [alpha |-> type_of x] boolSyntax.universal)
  in fn th => forall (ABS x th)
  end
  handle HOL_ERR _ => raise ERR "FORALL_EQ" ""

(*---------------------------------------------------------------------------
 * !: abstraction
 *
 *           A |- t1 = t2
 *     --------------------------
 *      A |- (!:a.t1) = (!:a.t2)
 *---------------------------------------------------------------------------*)

fun TY_FORALL_EQ a =
  let val tyforall = AP_TERM boolSyntax.ty_universal
  in fn th => tyforall (TY_ABS a th)
  end
  handle HOL_ERR _ => raise ERR "TY_FORALL_EQ" "";


(*---------------------------------------------------------------------------
 * ? abstraction
 *
 *          A |- t1 = t2
 *     -----------------------
 *      A |- (?x.t1) = (?x.t2)
 *---------------------------------------------------------------------------*)

fun EXISTS_EQ x =
  let val exists = AP_TERM (inst [alpha |-> type_of x] boolSyntax.existential)
   in fn th => exists (ABS x th)
   end
   handle HOL_ERR _ => raise ERR "EXISTS_EQ" ""

(*---------------------------------------------------------------------------
 * ?: abstraction
 *
 *           A |- t1 = t2
 *     --------------------------
 *      A |- (?:a.t1) = (?:a.t2)
 *---------------------------------------------------------------------------*)

fun TY_EXISTS_EQ a =
  let val tyexists = AP_TERM boolSyntax.ty_existential
   in fn th => tyexists (TY_ABS a th)
   end
   handle HOL_ERR _ => raise ERR "TY_EXISTS_EQ" "";


(*---------------------------------------------------------------------------
 * @ abstraction
 *
 *          A |- t1 = t2
 *     -----------------------
 *      A |- (@x.t1) = (@x.t2)
 *---------------------------------------------------------------------------*)

fun SELECT_EQ x =
 let val ty = type_of x
     val choose = inst [alpha |-> ty] boolSyntax.select
 in fn th => AP_TERM choose (ABS x th)
 end
 handle HOL_ERR _ => raise ERR "SELECT_EQ" ""

(*---------------------------------------------------------------------------
 * Beta-conversion to the rhs of an equation
 *
 *   A |- t1 = (\x.t2)t3
 *  --------------------
 *   A |- t1 = t2[t3/x]
 *---------------------------------------------------------------------------*)

fun RIGHT_BETA th =
 TRANS th (BETA_CONV(rhs(concl th)))
 handle HOL_ERR _ => raise ERR "RIGHT_BETA" ""

(*---------------------------------------------------------------------------
 * Type beta-conversion to the rhs of an equation
 *
 *   A |- t1 = (\:a.t2) [:ty:]
 *  --------------------
 *   A |- t1 = t2[ty/a]
 *---------------------------------------------------------------------------*)

fun RIGHT_TY_BETA th =
 TRANS th (TY_BETA_CONV(rhs(concl th)))
 handle HOL_ERR _ => raise ERR "RIGHT_TY_BETA" "";

fun RIGHT_TY_TM_BETA th = RIGHT_BETA th
 handle HOL_ERR _ => RIGHT_TY_BETA th
 handle HOL_ERR _ => raise ERR "RIGHT_TY_TM_BETA" "";


(*---------------------------------------------------------------------------
 *  "(\x1 ... xn.t)t1 ... tn" -->
 *    |- (\x1 ... xn.t)t1 ... tn = t[t1/x1] ... [tn/xn]
 *---------------------------------------------------------------------------*)

fun LIST_BETA_CONV tm =
   let val (Rator,Rand) = dest_comb tm
   in RIGHT_BETA (AP_THM (LIST_BETA_CONV Rator) Rand)
   end handle HOL_ERR _ => REFL tm

(*---------------------------------------------------------------------------
 *  "(\:a1 ... an.t) [:ty1, ... tyn:]" -->
 *    |- (\:a1 ... an.t) [:ty1, ... tyn:] = t[ty1/a1] ... [tyn/an]
 *---------------------------------------------------------------------------*)

fun LIST_TY_BETA_CONV tm =
   let val (Rator,Rand) = dest_tycomb tm
   in RIGHT_TY_BETA (TY_COMB (LIST_TY_BETA_CONV Rator) Rand)
   end handle HOL_ERR _ => REFL tm;

fun TY_TM_BETA_CONV tm =
   BETA_CONV tm
   handle HOL_ERR _ =>
   TY_BETA_CONV tm
   handle HOL_ERR _ => raise ERR "TY_TM_BETA_CONV" "";

fun LIST_TY_TM_BETA_CONV tm =
   let val (Rator,Rand) = dest_comb tm
   in RIGHT_BETA (AP_THM (LIST_TY_TM_BETA_CONV Rator) Rand)
   end handle HOL_ERR _ =>
   let val (Rator,Rand) = dest_tycomb tm
   in RIGHT_TY_BETA (TY_COMB (LIST_TY_TM_BETA_CONV Rator) Rand)
   end handle HOL_ERR _ => REFL tm;


fun RIGHT_LIST_BETA th = TRANS th (LIST_BETA_CONV(rhs(concl th)))

fun RIGHT_LIST_TY_BETA th = TRANS th (LIST_TY_BETA_CONV(rhs(concl th)))

fun RIGHT_LIST_TY_TM_BETA th = TRANS th (LIST_TY_TM_BETA_CONV(rhs(concl th)))

(*---------------------------------------------------------------------------*
 * "A |- t1 /\ ... /\ tn"   --->   ["A|-t1", ..., "A|-tn"],  where n>0       *
 *                                                                           *
 * Flattens out all conjuncts, regardless of grouping                        *
 *---------------------------------------------------------------------------*)

fun CONJUNCTS th =
let
  fun aux th acc =
    aux (CONJUNCT1 th) (aux (CONJUNCT2 th) acc)
      handle HOL_ERR _ =>
        th :: acc
in
  aux th []
end

(*---------------------------------------------------------------------------*
 * |- t1 = t2  if t1 and t2 are equivalent using idempotence, symmetry and   *
 *                associativity of /\.                                       *
 *---------------------------------------------------------------------------*)

fun CONJUNCTS_AC (t1, t2) =
let
  fun conjuncts dict th =
    conjuncts (conjuncts dict (CONJUNCT1 th)) (CONJUNCT2 th)
      handle HOL_ERR _ =>
        Redblackmap.insert (dict, concl th, th)
  fun prove_conj dict t =
    let
      val (l, r) = dest_conj t
    in
      CONJ (prove_conj dict l) (prove_conj dict r)
    end
    handle HOL_ERR _ =>
      Redblackmap.find (dict, t)
  val empty = Redblackmap.mkDict compare
  val t1_imp_t2 = prove_conj (conjuncts empty (ASSUME t1)) t2
  val t2_imp_t1 = prove_conj (conjuncts empty (ASSUME t2)) t1
in
  IMP_ANTISYM_RULE (DISCH t1 t1_imp_t2) (DISCH t2 t2_imp_t1)
end
handle HOL_ERR _ => raise ERR "CONJUNCTS_AC" ""
     | Redblackmap.NotFound => raise ERR "CONJUNCTS_AC" ""

(*---------------------------------------------------------------------------*
 * |- t1 = t2  if t1 and t2 are equivalent using idempotence, symmetry and   *
 *                associativity of \/.                                       *
 *---------------------------------------------------------------------------*)

(*
The implementation is dual to that of CONJUNCTS_AC. We first show that t2
follows from each of its disjuncts. These intermediate theorems are stored in
a dictionary with logarithmic time access. Combining them, we then show that
since each disjunct of t1 implies t2, t1 implies t2.

Note that deriving t2 from each of its disjuncts is not completely
straightforward. An implementation that, for each disjunct, assumes the
disjunct and derives t2 by disjunction introduction would have quadratic
complexity. The given implementation achieves linearithmic complexity by
assuming t2, and then deriving "l |- t2" and "r |- t2" from "l \/ r |- t2".

We found the implementation of this inference step that is used in "disjuncts"
(below) to be roughly twice as fast as one that instantiates a proforma
theorem "(l \/ r ==> t2) ==> l ==> t2" (and a similar proforma theorem for r).
Still, it is relatively expensive. If the number of disjuncts is small, an
implementation with quadratic complexity (as outlined above) is faster. Of
course, these figures very much depend on the primitive inference rules
available and their performance relative to each other.
*)

fun DISJUNCTS_AC (t1, t2) =
let
  fun disjuncts dict (t, th) =
    let
      val (l, r) = dest_disj t
      val th = DISCH t th
      val l_th = MP th (DISJ1 (ASSUME l) r)
      val r_th = MP th (DISJ2 l (ASSUME r))
    in
      disjuncts (disjuncts dict (l, l_th)) (r, r_th)
    end
    handle HOL_ERR _ =>
      Redblackmap.insert (dict, t, th)
  fun prove_from_disj dict t =
    let
      val (l, r) = dest_disj t
    in
      DISJ_CASES (ASSUME t) (prove_from_disj dict l) (prove_from_disj dict r)
    end
    handle HOL_ERR _ =>
      Redblackmap.find (dict, t)
  val empty = Redblackmap.mkDict compare
  val t1_imp_t2 = prove_from_disj (disjuncts empty (t2, ASSUME t2)) t1
  val t2_imp_t1 = prove_from_disj (disjuncts empty (t1, ASSUME t1)) t2
in
  IMP_ANTISYM_RULE (DISCH t1 t1_imp_t2) (DISCH t2 t2_imp_t1)
end
handle HOL_ERR _ => raise ERR "DISJUNCTS_AC" ""
     | Redblackmap.NotFound => raise ERR "DISJUNCTS_AC" ""

(*---------------------------------------------------------------------------
 *           A,t |- t1 = t2
 *    -----------------------------
 *      A |- (t /\ t1) = (t /\ t2)
 *---------------------------------------------------------------------------*)

fun CONJ_DISCH t th =
   let val (lhs,rhs) = dest_eq(concl th)
       and th1 = DISCH t th
       val left_t  = mk_conj(t,lhs)
       val right_t = mk_conj(t,rhs)
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
   end

(*---------------------------------------------------------------------------
 *                    A,t1,...,tn |- t = u
 *    --------------------------------------------------------
 *      A |- (t1 /\ ... /\ tn /\ t) = (t1 /\ ... /\ tn /\ u)
 *---------------------------------------------------------------------------*)

val CONJ_DISCHL = itlist CONJ_DISCH

(*---------------------------------------------------------------------------
 *       A,t1 |- t2                A,t |- F
 *     --------------              --------
 *     A |- t1 ==> t2               A |- ~t
 *---------------------------------------------------------------------------*)

fun NEG_DISCH t th =
  (if eq (concl th) boolSyntax.F
      then NOT_INTRO (DISCH t th) else DISCH t th)
  handle HOL_ERR _ => raise ERR "NEG_DISCH" ""

(*---------------------------------------------------------------------------
 *    A |- ~(t1 = t2)
 *   -----------------
 *    A |- ~(t2 = t1)
 *---------------------------------------------------------------------------*)

local fun flip (lhs,rhs) = (rhs, lhs)
in
fun NOT_EQ_SYM th =
   let val t = (mk_eq o flip o dest_eq o dest_neg o concl) th
   in MP (SPEC t IMP_F) (DISCH t (MP th (SYM(ASSUME t))))
   end
end

(* ---------------------------------------------------------------------*)
(* EQF_INTRO: inference rule for introducing equality with "F".		*)
(*									*)
(* 	         ~tm							*)
(*	     -----------    EQF_INTRO					*)
(*	        tm = F							*)
(*									*)
(* [TFM 90.05.08]							*)
(* ---------------------------------------------------------------------*)

local val Fth = ASSUME F
in
fun EQF_INTRO th =
   IMP_ANTISYM_RULE (NOT_ELIM th)
                    (DISCH F (CONTR (dest_neg (concl th)) Fth))
   handle HOL_ERR _ => raise ERR "EQF_INTRO" ""
end

(* ---------------------------------------------------------------------*)
(* EQF_ELIM: inference rule for eliminating equality with "F".		*)
(*									*)
(*	      |- tm = F							*)
(*	     -----------    EQF_ELIM					*)
(* 	       |- ~ tm							*)
(*									*)
(* [TFM 90.08.23]							*)
(* ---------------------------------------------------------------------*)

fun EQF_ELIM th =
   let val (lhs,rhs) = dest_eq(concl th)
       val _ = assert (eq boolSyntax.F) rhs
   in NOT_INTRO(DISCH lhs (EQ_MP th (ASSUME lhs)))
   end
   handle HOL_ERR _ => raise ERR "EQF_ELIM" ""

(*---------------------------------------------------------------------------
 * Generalise a theorem over all variables free in conclusion but not in hyps
 *
 *         A |- t[x1,...,xn]
 *    ----------------------------
 *     A |- !x1...xn.t[x1,...,xn]
 *---------------------------------------------------------------------------*)

fun GEN_ALL th =
   HOLset.foldl (fn (v, th) => GEN v th)
       th
      (HOLset.difference (FVL [concl th] empty_tmset, hyp_frees th))

(*---------------------------------------------------------------------------
 * Generalise a theorem over all type variables free in conclusion but not in hyps
 *
 *         A |- t[a1,...,an]
 *    ----------------------------                 TY_GEN_ALL
 *     A |- !:a1...an.t[a1,...,an]
 *---------------------------------------------------------------------------*)

fun TY_GEN_ALL th =
   HOLset.foldl (fn (v, th) => TY_GEN v th)
       th
      (HOLset.difference (HOLset.addList(empty_tyset, type_vars_in_term(concl th)), hyp_tyvars th))

fun TY_TM_GEN_ALL th = TY_GEN_ALL (GEN_ALL th)


(*---------------------------------------------------------------------------*
 *  Discharge all hypotheses                                                 *
 *                                                                           *
 *       t1, ... , tn |- t                                                   *
 *  ------------------------------                                           *
 *    |- t1 ==> ... ==> tn ==> t                                             *
 *---------------------------------------------------------------------------*)

fun DISCH_ALL th =
    HOLset.foldl (fn (h, th) => DISCH h th) th (hypset th)

(*---------------------------------------------------------------------------*
 *    A |- t1 ==> ... ==> tn ==> t                                           *
 *  -------------------------------                                          *
 *        A, t1, ..., tn |- t                                                *
 *---------------------------------------------------------------------------*)

fun UNDISCH_ALL th = if is_imp(concl th) then UNDISCH_ALL (UNDISCH th) else th

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

local fun varyAcc v (V,l) =
       let val v' = prim_variant V v in (v'::V, v'::l) end
in
fun SPEC_ALL th =
    if is_forall (concl th) then let
        val (hvs,con) = (HOLset.listItems ## I) (hyp_frees th, concl th)
        val fvs = free_vars con
        val vars = fst(strip_forall con)
      in
        SPECL (snd(itlist varyAcc vars (hvs@fvs,[]))) th
      end
    else th
end

(* ---------------------------------------------------------------------*)
(* TY_SPEC_ALL : thm -> thm						*)
(*									*)
(*     A |- !:a1 ... an. t[ai]						*)
(*    ------------------------   where the ai' are distinct typevars    *)
(*        A |- t[ai'/ai]	 and not free in the input theorem	*)
(*									*)
(* BUGFIX: added the "distinct" part and code to make the ai's not free *)
(* in the conclusion !a1...an.t[ai].		        [TFM 90.10.04]	*)
(* ---------------------------------------------------------------------*)

local fun varyAcc v (V,l) =
       let val v' = prim_variant_type V v in (v'::V, v'::l) end
in
fun TY_SPEC_ALL th =
    if is_tyforall (concl th) then let
        val (hvs,con) = (HOLset.listItems ## I) (hyp_tyvars th, concl th)
        val fvs = type_vars_in_term con
        val vars = fst(strip_tyforall con)
      in
        TY_SPECL (snd(itlist varyAcc vars (hvs@fvs,[]))) th
      end
    else th
end;

local fun varyAcc (inR v) (TV,V,l) =
       let val v' = prim_variant V v in (TV, v'::V, inR v'::l) end
        | varyAcc (inL v) (TV,V,l) =
       let val v' = prim_variant_type TV v in (v'::TV, V, inL v'::l) end
in
fun TY_TM_SPEC_ALL th =
  let val con = concl th
  in
    if is_tyforall con orelse is_forall con then let
        val htvs = HOLset.listItems (hyp_tyvars th)
        val hvs  = HOLset.listItems (hyp_frees th)
        val ftvs = type_vars_in_term con
        val fvs  = free_vars con
        val vars = fst(strip_all_forall con)
      in
        TY_TM_SPECL (#3(itlist varyAcc vars (htvs@ftvs,hvs@fvs,[]))) th
      end
    else th
  end
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

(* old:
fun ISPEC t th =
   let val th = TY_SPEC_ALL th
       val (Bvar,_) = dest_forall(concl th) handle HOL_ERR _
                      => raise ERR "ISPEC"
                           "input theorem not universally quantified"
       val (_,inst) = match_term Bvar t handle HOL_ERR e
                      => raise ERR "ISPEC"
                           "can't type-instantiate input theorem"
       val ith = PURE_INST_TYPE inst th
                    handle HOL_ERR {message,...}
                      => raise ERR "ISPEC"
                           ("failed to type-instantiate input theorem:\n" ^ message)
   in SPEC t ith handle HOL_ERR _
         => raise ERR "ISPEC" ": type variable free in assumptions"
   end
*)

(* ---------------------------------------------------------------------*)
(* ISPEC: specialization, with type/kind/rank instantation if necessary.*)
(*									*)
(*     A |- !x:ty.tm							*)
(*  -----------------------   ISPEC "t:ty'" 				*)
(*      A |- tm[t/x]							*)
(*									*)
(* (where t is free for x in tm, and ty' is an instance of ty)		*)
(* ---------------------------------------------------------------------*)

fun ISPEC t th =
   let val th = TY_SPEC_ALL th
       val (Bvar,_) = dest_forall(concl th) handle HOL_ERR _
                      => raise ERR "ISPEC"
                           "input theorem not universally quantified"
       val (_,inst,kd_inst,rk) = kind_match_term Bvar t handle HOL_ERR _
                      => raise ERR "ISPEC"
                           "can't type-instantiate input theorem"
       val rth = INST_RANK rk th
                    handle HOL_ERR {message,...}
                      => raise ERR "ISPEC"
                           ("failed to rank-instantiate input theorem:\n" ^ message)
       val kth = INST_KIND kd_inst rth
                    handle HOL_ERR {message,...}
                      => raise ERR "ISPEC"
                           ("failed to kind-instantiate input theorem:\n" ^ message)
       val ith = PURE_INST_TYPE inst kth
                    handle HOL_ERR {message,...}
                      => raise ERR "ISPEC"
                           ("failed to type-instantiate input theorem:\n" ^ message)
   in SPEC t ith handle HOL_ERR _
         => raise ERR "ISPEC" ": type or kind variable free in assumptions"
   end

(* ---------------------------------------------------------------------*)
(* ISPECL: iterated specialization, with type instantiation if necessary.*)
(*									*)
(*        A |- !x1...xn.tm						*)
(*  ---------------------------------   ISPECL ["t1",...,"tn"]		*)
(*      A |- tm[t1/x1,...,tn/xn]					*)
(*									*)
(* (where ti is free for xi in tm)					*)
(*                                                                      *)
(* Note: the following is simpler but it DOESN'T WORK.                  *)
(*                                                                      *)
(*  fun ISPECL tms th = rev_itlist ISPEC tms th                         *)
(*                                                                      *)
(* ---------------------------------------------------------------------*)

local fun strip [] _ = []     (* Returns a list of (pat,ob) pairs. *)
        | strip (tm::tml) M =
            let val (Bvar,Body) = dest_forall M
            in (type_of Bvar,type_of tm)::strip tml Body   end
      fun funty [] = bool
        | funty (ty::tys) = ty --> funty tys
in
fun ISPECL [] = TY_SPEC_ALL (*I*)
  | ISPECL [tm] = ISPEC tm
  | ISPECL tms = fn th =>
     let val th = TY_SPEC_ALL th
         val pairs = strip tms (concl th) handle HOL_ERR _
                     => raise ERR "ISPECL" "list of terms too long for theorem"
         val (pats,obs) = split pairs
         val (ty_theta,kd_theta,rk) =
             Type.kind_match_type (funty pats) (funty obs)
                      handle HOL_ERR _ => raise ERR "ISPECL"
                              "can't type-instantiate input theorem"
     in SPECL tms (INST_RK_KD_TY (rk,kd_theta,ty_theta) th) handle HOL_ERR _
        => raise ERR "ISPECL" "type variable or kind variable free in assumptions"
     end
end


(*---------------------------------------------------------------------------
 * Use the conclusion of the first theorem to delete a hypothesis of
 *   the second theorem.
 *
 *    A |- t1 	B, t1 |- t2
 *    -----------------------
 *         A u B |- t2
 *---------------------------------------------------------------------------*)

fun PROVE_HYP ath bth =  MP (DISCH (concl ath) bth) ath

(*---------------------------------------------------------------------------
 * A |- t1/\t2  ---> A |- t1, A |- t2
 *---------------------------------------------------------------------------*)

fun CONJ_PAIR th = (CONJUNCT1 th, CONJUNCT2 th)
                   handle HOL_ERR _ => raise ERR "CONJ_PAIR" ""

(*---------------------------------------------------------------------------
 * ["A1|-t1", ..., "An|-tn"]  ---> "A1u...uAn|-t1 /\ ... /\ tn", where n>0
 *---------------------------------------------------------------------------*)

val LIST_CONJ = end_itlist CONJ

(*---------------------------------------------------------------------------
 * "A |- t1 /\ (...(... /\ tn)...)"
 *   --->
 *   [ "A|-t1", ..., "A|-tn"],  where n>0
 *
 * Inverse of LIST_CONJ : flattens only right conjuncts.
 * You must specify n, since tn could itself be a conjunction
 *---------------------------------------------------------------------------*)

fun CONJ_LIST 1 th = [th]
  | CONJ_LIST n th =  CONJUNCT1 th :: CONJ_LIST (n-1) (CONJUNCT2 th)
      handle HOL_ERR _ => raise ERR "CONJ_LIST" ""

(*---------------------------------------------------------------------------
 * "|- !x. (t1 /\ ...) /\ ... (!y. ... /\ tn)"
 *   --->  [ "|-t1", ..., "|-tn"],  where n>0
 *
 * Flattens out conjuncts even in bodies of forall's
 *---------------------------------------------------------------------------*)

fun BODY_CONJUNCTS th =
   if is_forall (concl th)
   then BODY_CONJUNCTS (SPEC_ALL th)
   else if is_conj (concl th)
        then (BODY_CONJUNCTS (CONJUNCT1 th) @ BODY_CONJUNCTS (CONJUNCT2 th))
        else [th]

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
 *---------------------------------------------------------------------------*)

fun IMP_CANON th =
 let val w = concl th
 in if is_forall w then IMP_CANON (SPEC_ALL th) else
    if is_conj w then IMP_CANON(CONJUNCT1 th) @ IMP_CANON(CONJUNCT2 th) else
    if is_imp w
    then let val (ant,_) = dest_imp w
         in if is_conj ant
            then let val (conj1,conj2) = dest_conj ant
                 in IMP_CANON (DISCH conj1 (DISCH conj2
                        (MP th (CONJ(ASSUME conj1)(ASSUME conj2)))))
                 end
            else
            if is_disj ant
            then let val (disj1,disj2) = dest_disj ant
                 in IMP_CANON(DISCH disj1 (MP th (DISJ1(ASSUME disj1) disj2)))
                    @
                    IMP_CANON(DISCH disj2 (MP th (DISJ2 disj1 (ASSUME disj2))))
                 end
            else
            if is_exists ant
            then let val (Bvar,Body) = dest_exists ant
                     val bv' = variant (thm_frees th) Bvar
                     val body' = subst [Bvar |-> bv'] Body
                 in IMP_CANON (DISCH body'
                        (MP th (EXISTS(ant, bv') (ASSUME body'))))
                 end
            else map (DISCH ant) (IMP_CANON (UNDISCH th))
         end
    else [th]
   end


(*---------------------------------------------------------------------------
 * MP_CANON puts a theorem
 *
 *       |- !x. t1 ==> !y. t2 ==> ... ==> tm ==>  t
 *
 * into canonical form for applying MATCH_MP_TAC by moving quantifiers to 
 * the outmost level and combining implications
 * 
 *      t1 ==> !x. t2     --->  !x. t1 ==> t2
 *      t1 ==> t2 ==> t3  --->  t1 /\ t2 ==> t3
 * 
 * It might be useful to replace equivalences with implications while 
 * normalising. MP_GENEQ_CANON gets a list of boolean values as an extra 
 * argument to configure such replacements. The occuring equations are split 
 * according to the elements of this list. true focuses on the left hand side,
 * i.e. the right-hand side is put into the antecedent. false focuses on the
 * right hand side. If the list is empty, the equation is not splitted.
 * 
 * MP_GENEQ_CANON [true]  |- !x. A x ==> (!y. (B1 x y):bool = B2 y) --->
 *                           !x y. A x /\ B2 y ===> B1 x y
 * MP_GENEQ_CANON [false] |- !x. A x ==> (!y. (B1 x y):bool = B2 y) --->
 *                           !x y. A x /\ B1 x y ===> B2 y
 * 
 * For convinience the most common cases of this parameter are introduced 
 * own functions 
 *
 * val MP_CANON     = MP_GENEQ_CANON []
 * val MP_LEQ_CANON = MP_GENEQ_CANON [true]
 * val MP_REQ_CANON = MP_GENEQ_CANON [false]
 *---------------------------------------------------------------------------*)

local
fun RIGHT_IMP_IMP_FORALL_RULE th =
  let val w = concl th
  in if is_imp_only w
     then let val (ant,conc) = dest_imp w 
          in if is_forall conc 
             then let val (Bvar,Body) = dest_forall conc;
                      val bv' = variant (thm_frees th) Bvar
                      val th1 = MP th (ASSUME ant);
                      val th2 = SPEC bv' th1;
                      val th3 = DISCH ant th2;
                      val th4 = RIGHT_IMP_IMP_FORALL_RULE th3;
                      val th5 = GEN bv' th4
                  in th5 
                  end
             else
             if is_imp_only conc                
             then let val (ant2,conc2) = dest_imp conc
                      val conc_t = mk_conj (ant, ant2);
                      val conc_thm = ASSUME conc_t;
                      val th1 = MP th  (CONJUNCT1 conc_thm);
                      val th2 = MP th1 (CONJUNCT2 conc_thm);
                      val th3 = DISCH conc_t th2
                  in RIGHT_IMP_IMP_FORALL_RULE th3
                  end
             else th
          end
     else th 
  end

in
fun MP_GENEQ_CANON eqL th = 
  let val w = concl th
  in if is_forall w 
     then let val (Bvar,Body) = dest_forall w
             val bv' = variant (thm_frees th) Bvar
             val th1 = MP_GENEQ_CANON eqL (SPEC bv' th);
             val th2 = GEN bv' th1
          in th2
          end
     else
     if is_imp_only w
     then let val (ant,conc) = dest_imp w 
              val th1 = MP th  (ASSUME ant)
              val th2 = MP_GENEQ_CANON eqL th1
              val th3 = DISCH ant th2
              val th4 = RIGHT_IMP_IMP_FORALL_RULE th3
          in th4
          end
     else 
     if not (null eqL) andalso is_eq w 
     then
       (MP_GENEQ_CANON (tl eqL) (((if hd eqL then snd else fst)) (EQ_IMP_RULE th)) handle HOL_ERR _ => th)
     else th
  end
end;

val MP_CANON     = MP_GENEQ_CANON [];
val MP_LEQ_CANON = MP_GENEQ_CANON [true];
val MP_REQ_CANON = MP_GENEQ_CANON [false];


(*---------------------------------------------------------------------------
 *  A1 |- t1   ...   An |- tn      A |- t1==>...==>tn==>t
 *   -----------------------------------------------------
 *            A u A1 u ... u An |- t
 *---------------------------------------------------------------------------*)

val LIST_MP  = rev_itlist (fn x => fn y => MP y x)

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
  let val (ant,conseq) = dest_imp (concl impth)
      val notb = mk_neg conseq
  in DISCH notb
      (EQ_MP (SPEC ant imp_th)
             (DISCH ant (MP (ASSUME notb)
                            (MP impth (ASSUME ant)))))
  end
  handle HOL_ERR _ => raise ERR "CONTRAPOS" ""
end

(*---------------------------------------------------------------------------
 *      A |- t1 \/ t2
 *   --------------------
 *     A |-  ~ t1 ==> t2
 *---------------------------------------------------------------------------*)

fun DISJ_IMP dth =
   let val (disj1,disj2) = dest_disj (concl dth)
       val nota = mk_neg disj1
   in DISCH nota
        (DISJ_CASES dth (CONTR disj2 (MP (ASSUME nota) (ASSUME disj1)))
                        (ASSUME disj2))
   end
   handle HOL_ERR _ => raise ERR "DISJ_IMP" ""

(*---------------------------------------------------------------------------
 *  A |- t1 ==> t2
 *  ---------------
 *   A |- ~t1 \/ t2
 *---------------------------------------------------------------------------*)

fun IMP_ELIM th =
   let val (ant,conseq) = dest_imp (concl th)
       val not_t1 = mk_neg ant
   in
   DISJ_CASES (SPEC ant EXCLUDED_MIDDLE)
              (DISJ2 not_t1 (MP th (ASSUME ant)))
              (DISJ1 (ASSUME not_t1) conseq)
   end
   handle HOL_ERR _ => raise ERR "IMP_ELIM" ""

(*---------------------------------------------------------------------------
 *  A |- t1 \/ t2     A1, t1 |- t3      A2, t2 |- t4
 *   ------------------------------------------------
 *                A u A1 u A2 |- t3 \/ t4
 *---------------------------------------------------------------------------*)

fun DISJ_CASES_UNION dth ath bth =
    DISJ_CASES dth (DISJ1 ath (concl bth)) (DISJ2 (concl ath) bth)

(*---------------------------------------------------------------------------*)
(*                                                                           *)
(*       |- A1 \/ ... \/ An     [H1,A1 |- M,  ...,  Hn,An |- M]              *)
(*     ---------------------------------------------------------             *)
(*                   H1 u ... u Hn |- M                                      *)
(*                                                                           *)
(* The order of the theorems in the list doesn't matter: an operation akin   *)
(* to sorting lines them up with the disjuncts in the theorem.               *)
(*---------------------------------------------------------------------------*)

local
 fun ishyp tm th = HOLset.member(hypset th,tm)
 fun organize (tm::rst) (alist as (_::_)) =
      let val (th,next) = Lib.pluck (ishyp tm) alist
      in th::organize rst next
      end
   | organize [] [] = []
   | organize other wise = raise ERR "DISJ_CASESL.organize" "length difference"
in
fun DISJ_CASESL disjth thl =
 let val cases = strip_disj(concl disjth)
     val thl' = organize cases thl
     fun DL th [] = raise ERR "DISJ_CASESL" "no cases"
       | DL th [th1] = PROVE_HYP th th1
       | DL th [th1,th2] = DISJ_CASES th th1 th2
       | DL th (th1::rst) = DISJ_CASES th th1
                               (DL(ASSUME(snd(dest_disj(concl th)))) rst)
 in DL disjth thl'
 end
 handle e => raise wrap_exn "Drule" "DISJ_CASESL" e
end

(*---------------------------------------------------------------------------
 * Rename the bound variable of a lambda-abstraction
 *
 *       "x"   "(\y.t)"   --->   |- "\y.t = \x. t[x/y]"
 *---------------------------------------------------------------------------*)

fun ALPHA_CONV x t = let
  (* avoid calling dest_abs *)
  val (dty, _) = dom_rng (type_of t)
                 handle HOL_ERR _ =>
                        raise ERR "ALPHA_CONV" "Second term not an abstraction"
  val (xstr, xty) = with_exn dest_var x
                      (ERR "ALPHA_CONV" "First term not a variable")
  val _ = Type.compare(dty, xty) = EQUAL
          orelse raise ERR "ALPHA_CONV"
                           ("Type of variable not compatible with abstraction"
                            ^": "^type_to_string dty^" : "^type_to_string xty)
  val t' = rename_bvar xstr t
in
  ALPHA t t'
end

fun ALPHA_NAME_CONV s t = let
  (* avoid calling dest_abs *)
  val _ = dom_rng (type_of t)
                 handle HOL_ERR _ =>
                        raise ERR "ALPHA_NAME_CONV" "Term not an abstraction"
  val t' = rename_bvar s t
in
  ALPHA t t'
end


(*---------------------------------------------------------------------------
 * Rename the bound variable of a lambda type-abstraction
 *
 *       "'a"   "(\:'b.t)"   --->   |- "\:'b.t = \:'a. t['a/'b]"
 *
 *---------------------------------------------------------------------------*)

fun TY_ALPHA_CONV x t = let
  (* avoid calling dest_tyabs *)
  val (dty, _) = dest_univ_type (type_of t)
                 handle HOL_ERR _ =>
                        raise ERR "TY_ALPHA_CONV" "Term is not a type abstraction"
  val (xstr, xkd) = with_exn dest_var_type x
                      (ERR "TY_ALPHA_CONV" "Type is not a type variable")
  val _ = Kind.kind_compare(kind_of dty, xkd) = EQUAL
          orelse raise ERR "TY_ALPHA_CONV"
                           "Kind of type variable not compatible with type abstraction"
  val t' = rename_btyvar xstr t
in
  ALPHA t t'
end

fun TY_ALPHA_NAME_CONV s t = let
  (* avoid calling dest_tyabs *)
  val _ = dest_univ_type (type_of t)
                 handle HOL_ERR _ =>
                        raise ERR "TY_ALPHA_NAME_CONV" "Term is not a type abstraction"
  val t' = rename_btyvar s t
in
  ALPHA t t'
end

(*----------------------------------------------------------------------------
 * Version of  ALPHA_CONV that renames "x" when necessary, but then it doesn't
 * meet the specification. Is that really a problem? Notice that this version
 * of ALPHA_CONV is more efficient.
 *
 *fun ALPHA_CONV x t =
 *  if Term.free_in x t
 *  then ALPHA_CONV (variant (free_vars t) x) t
 *  else ALPHA t (mk_abs{Bvar = x,
 *                       Body = Term.beta_conv(mk_comb{Rator = t,Rand = x})})
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

fun GEN_ALPHA_CONV x t =
   if is_abs t
   then ALPHA_CONV x t
   else let val (Rator, Rand) = dest_comb t
        in AP_TERM Rator (ALPHA_CONV x Rand)
        end
        handle HOL_ERR _ => raise ERR "GEN_ALPHA_CONV" ""

(*---------------------------------------------------------------------------
 * Rename bound variables
 *
 *       "a"   "(\:b.t)"   --->    |- "\:b.t  = \:a. t[a/b]"
 *       "a"   "(!:b.t)"   --->    |- "!:b.t  = !:a. t[a/b]"
 *       "a"   "(?:b.t)"   --->    |- "?:b.t  = ?:a. t[a/b]"
 *---------------------------------------------------------------------------*)

fun GEN_TY_ALPHA_CONV a t =
   if is_tyabs t
   then TY_ALPHA_CONV a t
   else let val (Rator, Rand) = dest_comb t
        in AP_TERM Rator (TY_ALPHA_CONV a Rand)
        end
        handle HOL_ERR _ => raise ERR "GEN_TY_ALPHA_CONV" "";

fun GEN_TY_TM_ALPHA_CONV v t =
   (case v of
      inL a => GEN_TY_ALPHA_CONV a t
    | inR x =>    GEN_ALPHA_CONV x t)
   handle HOL_ERR _ => raise ERR "GEN_TY_TM_ALPHA_CONV" "";

(* ---------------------------------------------------------------------*)
(*  A1 |- P ==> Q    A2 |- R ==> S					*)
(* --------------------------------- IMP_CONJ				*)
(*   A1 u A2 |- P /\ R ==> Q /\ S					*)
(* ---------------------------------------------------------------------*)

fun IMP_CONJ th1 th2 =
    let val (A1,_) = dest_imp (concl th1)
        and (A2,_) = dest_imp (concl th2)
        val conj = mk_conj(A1,A2)
        val (a1,a2) = CONJ_PAIR (ASSUME conj)
    in
      DISCH conj (CONJ (MP th1 a1) (MP th2 a2))
    end

(* ---------------------------------------------------------------------*)
(* EXISTS_IMP : existentially quantify the antecedent and conclusion 	*)
(* of an implication.							*)
(*									*)
(*        A |- P ==> Q							*)
(* -------------------------- EXISTS_IMP `x`				*)
(*   A |- (?x.P) ==> (?x.Q)						*)
(* ---------------------------------------------------------------------*)

fun EXISTS_IMP x th =
  if not (is_var x)
  then raise ERR "EXISTS_IMP" "first argument not a variable"
  else let val (ant,conseq) = dest_imp(concl th)
           val th1 = EXISTS (mk_exists(x,conseq),x) (UNDISCH th)
           val asm = mk_exists(x,ant)
       in DISCH asm (CHOOSE (x,ASSUME asm) th1)
       end
       handle HOL_ERR _ => raise ERR "EXISTS_IMP"
                            "variable free in assumptions"

(* ---------------------------------------------------------------------*)
(* TY_EXISTS_IMP : type existentially quantify the antecedent and 	*)
(* conclusion of an implication.					*)
(*									*)
(*        A |- P ==> Q							*)
(* ---------------------------- TY_EXISTS_IMP `:a`			*)
(*   A |- (?:a.P) ==> (?:a.Q)						*)
(*									*)
(* ---------------------------------------------------------------------*)

fun TY_EXISTS_IMP x th =
  if not (is_vartype x)
  then raise ERR "TY_EXISTS_IMP" "first argument not a type variable"
  else let val (ant,conseq) = dest_imp(concl th)
           val th1 = TY_EXISTS (mk_tyexists(x,conseq),x) (UNDISCH th)
           val asm = mk_tyexists(x,ant)
       in DISCH asm (TY_CHOOSE (x,ASSUME asm) th1)
       end
       handle HOL_ERR _ => raise ERR "TY_EXISTS_IMP"
                            "type variable free in assumptions";


(*---------------------------------------------------------------------------*
 * Instantiate terms and types of a theorem.                                 *
 *---------------------------------------------------------------------------*)

fun PURE_INST_TY_TERM(Stm,Sty) th = INST_ALL (Stm,Sty,[],0) th

(*---------------------------------------------------------------------------*
 * Instantiate terms, types, kinds, and ranks of a theorem. This aligns      *
 * the kinds and ranks according to the type substitution.                   *
 *---------------------------------------------------------------------------*)

fun INST_TY_TERM(Stm,Sty) th = INST Stm (INST_TYPE Sty th)

(*---------------------------------------------------------------------------*
 *   |- !x y z. w   --->  |- w[g1/x][g2/y][g3/z]                             *
 *---------------------------------------------------------------------------*)

fun GSPEC th =
  let val (_,w) = dest_thm th
  in if is_forall w
     then GSPEC (SPEC (genvar (type_of (fst (dest_forall w)))) th)
     else th
  end

(*---------------------------------------------------------------------------*
 *   |- !:'a 'b 'c. w   --->  |- w['g1/'a]['g2/'b]['g3/'c]                   *
 *---------------------------------------------------------------------------*)

fun TY_GSPEC th =
  let val (_,w) = dest_thm th
  in if is_tyforall w
     then let val a = fst (dest_tyforall w)
          in TY_GSPEC (TY_SPEC (gen_var_type (kind_of a)) th)
          end
     else th
  end;

(*---------------------------------------------------------------------------*
 *   |- !:'a. !x. !:'b. !y. !:'c. !z. w   --->                               *
 *                         |- w['g1/'a][g1/x]['g2/'b][g2/y]['g3/'c][g3/z]    *
 *---------------------------------------------------------------------------*)

fun TY_TM_GSPEC th =
  let val (_,w) = dest_thm th
  in if is_forall w
     then let val v = fst (dest_forall w)
              val (_,ty) = dest_var v
          in TY_TM_GSPEC (SPEC (genvar ty) th)
          end
     else if is_tyforall w
     then let val a = fst (dest_tyforall w)
          in TY_TM_GSPEC (TY_SPEC (gen_var_type (kind_of a)) th)
          end
     else th
  end;


(*---------------------------------------------------------------------------*
 * Match a given part of "th" to a term, instantiating "th". The part        *
 * should be free in the theorem, except for outer bound variables.          *
 *---------------------------------------------------------------------------*)

fun PART_MATCH partfn th = let
  val th = TY_TM_SPEC_ALL th
  val conclfvs = Term.FVL [concl th] empty_tmset
  val hypfvs = Thm.hyp_frees th
  val hyptyvars = HOLset.listItems (Thm.hyp_tyvars th)
  val hypkdvars = HOLset.listItems (Thm.hyp_kdvars th)
  val hyprkvars = Term.has_var_rankl (Thm.hyp th)
  val pat = partfn(concl th)
  val matchfn =
      kind_match_terml hyprkvars hypkdvars hyptyvars (HOLset.intersection(conclfvs, hypfvs)) pat
in
  (fn tm => INST_ALL (matchfn tm) th)
end

(* -------------------------------------------------------------------- *
 * MATCH_MP: Matching Modus Ponens for implications.			*
 *									*
 *    |- !x1 ... xn. P ==> Q     |- P' 					*
 * ---------------------------------------				*
 *                |- Q'  						*
 *									*
 * Matches all types in conclusion except those mentioned in hypotheses.*
 * -------------------------------------------------------------------- *)

(*
val +++ = Lib.+++;
infix +++;

val ith = Kdmonad_umj1';
val th = cat;
*)

local fun variants (_,[]) = []
        | variants (av, h::rst) =
            let val vh = variant av h in vh::variants (vh::av, rst) end
      fun variant_types (_,[]) = []
        | variant_types (av, h::rst) =
            let val vh = variant_type av h in vh::variant_types (vh::av, rst) end
      fun rassoc_total1 x theta =
         case subst_assoc (equal x) theta
          of SOME y => y
           | NONE => x
      fun rassoc_total x theta =
         case subst_assoc (eq x) theta
          of SOME y => y
           | NONE => x
      fun neq1 {redex,residue} = not (equal redex residue)
      fun neq  {redex,residue} = not (eq redex residue)
in
fun MATCH_MP ith =
 let val hyptyvars = hyp_tyvars ith
     val hyptmvars = hyp_frees  ith
     val hyptyvarl = HOLset.listItems hyptyvars
     val hyptmvarl = HOLset.listItems hyptmvars
     (* val (ial2,ibod) = strip_all_forall_avoid (hyptyvarl,hyptmvarl) (concl ith) *)
     val (ial2,ibod) = strip_all_forall (concl ith)
     val ityl = mapfilter outL ial2
     val itml = mapfilter outR ial2
     val itys = HOLset.addList(empty_tyset, ityl)
     val bod = fst(dest_imp ibod)
     val hyptyvars = HOLset.listItems (HOLset.difference(hyptyvars, itys))
     val hypkdvars = HOLset.listItems (hyp_kdvars ith)
     val hyprkvars = Term.has_var_rankl (hyp ith)
(* or,
     val hyptyvars = HOLset.listItems (HOLset.intersection
                     (HOLset.addList(empty_tyset, type_vars_in_term (concl ith)),
                      hyptyvars))
*)
     val lconsts = HOLset.intersection
                     (FVL [concl ith] empty_tmset, hyptmvars)
 in fn th =>
   let val mfn = C (Term.kind_match_terml hyprkvars hypkdvars hyptyvars lconsts) (concl th)
       val (_,tyS,kdS,rkS) = mfn bod
       val (atyS,tyS) = partition (fn {redex,residue} => mem redex ityl) tyS
       val tth = INST_RK_KD_TY (rkS,kdS,tyS) ith
       val (avs,tbody) = strip_all_forall (concl tth)
       val (ant,conseq) = dest_imp tbody
       val (tmin,tyin,_,_) = mfn ant
       val tyhy1 = HOLset.listItems (hyp_tyvars tth)
       and tyhy2 = HOLset.listItems (hyp_tyvars th)
       val hy1 = HOLset.listItems (hyp_frees tth)
       and hy2 = HOLset.listItems (hyp_frees th)
       val (rtyvs,ftyvs) = partition (C type_var_occurs ant) (type_vars_in_term conseq)
       val (rvs,fvs) = partition (C free_in ant) (free_vars conseq)
       val atyvs = mapfilter outL avs
       val atmvs = mapfilter outR avs
       val aftyvs = Lib.set_diff ftyvs (Lib.set_diff tyhy1 atyvs)
       val ctyvs = type_varsl (map (C rassoc_total1 tyin) rtyvs)
       val vftyvs = map (op |->) (zip aftyvs (variant_types (ctyvs@tyhy1@tyhy2, aftyvs)))
       val atyin = (filter neq1 vftyvs)@tyin
       val atmvs' = map (inst atyin) atmvs
       val fvs' = map (inst atyin) fvs
       val afvs = Lib.op_set_diff eq fvs' (Lib.op_set_diff eq hy1 atmvs')
       val cvs = free_varsl (map (C rassoc_total tmin o inst tyin(*or atyin*)) rvs)
       val vfvs = map (op |->) (zip afvs (variants (cvs@hy1@hy2, afvs)))
       val atmin = (filter neq vfvs)@tmin
       val (sptyl,iltyl) = partition (C mem atyvs o #redex) atyin
       val (spl,ill) = partition (C (op_mem eq) atmvs' o #redex) atmin
       val fspl = map (C rassoc_total1 sptyl +++ (C rassoc_total spl o inst atyin)) avs
       val mth = MP (TY_TM_SPECL fspl (INST ill (PURE_INST_TYPE iltyl tth))) th
       fun loop [] = []
         | loop (inR tm::rst) =
             (case subst_assoc (eq (inst atyin tm)) vfvs
                of NONE => loop rst
                 | SOME x => inR x::loop rst)
         | loop (inL ty::rst) =
             (case subst_assoc (equal ty) vftyvs
                of NONE => loop rst
                 | SOME x => inL x::loop rst)
   in
     TY_TM_GENL (loop avs) mth
   end
 end
end

(*---------------------------------------------------------------------------*
 * Now higher-order versions of PART_MATCH and MATCH_MP                      *
 *---------------------------------------------------------------------------*)

(* IMPORTANT: See the bottom of this file for a longish discussion of some
              of the ways this implementation attempts to keep bound variable
              names sensible.
*)

(* ------------------------------------------------------------------------- *)
(* Attempt alpha conversion.                                                 *)
(* ------------------------------------------------------------------------- *)

fun tryalpha v tm =
 let val (Bvar,Body) = dest_abs tm
 in if eq v Bvar then tm else
    if var_occurs v Body then tryalpha (variant (free_vars tm) v) tm
    else mk_abs(v, subst[Bvar |-> v] Body)
 end

fun trytyalpha a tm =
 let val (Bvar,Body) = dest_tyabs tm
 in if a = Bvar then tm else
    if type_var_occurs a Body then trytyalpha (variant_type (type_vars_in_term tm) a) tm
    else mk_tyabs(a, inst[Bvar |-> a] Body)
 end


(* ------------------------------------------------------------------------- *)
(* Match up bound variables names.                                           *)
(* ------------------------------------------------------------------------- *)

(* first argument is actual term, second is from theorem being matched *)
fun match_bvs t1 t2 (acc as (tyacc,tmacc)) =
 case (dest_term t1, dest_term t2)
  of (LAMB(v1,b1), LAMB(v2,b2))
      => let val n1 = fst(dest_var v1)
             val n2 = fst(dest_var v2)
             val newacc = if n1 = n2 then acc else (tyacc, insert(n1, n2) tmacc)
         in
           match_bvs b1 b2 newacc
         end
  | (COMB(l1,r1), COMB(l2,r2)) => match_bvs l1 l2 (match_bvs r1 r2 acc)
  | (TYLAMB(a1,b1), TYLAMB(a2,b2))
      => let val n1 = #1(dest_var_type a1)
             val n2 = #1(dest_var_type a2)
             val newacc = if n1 = n2 then acc else (insert(n1, n2) tyacc, tmacc)
         in
           match_bvs b1 b2 newacc
         end
  | (TYCOMB(tm1,ty1), TYCOMB(tm2,ty2)) => match_bvs tm1 tm2 acc
  | otherwise => acc

(* bindings come from match_bvs, telling us which bound variables are going
   to get renamed, and thmc is the conclusion of the pattern theorem.
   acc is a set of free variables that need to get instantiated away *)
fun look_for_avoids bindings thmc acc = let
  val lfa = look_for_avoids bindings
  val (tybindings,tmbindings) = bindings
in
  case dest_term thmc of
    LAMB (v, b) => let
      val (thm_n, _) = dest_var v
    in
      case Lib.total (rev_assoc thm_n) tmbindings of
        SOME n => let
          val fvs = FVL [b] empty_tmset
          fun f (v, acc as (tyacc,tmacc)) =
              if #1 (dest_var v) = n then (tyacc, HOLset.add(tmacc, v))
              else acc
        in
          lfa b (HOLset.foldl f acc fvs)
        end
      | NONE => lfa b acc
    end
  | COMB (l,r) => lfa l (lfa r acc)
  | TYLAMB (a, b) => let
      val (thm_n, _) = dest_var_type a
    in
      case Lib.total (rev_assoc thm_n) tybindings of
        SOME n => let
          val ftvs = HOLset.addList(empty_tyset, type_vars_in_term b)
          fun f (a, acc as (tyacc,tmacc)) =
              if #1 (dest_var_type a) = n then (HOLset.add(tyacc, a), tmacc)
              else acc
        in
          lfa b (HOLset.foldl f acc ftvs)
        end
      | NONE => lfa b acc
    end
  | TYCOMB (t, ty) => lfa t acc
  | _ => acc
end


(* ------------------------------------------------------------------------- *)
(* Modify bound variable names at depth. (Not very efficient...)             *)
(* ------------------------------------------------------------------------- *)

fun deep_alpha ([],[]) tm = tm
  | deep_alpha (env as (tyenv,tmenv)) tm =
     case dest_term tm
      of LAMB(Bvar,Body) =>
          (let val (Name,Ty) = dest_var Bvar
               val ((vn',_),newenv) = Lib.pluck (fn (_,x) => x = Name) tmenv
               val tm' = tryalpha (mk_var(vn', Ty)) tm
               val (iv,ib) = dest_abs tm'
           in mk_abs(iv, deep_alpha (tyenv,newenv) ib)
           end
           handle HOL_ERR _ => mk_abs(Bvar,deep_alpha env Body))
       | COMB(Rator,Rand) => mk_comb(deep_alpha env Rator, deep_alpha env Rand)
       | TYLAMB(Bvar,Body) =>
          (let val (Name,Kind) = dest_var_type Bvar
               val ((vn',_),newenv) = Lib.pluck (fn (_,x) => x = Name) tyenv
               val tm' = trytyalpha (mk_var_type(vn', Kind)) tm
               val (iv,ib) = dest_tyabs tm'
           in mk_tyabs(iv, deep_alpha (newenv,tmenv) ib)
           end
           handle HOL_ERR _ => mk_tyabs(Bvar,deep_alpha env Body))
       | TYCOMB(Rator,Rand) => mk_tycomb(deep_alpha env Rator, Rand)
       | otherwise => tm

(* -------------------------------------------------------------------------
 * BETA_VAR
 *
 * Set up beta-conversion for head instances of free variable v in tm.
 *
 * EXAMPLES
 *
 *   BETA_VAR (--`x:num`--) (--`(P:num->num->bool) x x`--);
 *   BETA_VAR (--`x:num`--) (--`x + 1`--);
 *
 * Note (kxs): I am defining this before Conv, so some conversion(al)s are
 * p(re)-defined here. Ugh.
 * -------------------------------------------------------------------------
 * -------------------------------------------------------------------------
 * PART_MATCH
 *
 * Match (higher-order) part of a theorem to a term.
 *
 * PART_MATCH (snd o strip_forall) BOOL_CASES_AX (--`(P = T) \/ (P = F)`--);
 * val f = PART_MATCH lhs;
 * profile2 f NOT_FORALL_THM (--`~!x. (P:num->num->bool) x y`--);
 * profile2 f NOT_EXISTS_THM (--`?x. ~(P:num->num->bool) x y`--);
 * profile2 f LEFT_AND_EXISTS_THM
 *             (--`(?x. (P:num->num->bool) x x) /\ Q (y:num)`--);
 * profile LEFT_AND_EXISTS_CONV
 *           (--`(?x. (P:num->num->bool) x x) /\ Q (x:num)`--);
 * profile2 f NOT_FORALL_THM (--`~!x. (P:num->num->bool) y x`--);
 * profile NOT_FORALL_CONV (--`~!x. (P:num->num->bool) y x`--);
 * val f = PART_MATCH (lhs o snd o strip_imp);
 * val CRW_THM = mk_thm([],(--`P x ==> Q x (y:num) ==> (x + 0 = x)`--));
 * f CRW_THM (--`y + 0`--);
 *
 * val beta_thm = prove(--`(\x:'a. P x) b = (P b:'b)`--)--,
 *                      BETA_TAC THEN REFL_TAC);
 * val f = profile PART_MATCH lhs beta_thm;
 * profile f (--`(\x. I x) 1`--);
 * profile f (--`(\x. x) 1`--);
 * profile f (--`(\x. P x x:num) 1`--);
 *
 * The current version attempts to keep variable names constant.  This
 * is courtesy of JRH.
 *
 * Non renaming version (also courtesy of JRH!!)
 *
 * fun PART_MATCH partfn th =
 *   let val sth = SPEC_ALL th
 *       val bod = concl sth
 *       val possbetas = mapfilter (fn v => (v,BETA_VAR v bod)) (free_vars bod)
 *       fun finish_fn tyin bvs =
 *         let val npossbetas = map (inst tyin ## I) possbetas
 *         in CONV_RULE (EVERY_CONV (mapfilter (C assoc npossbetas) bvs))
 *         end
 *       val pbod = partfn bod
 *   in fn tm =>
 *     let val (tmin,tyin,kdin,rkin) = kind_match_term pbod tm
 *         val th0 = INST_ALL (tmin,tyin,kdin,rkin) sth
 *     in finish_fn tyin (map #redex tmin) th0
 *     end
 *   end;
 *
 * EXAMPLES:
 *
 * val CET = mk_thm([],(--`(!c. P ($COND c x y) c) = (P x T /\ P y F)`--));

 * PART_MATCH lhs FORALL_SIMP (--`!x. y + 1 = 2`--);
 * PART_MATCH lhs FORALL_SIMP (--`!x. x + 1 = 2`--); (* fails *)
 * PART_MATCH lhs CET (--`!b. ~(f (if b then t else e))`--);
 * PART_MATCH lhs option_CASE_ELIM (--`!b. ~(P (option_CASE e f b))`--);
 * PART_MATCH lhs (MK_FORALL (--`c:bool`--) COND_ELIM_THM)
 *                (--`!b. ~(f (if b then t else e))`--);
 * PART_MATCH lhs (MK_FORALL (--`c:bool`--) COND_ELIM_THM)
 *                 (--`!b. ~(f (if b then t else e))`--);
 * ho_term_match [] (--`!c.  P ($COND c x y)`--)
 *
 * BUG FIXES & TEST CASES
 *
 * Variable Renaming:
 * PART_MATCH (lhs o snd o strip_forall) SKOLEM_THM (--`!p. ?GI. Q GI p`--);
 * Before renaming this produced: |- (!x. ?y. Q y x) = (?y. !x. Q (y x) x)
 * After renaming this produced: |- (!p. ?GI. Q GI p) = (?GI. !p. Q (GI p) p)
 *
 * Variable renaming problem (DRS, Feb 1996):
 * PART_MATCH lhs NOT_FORALL_THM (--`~!y. P x`--);
 * Before fix produced:  |- ~(!x'. P x) = (?x'. ~(P x)) : thm
 * After fix produced:  |- ~(!y. P x) = (?y. ~(P x))
 * Fix:
 *	val bvms = match_bvs tm (inst tyin pbod) []
 * Became:
 *      val bvms = match_bvs tm (partfn (concl th0)) []
 *
 * Variable renaming problem (DRS, Feb 1996):
 * PART_MATCH lhs NOT_FORALL_THM (--`~!x. (\y. t) T`--);
 * Before fix produced (--`?y. ~(\y. t) T`--);
 * After fix produced (--`?x. ~(\y. t) T`--);
 * Fix:
 *      Moved beta reduction to be before alpha renaming.  This makes
 * match_bvs more accurate.  This was not a problem before the previous
 * fix.
 *
 * Another bug (unfixed).  bvms =  [("x","y"),("E'","x")]
 *   PART_MATCH lhs SWAP_EXISTS_THM  (--`?E' x const'.
 *       ((s = s') /\
 *         (E = E') /\
 *       (val = Val_Constr (const',x)) /\
 *       (sym = const)) /\
 *      (a1 = NONE) /\
 *      ~(const = const')`--)
 * ------------------------------------------------------------------------- *)

nonfix THENC ORELSEC
local fun COMB_CONV2 c1 c2 M =
        let val (f,x) = dest_comb M in MK_COMB(c1 f, c2 x) end
      fun ABS_CONV c M =
        let val (Bvar,Body) = dest_abs M in ABS Bvar (c Body) end
      fun TY_ABS_CONV c M =
        let val (Bvar,Body) = dest_tyabs M in TY_ABS Bvar (c Body) end
      fun TY_COMB_CONV c M =
        let val (Tm,Ty) = dest_tycomb M in TY_COMB (c Tm) Ty end
      fun RAND_CONV c M =
        let val (Rator,Rand) = dest_comb M in AP_TERM Rator (c Rand) end
      fun RATOR_CONV c M =
        let val (Rator,Rand) = dest_comb M in AP_THM (c Rator) Rand end
      fun TRY_CONV c M = c M handle HOL_ERR _ => REFL M
      fun THENC c1 c2 M =
        let val th = c1 M in TRANS th (c2 (rhs (concl th))) end
      fun ORELSEC c1 c2 M =
        c1 M handle HOL_ERR _ => c2 M
      fun TY_TM_RATOR_CONV c = ORELSEC (RATOR_CONV c) (TY_COMB_CONV c)
      fun EVERY_CONV convl = itlist THENC convl REFL
      fun CONV_RULE conv th = EQ_MP (conv(concl th)) th
      fun BETA_CONVS n =
        if n = 1 then TRY_CONV BETA_CONV
        else THENC (RATOR_CONV (BETA_CONVS (n-1))) (TRY_CONV BETA_CONV)
      fun TY_BETA_CONVS n =
        if n = 1 then TRY_CONV TY_BETA_CONV
        else THENC (TY_COMB_CONV (TY_BETA_CONVS (n-1))) (TRY_CONV TY_BETA_CONV)
      fun TY_TM_BETA_CONVS n =
        if n = 1 then TRY_CONV TY_TM_BETA_CONV
        else THENC (TY_TM_RATOR_CONV (TY_TM_BETA_CONVS (n-1))) (TRY_CONV TY_TM_BETA_CONV)
in

fun BETA_VAR v tm =
 if is_abs tm
 then let val (Bvar,Body) = dest_abs tm
      in if eq v Bvar then failwith "BETA_VAR: UNCHANGED"
         else ABS_CONV(BETA_VAR v Body) end
 else
 if is_tyabs tm
 then let val (Bvar,Body) = dest_tyabs tm
      in if type_var_occurs Bvar v then failwith "BETA_VAR: UNCHANGED"
         else TY_ABS_CONV(BETA_VAR v Body) end
 else
 if is_tycomb tm
 then let val (Tm,Ty) = dest_tycomb tm
      in TY_COMB_CONV(BETA_VAR v Tm) end
 else
 case strip_comb tm
  of (_,[]) => failwith "BETA_VAR: UNCHANGED"
   | (oper,args) =>
      if eq oper v then BETA_CONVS (length args)
      else let val (Rator,Rand) = dest_comb tm
           in let val lconv = BETA_VAR v Rator
              in let val rconv = BETA_VAR v Rand
                 in COMB_CONV2 lconv rconv
                 end handle HOL_ERR _ => RATOR_CONV lconv
              end handle HOL_ERR _ => RAND_CONV (BETA_VAR v Rand)
           end

(* v is a term variable of a universal type. *)
fun TY_BETA_VAR v tm =
 if is_tyabs tm
 then let val (Bvar,Body) = dest_tyabs tm
      in TY_ABS_CONV(TY_BETA_VAR v Body) end
 else
 if is_abs tm
 then let val (Bvar,Body) = dest_abs tm
      in if eq v Bvar then failwith "TY_BETA_VAR: UNCHANGED"
         else ABS_CONV(TY_BETA_VAR v Body) end
 else
 if is_comb tm
 then let val (Rator,Rand) = dest_comb tm
      in let val lconv = TY_BETA_VAR v Rator
         in let val rconv = TY_BETA_VAR v Rand
            in COMB_CONV2 lconv rconv
            end handle HOL_ERR _ => RATOR_CONV lconv
         end handle HOL_ERR _ => RAND_CONV (TY_BETA_VAR v Rand)
      end
 else
 case strip_tycomb tm
  of (_,[]) => failwith "TY_BETA_VAR: UNCHANGED"
   | (oper,args) =>
      if eq oper v then TY_BETA_CONVS (length args)
      else let val (Rator,Rand) = dest_tycomb tm
           in TY_COMB_CONV (TY_BETA_VAR v Rator)
           end

local
fun strip_ty_tm_comb1 tm acc =
  let val (rator,rand) = dest_comb tm
  in strip_ty_tm_comb1 rator (inR rand::acc)
  end
  handle HOL_ERR _ =>
  let val (rator,rand) = dest_tycomb tm
  in strip_ty_tm_comb1 rator (inL rand::acc)
  end
  handle HOL_ERR _ =>
  (tm,acc)
in
fun strip_ty_tm_comb tm = strip_ty_tm_comb1 tm []
end


fun strip_ty_tm_abs tm =
  let val (bvar,body) = dest_abs tm
      val (bvars,core) = strip_ty_tm_abs body
  in (inR bvar::bvars,core)
  end
  handle HOL_ERR _ =>
  let val (bvar,body) = dest_tyabs tm
      val (bvars,core) = strip_ty_tm_abs body
  in (inL bvar::bvars,core)
  end
  handle HOL_ERR _ =>
  ([],tm)

(* v is a term variable of a function type or a universal type. *)
fun TY_TM_BETA_VAR v tm =
 if is_abs tm
 then let val (Bvar,Body) = dest_abs tm
      in if eq v Bvar then failwith "TY_TM_BETA_VAR: UNCHANGED"
         else ABS_CONV(TY_TM_BETA_VAR v Body)
      end
 else
 if is_tyabs tm
 then let val (Bvar,Body) = dest_tyabs tm
      in if type_var_occurs Bvar v then failwith "TY_TM_BETA_VAR: UNCHANGED"
         else TY_ABS_CONV(TY_TM_BETA_VAR v Body)
      end
 else
 case strip_ty_tm_comb tm
  of (_,[]) => failwith "TY_TM_BETA_VAR: UNCHANGED"
   | (oper,args) =>
      if eq oper v then TY_TM_BETA_CONVS (length args)
      else let val (Rator,Rand) = dest_comb tm
           in let val lconv = TY_TM_BETA_VAR v Rator
              in let val rconv = TY_TM_BETA_VAR v Rand
                 in COMB_CONV2 lconv rconv
                 end handle HOL_ERR _ => RATOR_CONV lconv
              end handle HOL_ERR _ => RAND_CONV (TY_TM_BETA_VAR v Rand)
           end
           handle HOL_ERR _ =>
           let val (Rator,Rand) = dest_tycomb tm
           in TY_COMB_CONV (TY_TM_BETA_VAR v Rator)
           end

structure Map = Redblackmap

(* count from zero to indicate last argument, up to #args - 1 to indicate
   first argument *)
fun arg_CONV 0 c t = RAND_CONV c t
  | arg_CONV n c t = TY_TM_RATOR_CONV (arg_CONV (n - 1) c) t

fun foldri f acc list = let
  fun foldthis (e, (acc, n)) = (f(n, e, acc), n + 1)
in
  #1 (foldr foldthis (acc,0) list)
end


fun print_ty_tm (inL ty) = (print "TY "; print_type ty)
  | print_ty_tm (inR tm) = (print "TM "; print_term tm)

fun print_ty_tms1 [] = print "]\n"
  | print_ty_tms1 [x] = (print_ty_tm x; print "]\n")
  | print_ty_tms1 (x::xs) = (print_ty_tm x; print ", "; print_ty_tms1 xs)
fun print_ty_tms xs = (print "["; print_ty_tms1 xs)


fun munge_bvars absmap th = let
  fun recurse curposn btyvarposns bvarposns (donebtyvars, donebvars, acc) t =
    let fun ty_tm_comb t = let
          val (f, args) = strip_ty_tm_comb t
          fun argfold (n, inR arg, A) =
              recurse (curposn o arg_CONV n) btyvarposns bvarposns A arg
            | argfold (n, inL (tyarg:hol_type), A) = A
        in
          case Map.peek(absmap, f) of
            NONE => foldri argfold (donebtyvars, donebvars, acc) args
          | SOME abs_t => let
              val (abs_bvars, _) = strip_ty_tm_abs abs_t
              val paired_up = ListPair.zip (args, abs_bvars)
              fun foldthis ((inR arg, inR absv), acc as (dbtyvars, dbvars, actionlist)) =
                  if HOLset.member(dbvars, arg) then acc
                  else (case Map.peek(bvarposns, arg) of
                          NONE => acc
                        | SOME p =>
                          let val absv_name = fst (dest_var absv)
                          in
                            (dbtyvars, HOLset.add(dbvars, arg),
                             p (ALPHA_NAME_CONV absv_name):: actionlist)
                          end)
                | foldthis ((inL arg, inL absv), acc as (dbtyvars, dbvars, actionlist)) =
                  if HOLset.member(dbtyvars, arg) then acc
                  else (case Map.peek(btyvarposns, arg) of
                          NONE => acc
                        | SOME p =>
                          let val absv_name = #1 (dest_var_type absv)
                          in
                            (HOLset.add(dbtyvars, arg), dbvars,
                             p (TY_ALPHA_NAME_CONV absv_name):: actionlist)
                          end)
                | foldthis _ = raise ERR "munge_bvars.COMB(foldthis)" "impossible type vs term"
              val A as (newdbtyvars, newdbvars, newacc) =
                  List.foldl foldthis (donebtyvars, donebvars, acc) paired_up
            in
              foldri argfold A args
            end
        end
    in
      case dest_term t of
        COMB _ => ty_tm_comb t
      | TYCOMB _ => ty_tm_comb t
      | LAMB(bv, body) => let
          val newposnmap = Map.insert(bvarposns, bv, curposn)
          val (newdonemap, restore) =
              (HOLset.delete(donebvars, bv), (fn m => HOLset.add(m, bv)))
              handle HOLset.NotFound =>
                     (donebvars, (fn m => HOLset.delete(m, bv)
                                     handle HOLset.NotFound => m))
          val (dbtyvars, dbvars, actions) =
              recurse (curposn o ABS_CONV) btyvarposns newposnmap (donebtyvars, newdonemap, acc) body
        in
          (dbtyvars, restore dbvars, actions)
        end
      | TYLAMB(bv, body) => let
          val newposnmap = Map.insert(btyvarposns, bv, curposn)
          val (newdonemap, restore) =
              (HOLset.delete(donebtyvars, bv), (fn m => HOLset.add(m, bv)))
              handle HOLset.NotFound =>
                     (donebtyvars, (fn m => HOLset.delete(m, bv)
                                       handle HOLset.NotFound => m))
          val (dbtyvars, dbvars, actions) =
              recurse (curposn o TY_ABS_CONV) newposnmap bvarposns (newdonemap, donebvars, acc) body
        in
          (restore dbtyvars, dbvars, actions)
        end
      | _ => (donebtyvars, donebvars, acc)
    end
in
  recurse I (Map.mkDict Type.compare) (Map.mkDict Term.compare)
            (empty_tyset, empty_tmset, []) (concl th)
end



(* Modified HO_PART_MATCH by PVH on Apr. 25, 2005: code was broken;
   repaired by tightening "foldthis" condition for entry to "bound_to_abs";
   see longish note at bottom for more details. *)

(* "bound_vars" returns set of bound type and term variables within term t *)
(* "t" argument is actual term, "acc" is pair of accumulating sets, orig. empty *)
local
 fun bound_vars1 t (acc as (tvs,vs)) =
  case dest_term t
   of LAMB(v,b) => bound_vars1 b (tvs,HOLset.add(vs, v))
    | COMB(l,r) => bound_vars1 l (bound_vars1 r acc)
    | TYLAMB(a,b) => bound_vars1 b (HOLset.add(tvs, a),vs)
    | TYCOMB(f,a) => bound_vars1 f acc
    | otherwise => acc
in
fun bound_vars t = bound_vars1 t (empty_tyset,empty_tmset)
end


fun HO_PART_MATCH partfn th =
 let val sth = TY_TM_SPEC_ALL th
     val bod = concl sth
     val pbod = partfn bod
     val atys = type_vars_in_term bod
     fun is_fun_or_univ_type ty = can dom_rng ty orelse can dest_univ_type ty
     val possbetas = mapfilter (fn v => (v,TY_TM_BETA_VAR v bod))
                               (filter (is_fun_or_univ_type o type_of) (free_vars bod))
     fun finish_fn rkin kdin tyin ivs =
       let val npossbetas =
            if rkin=0 andalso null kdin andalso null tyin then possbetas
            else map ((inst tyin o inst_rank_kind rkin kdin) ## I) possbetas
       in if null npossbetas then Lib.I
          else CONV_RULE (EVERY_CONV (mapfilter
                                        (TRY_CONV o C (op_assoc eq) npossbetas)
                                        ivs))
       end
     val lconsts = HOLset.intersection (FVL[pbod]empty_tmset, hyp_frees th)
     val lkdconsts = HOLset.listItems (hyp_kdvars th)
     val ltyconsts = HOLset.listItems (hyp_tyvars th)
 in fn tm =>
    let val (tmin,tyin,kdin,rkin) = ho_kind_match_term lkdconsts ltyconsts lconsts pbod tm
        val (tmbtvs,tmbvs) = bound_vars tm
        fun foldthis ({redex,residue}, acc) =
            if (is_abs residue orelse is_tyabs residue) andalso
               all (fn inR v => HOLset.member(tmbvs, v)
                     | inL a => HOLset.member(tmbtvs, a))
                   (fst (strip_ty_tm_abs residue))
            then Map.insert(acc, redex, residue)
            else acc
        val bound_to_abs = List.foldl foldthis (Map.mkDict Term.compare) tmin
        val sth0 = INST_RK_KD_TY (rkin,kdin,tyin) sth
        val sth0c = concl sth0
        val (sth1, tyin', tmin') =
            case match_bvs tm (partfn sth0c) ([],[]) of
              ([],[]) => (sth0, [], tmin)
            | bvms => let
                val (tyavoids,avoids) = look_for_avoids bvms sth0c (empty_tyset,empty_tmset)
                fun g (a, acc) = (a |-> gen_var_type (kind_of a)) :: acc
                val tyin' = HOLset.foldl g [] tyavoids
                fun f (v, acc) = (v |-> genvar (type_of v)) :: acc
                val newinst = HOLset.foldl f [] avoids
                val newthm = INST newinst (PURE_INST_TYPE tyin' sth0)
                val tmin' = map (fn {residue, redex} =>
                                    {residue = residue,
                                     redex = Term.subst newinst (Term.inst tyin' redex)}) tmin
                val thmc = concl newthm
              in
                (EQ_MP (ALPHA thmc (deep_alpha bvms thmc)) newthm, tyin', tmin')
              end
        val sth2 =
            if Map.numItems bound_to_abs = 0 then sth1
            else
              CONV_RULE (EVERY_CONV (#3 (munge_bvars bound_to_abs sth1))) sth1
        val th0 = INST tmin' (PURE_INST_TYPE tyin' sth2)
        val th1 = finish_fn rkin kdin tyin (map #redex tmin) th0
    in
      th1
    end
 end

end


fun HO_MATCH_MP ith =
 let val sth =
       let val tm = concl ith
           val (avs,bod) = strip_all_forall tm
           val (ant,_) = dest_imp_only bod
       in case partition (C type_var_occurs ant +-+ C var_occurs ant) avs
           of (_,[]) => ith
            | (svs,pvs) =>
              let val th1 = TY_TM_SPECL avs (ASSUME tm)
                  val th2 = TY_TM_GENL svs (DISCH ant (TY_TM_GENL pvs (UNDISCH th1)))
              in MP (DISCH tm th2) ith
              end
       end handle HOL_ERR _ => raise ERR "MATCH_MP" "Not an implication"
     val match_fun = HO_PART_MATCH (fst o dest_imp_only) sth
 in fn th =>
     MP (match_fun (concl th)) th
     handle HOL_ERR _ => raise ERR "MATCH_MP" "No match"
 end

(* =====================================================================*)
(* The "resolution" tactics for HOL (outmoded technology, but           *)
(* sometimes useful) uses RES_CANON and SPEC_ALL 		        *)
(* =====================================================================*)
(*                                                                      *)
(* Put a theorem 							*)
(*									*)
(*	 |- !x. t1 ==> !y. t2 ==> ... ==> tm ==>  t 			*)
(*									*)
(* into canonical form for resolution by splitting conjunctions apart   *)
(* (like IMP_CANON but without the stripping out of quantifiers and only*)
(* outermost negations being converted to implications).		*)
(*									*)
(*   ~t            --->          t ==> F        (at outermost level)	*)
(*   t1 /\ t2	  --->		t1,   t2				*)
(*   (t1/\t2)==>t  --->		t1==> (t2==>t)				*)
(*   (t1\/t2)==>t  --->		t1==>t, t2==>t				*)
(*									*)
(*									*)
(* Modification provided by David Shepherd of Inmos to make resolution  *)
(* work with equalities as well as implications. HOL88.1.08,23 jun 1989.*)
(*									*)
(*   t1 = t2      --->          t1=t2, t1==>t2, t2==>t1			*)
(*									*)
(* Modification provided by T Melham to deal with the scope of 		*)
(* universal quantifiers. [TFM 90.04.24]				*)
(*									*)
(*   !x. t1 ==> t2  --->  t1 ==> !x.t2   (x not free in t1)		*)
(*									*)
(* The old code is given below:						*)
(* 									*)
(*    letrec RES_CANON_FUN th =						*)
(*     let w = concl th in						*)
(*     if is_conj w 							*)
(*     then RES_CANON_FUN(CONJUNCT1 th)@RES_CANON_FUN(CONJUNCT2 th)	*)
(*     else if is_imp w & not(is_neg w) then				*)
(* 	let ante,conc = dest_imp w in					*)
(* 	if is_conj ante then						*)
(* 	    let a,b = dest_conj ante in					*)
(* 	    RES_CANON_FUN 						*)
(* 	    (DISCH a (DISCH b (MP th (CONJ (ASSUME a) (ASSUME b)))))	*)
(* 	else if is_disj ante then					*)
(* 	    let a,b = dest_disj ante in					*)
(* 	    RES_CANON_FUN (DISCH a (MP th (DISJ1 (ASSUME a) b))) @	*)
(* 	    RES_CANON_FUN (DISCH b (MP th (DISJ2 a (ASSUME b))))	*)
(* 	else								*)
(* 	map (DISCH ante) (RES_CANON_FUN (UNDISCH th))			*)
(*     else [th];							*)
(* 									*)
(* This version deleted for HOL 1.12 (see below)	[TFM 91.01.17]  *)
(*									*)
(* let RES_CANON = 							*)
(*     letrec FN th = 							*)
(*       let w = concl th in						*)
(*       if (is_conj w) then FN(CONJUNCT1 th) @ FN(CONJUNCT2 th) else	*)
(*       if ((is_imp w) & not(is_neg w)) then				*)
(*       let ante,conc = dest_imp w in					*)
(*       if (is_conj ante) then						*)
(*          let a,b = dest_conj ante in					*)
(* 	    let ath = ASSUME a and bth = ASSUME b			*)
(*          in FN (DISCH a (DISCH b (MP th (CONJ ath bth)))) else       *)
(*       if is_disj ante then                                           *)
(*         let a,b = dest_disj ante in					*)
(*         let ath = ASSUME a and bth = ASSUME b 			*)
(* 	   in FN (DISCH a (MP th (DISJ1 ath b))) @			*)
(*            FN (DISCH b (MP th (DISJ2 a bth)))                        *)
(*       else map (GEN_ALL o (DISCH ante)) (FN (UNDISCH th))    	*)
(*       else if is_eq w then						*)
(*        let l,r = dest_eq w in					*)
(*            if (type_of l = ":bool")                                  *)
(*            then let (th1,th2) = EQ_IMP_RULE th                       *)
(*                 in (GEN_ALL th) . ((FN  th1) @ (FN  th2)) 		*)
(*            else [GEN_ALL th]                                         *)
(*        else [GEN_ALL th] in                                          *)
(*     \th. (let vars,w = strip_forall(concl th) in			*)
(*           let th1 = if (is_neg w)	 				*)
(* 	  		then NOT_ELIM(SPEC_ALL th) 			*)
(* 			else (SPEC_ALL th) in				*)
(*               map GEN_ALL (FN th1) ? failwith `RES_CANON`);		*)
(* ---------------------------------------------------------------------*)
(* ---------------------------------------------------------------------*)
(* New RES_CANON for version 1.12.			 [TFM 90.12.07] *)
(* 									*)
(* The complete list of transformations is now:				*)
(*									*)
(*   ~t              --->       t ==> F        (at outermost level)	*)
(*   t1 /\ t2	     --->	t1, t2	       (at outermost level)	*)
(*   (t1/\t2)==>t    --->	t1==>(t2==>t), t2==>(t1==>t)		*)
(*   (t1\/t2)==>t    --->	t1==>t, t2==>t				*)
(*   t1 = t2         --->       t1==>t2, t2==>t1			*)
(*   !x. t1 ==> t2   --->       t1 ==> !x.t2   (x not free in t1)	*)
(*   !:a. t1 ==> t2  --->       t1 ==> !:a.t2  (a not free in t1)	*)
(*   (?x.t1) ==> t2  --->	!x'. t1[x'/x] ==> t2			*)
(*   (?:a.t1) ==> t2 --->	!:a'. t1[a'/a] ==> t2			*)
(*									*)
(* The function now fails if no implications can be derived from the 	*)
(* input theorem.							*)
(* ---------------------------------------------------------------------*)

local fun not_elim th =
       if is_neg(concl th) then (true, NOT_ELIM th) else (false, th)
fun canon (fl,th) =
   let val w = concl th
   in
   if is_conj w
     then let val (th1,th2) = CONJ_PAIR th
          in (canon(fl,th1) @ canon(fl,th2))
          end else
   if is_imp w andalso not(is_neg w) then
     let val (ant,_) = dest_imp w
     in if is_conj ant
        then let val (conj1,conj2) = dest_conj ant
                 val cth = MP th (CONJ (ASSUME conj1) (ASSUME conj2))
                 val th1 = DISCH conj2 cth
                 and th2 = DISCH conj1 cth
             in
                canon(true,DISCH conj1 th1) @ canon(true,DISCH conj2 th2)
             end else
        if is_disj ant
        then let val (disj1,disj2) = dest_disj ant
                 val ath = DISJ1 (ASSUME disj1) disj2
                 and bth = DISJ2 disj1 (ASSUME disj2)
                 val th1 = DISCH disj1 (MP th ath)
                 and th2 = DISCH disj2 (MP th bth)
             in
                 canon(true,th1) @ canon(true,th2)
             end else
        if is_exists ant
        then let val (Bvar,Body) = dest_exists ant
                 val newv = variant(thm_frees th) Bvar
                 val newa = subst [Bvar |-> newv] Body
                 val th1  = MP th (EXISTS (ant,newv) (ASSUME newa))
             in
               canon(true,DISCH newa th1)
             end else
        if is_tyexists ant
        then let val (Bvar,Body) = dest_tyexists ant
                 val ftvs = HOLset.listItems (HOLset.addList (hyp_tyvars th, type_vars_in_term(concl th)))
                 val newv = variant_type ftvs Bvar
                 val newa = inst [Bvar |-> newv] Body
                 val th1  = MP th (TY_EXISTS (ant,newv) (ASSUME newa))
             in
               canon(true,DISCH newa th1)
             end
        else map (TY_TM_GEN_ALL o (DISCH ant)) (canon (true,UNDISCH th))
     end else
   if is_eq w andalso (type_of (rand w) = Type.bool)
   then let val (th1,th2) = EQ_IMP_RULE th
        in (if fl then [TY_TM_GEN_ALL th] else [])@canon(true,th1)@canon(true,th2)
        end else
   if is_forall w orelse is_tyforall w then
     let val (vs,_) = strip_all_forall w
         val fvs = HOLset.listItems (FVL[concl th] (hyp_frees th))
         val ftvs = HOLset.listItems (HOLset.addList (hyp_tyvars th, type_vars_in_term(concl th)))
         val nvs = itlist (fn inR v => (fn nv => inR(variant (mapfilter outR nv @ fvs) v)::nv)
                            | inL v => (fn nv => inL(variant_type (mapfilter outL nv @ ftvs) v)::nv)
                          ) vs []
     in
        canon (fl, TY_TM_SPECL nvs th)
     end else
   if fl then [TY_TM_GEN_ALL th] else []
   end

fun CORE_RES_CANON finisher th =
 let val conjlist = CONJUNCTS (TY_TM_SPEC_ALL th)
     fun operate th accum =
          accum @ map finisher (canon (not_elim (TY_TM_SPEC_ALL th)))
     val imps = Lib.rev_itlist operate conjlist []
 in Lib.assert (op not o null) imps
 end handle HOL_ERR _
 => raise ERR "RES_CANON" "No implication is derivable from input thm"
in
fun OLD_RES_CANON th =
 let val ftyvs = HOLset.listItems (HOLset.difference
                  (HOLset.addList(empty_tyset, type_vars_in_term(concl th)), hyp_tyvars th))
 in if null ftyvs then CORE_RES_CANON GEN_ALL th
    else
     let val gvs = map (fn a => genvar (mk_app_type(gen_var_type(kind_of a ==> typ rho), a))) ftyvs
         val ty_hyp = LIST_CONJ (map REFL gvs)
         val ty_con = concl ty_hyp
         val th1 = ADD_ASSUM ty_con th
         val REM_TY_HYP = fn th => MP (DISCH ty_con th) ty_hyp
     in CORE_RES_CANON (GEN_ALL o REM_TY_HYP) th1
     end
 end

fun RES_CANON th =
 if is_omega th then CORE_RES_CANON TY_TM_GEN_ALL th
 else OLD_RES_CANON th
end

(*======================================================================*)
(*       Routines supporting the definition of types                    *)
(*                                                                      *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge              *)
(*                                                                      *)
(* NAME: define_new_type_bijections 					*)
(*									*)
(* DESCRIPTION: define isomorphism constants based on a type definition.*)
(*									*)
(* USAGE: define_new_type_bijections name ABS REP tyax                  *)
(*									*)
(* ARGUMENTS: tyax -- a type-defining axiom of the form returned by	*)
(*		     new_type_definition. For example:			*)
(*									*)
(* 			?rep. TYPE_DEFINITION P rep			*)
(*									*)
(*            ABS  --- the name of the required abstraction function    *)
(*									*)
(*            REP  --- the name of the required representation function *)
(*									*)
(*            name --- the name under which the definition is stored    *)
(*									*)
(* SIDE EFFECTS:    Introduces a definition for two constants `ABS` and *)
(*                  (--`REP`--) by the constant specification:          *)
(*									*)
(*  		   |- ?ABS REP. (!a. ABS(REP a) = a) /\                 *)
(*                              (!r. P r = (REP(ABS r) = r)             *)
(*									*)
(*                 The resulting constant specification is stored under *)
(*                 the name given as the first argument.                *)
(*									*)
(* FAILURE: if input theorem of wrong form.			        *)
(*									*)
(* RETURNS: The defining property of the representation and abstraction *)
(*          functions, given by:                                        *)
(*             								*)
(*           |- (!a. ABS(REP a) = a) /\ (!r. P r = (REP(ABS r) = r)   	*)
(* ---------------------------------------------------------------------*)

fun define_new_type_bijections{name,ABS,REP,tyax} =
  if not(HOLset.isEmpty (hypset tyax))
  then raise ERR "define_new_type_bijections"
                 "input theorem must have no assumptions"
  else
  let val (P,rep) = case strip_comb(snd(dest_exists(concl tyax)))
                    of (_,[P,rep]) => (P,rep)
                     | _ => raise Match
      val (a,r) = Type.dom_rng (type_of rep)
  in Rsyntax.new_specification
      {name=name,
       sat_thm=MP(SPEC P (INST_TYPE[beta |-> a, alpha |-> r]ABS_REP_THM)) tyax,
       consts = [{const_name=REP, fixity=Prefix},
                 {const_name=ABS, fixity=Prefix}]}
  end
  handle e => raise (wrap_exn "Drule" "define_new_type_bijections" e)

(* ---------------------------------------------------------------------*)
(* NAME: prove_rep_fn_one_one	 					*)
(*									*)
(* DESCRIPTION: prove that a type representation function is one-to-one.*)
(*									*)
(* USAGE: if th is a theorem of the kind returned by the ML function	*)
(*        define_new_type_bijections:					*)
(*									*)
(*           |- (!a. ABS(REP a) = a) /\ (!r. P r = (REP(ABS r) = r)   	*)
(*									*)
(*	 then prove_rep_fn_one_one th will prove and return a theorem	*)
(*	 stating that the representation function REP is one-to-one:	*)
(*									*)
(*	    |- !a a'. (REP a = REP a') = (a = a')			*)
(*									*)
(* ---------------------------------------------------------------------*)

fun prove_rep_fn_one_one th =
   let val thm = CONJUNCT1 th
       val (_,Body) = dest_forall(concl thm)
       val (A, Rand) = dest_comb(lhs Body)
       val (R, _)= dest_comb Rand
       val (aty,rty) = case Type.dest_type (type_of R)
                       of (_,[aty,rty]) => (aty,rty)
                        | _ => raise Match
       val a = mk_primed_var("a", aty)
       val a' = variant [a] a
       val a_eq_a' = mk_eq(a,a')
       and Ra_eq_Ra' = mk_eq(mk_comb(R,a), mk_comb(R, a'))
       val th1 = AP_TERM A (ASSUME Ra_eq_Ra')
       val ga1 = genvar aty
       and ga2 = genvar aty
       val th2 = SUBST [ga1 |-> SPEC a thm, ga2 |-> SPEC a' thm]
                       (mk_eq(ga1, ga2)) th1
       val th3 = DISCH a_eq_a' (AP_TERM R (ASSUME a_eq_a'))
   in
      GEN a (GEN a' (IMP_ANTISYM_RULE (DISCH Ra_eq_Ra' th2) th3))
   end
   handle HOL_ERR _ => raise ERR "prove_rep_fn_one_one"  ""
        | Bind => raise ERR "prove_rep_fn_one_one"
                            ("Theorem not of right form: must be\n "^
                             "|- (!a. to (from a) = a) /\\ "^
                             "(!r. P r = (from (to r) = r))")

(* ---------------------------------------------------------------------*)
(* NAME: prove_rep_fn_onto	 					*)
(*									*)
(* DESCRIPTION: prove that a type representation function is onto. 	*)
(*									*)
(* USAGE: if th is a theorem of the kind returned by the ML function	*)
(*        define_new_type_bijections:					*)
(*									*)
(*           |- (!a. ABS(REP a) = a) /\ (!r. P r = (REP(ABS r) = r)   	*)
(*									*)
(*	 then prove_rep_fn_onto th will prove and return a theorem	*)
(*	 stating that the representation function REP is onto:		*)
(*									*)
(*	    |- !r. P r = (?a. r = REP a)				*)
(*									*)
(* ---------------------------------------------------------------------*)

fun prove_rep_fn_onto th =
   let val (th1,th2) = case CONJUNCTS th
                       of [th1,th2] => (th1,th2)
                        | _ => raise Match
       val (Bvar,Body) = dest_forall(concl th2)
       val (_,eq) = dest_eq Body
       val (RE, ar) = dest_comb(lhs eq)
       val a = mk_primed_var("a", type_of ar)
       val sra = mk_eq(Bvar, mk_comb(RE, a))
       val ex = mk_exists(a, sra)
       val imp1 = EXISTS (ex,ar) (SYM(ASSUME eq))
       val v = genvar (type_of Bvar)
       and A = rator ar
       and ass = AP_TERM RE (SPEC a th1)
       val th = SUBST[v |-> SYM(ASSUME sra)]
                 (mk_eq(mk_comb(RE,mk_comb(A, v)),v)) ass
       val imp2 = CHOOSE (a,ASSUME ex) th
       val swap = IMP_ANTISYM_RULE (DISCH eq imp1) (DISCH ex imp2)
   in
   GEN Bvar (TRANS (SPEC Bvar th2) swap)
   end
   handle HOL_ERR _ => raise ERR "prove_rep_fn_onto" ""
        | Bind => raise ERR "prove_rep_fn_onto"
                            ("Theorem not of right form: must be\n "^
                             "|- (!a. to (from a) = a) /\\ "^
                             "(!r. P r = (from (to r) = r))")

(* ---------------------------------------------------------------------*)
(* NAME: prove_abs_fn_onto	 					*)
(*									*)
(* DESCRIPTION: prove that a type abstraction function is onto. 	*)
(*									*)
(* USAGE: if th is a theorem of the kind returned by the ML function	*)
(*        define_new_type_bijections:					*)
(*									*)
(*           |- (!a. ABS(REP a) = a) /\ (!r. P r = (REP(ABS r) = r)   	*)
(*									*)
(*	 then prove_abs_fn_onto th will prove and return a theorem	*)
(*	 stating that the abstraction function ABS is onto:		*)
(*									*)
(*	    |- !a. ?r. (a = ABS r) /\ P r				*)
(*									*)
(* ---------------------------------------------------------------------*)

fun prove_abs_fn_onto th =
   let val (th1,th2) = case CONJUNCTS th
                       of [th1,th2] => (th1,th2)
                        | _ => raise Match
       val (bv_th1,Body) = dest_forall(concl th1)
       val (A,Rand) = dest_comb(lhs Body)
       val R = rator Rand
       val rb = mk_comb(R, bv_th1)
       val bth1 = SPEC bv_th1 th1
       val thm1 = EQT_ELIM(TRANS (SPEC rb th2) (EQT_INTRO (AP_TERM R bth1)))
       val thm2 = SYM bth1
       val (r,Body) = dest_forall(concl th2)
       val P = rator(lhs Body)
       val ex = mk_exists(r,
                  mk_conj(mk_eq(bv_th1,mk_comb(A, r)), mk_comb(P, r)))
   in GEN bv_th1 (EXISTS(ex,rb) (CONJ thm2 thm1))
   end
   handle HOL_ERR _ => raise ERR "prove_abs_fn_onto" ""
        | Bind => raise ERR "prove_abs_fn_one_onto"
                            ("Theorem not of right form: must be\n "^
                             "|- (!a. to (from a) = a) /\\ "^
                             "(!r. P r = (from (to r) = r))")

(* ---------------------------------------------------------------------*)
(* NAME: prove_abs_fn_one_one	 					*)
(*									*)
(* DESCRIPTION: prove that a type abstraction function is one-to-one. 	*)
(*									*)
(* USAGE: if th is a theorem of the kind returned by the ML function	*)
(*        define_new_type_bijections:					*)
(*									*)
(*           |- (!a. ABS(REP a) = a) /\ (!r. P r = (REP(ABS r) = r)   	*)
(*									*)
(*	 then prove_abs_fn_one_one th will prove and return a theorem	*)
(*	 stating that the abstraction function ABS is one-to-one:	*)
(*									*)
(*	    |- !r r'. P r ==>						*)
(*		      P r' ==>						*)
(*		      (ABS r = ABS r') ==> (r = r')			*)
(*									*)
(* ---------------------------------------------------------------------*)

fun prove_abs_fn_one_one th =
   let val (th1,th2) = case CONJUNCTS th
                       of [th1,th2] => (th1,th2)
                        | _ => raise Match
       val (r, Body) = dest_forall(concl th2)
       val P = rator(lhs Body)
       val (A, Rand) = dest_comb(lhs(snd(dest_forall(concl th1))))
       val R = rator Rand
       val r' = variant [r] r
       val r_eq_r' = mk_eq (r, r')
       val Pr = mk_comb(P, r)
       val Pr' = mk_comb(P, r')
       val as1 = ASSUME Pr
       and as2 = ASSUME Pr'
       val t1 = EQ_MP (SPEC r th2) as1
       and t2 = EQ_MP (SPEC r' th2) as2
       val eq = mk_eq(mk_comb(A, r), mk_comb(A, r'))
       val v1 = genvar(type_of r)
       and v2 = genvar(type_of r)
       val i1 = DISCH eq (SUBST [v1 |-> t1, v2 |-> t2]
                            (mk_eq(v1,v2)) (AP_TERM R (ASSUME eq)))
       val i2    = DISCH r_eq_r' (AP_TERM A (ASSUME r_eq_r'))
       val thm   = IMP_ANTISYM_RULE i1 i2
       val disch = DISCH Pr (DISCH Pr' thm)
   in
     GEN r (GEN r' disch)
   end
   handle HOL_ERR _ => raise ERR "prove_abs_fn_one_one"  ""
        | Bind => raise ERR "prove_abs_fn_one_one"
                            ("Theorem not of right form: must be\n "^
                             "|- (!a. to (from a) = a) /\\ "^
                             "(!r. P r = (from (to r) = r))")

(*---------------------------------------------------------------------------*)
(* Rules related to "semantic tags" for controlling rewriting                *)
(*---------------------------------------------------------------------------*)

val is_comm = can (kind_match_term comm_tm);
val is_assoc = can (kind_match_term assoc_tm);

(*---------------------------------------------------------------------------*)
(* Classify a pair of theorems as one assoc. thm and one comm. thm. Then     *)
(* return pair (A,C) where A has the form |- f(x,f(y,z)) = f(f(x,y),z)       *)
(*---------------------------------------------------------------------------*)

fun regen th = GENL (free_vars_lr (concl th)) th

fun norm_ac (th1,th2) =
 let val th1' = SPEC_ALL th1
     val th2' = SPEC_ALL th2
     val tm1 = concl th1'
     val tm2 = concl th2'
 in if is_comm tm2 then
      if is_assoc tm1 then (regen th1',regen th2')
      else
        let val th1a = SYM th1'
        in if is_assoc (concl th1a)
           then (regen th1a,regen th2')
           else (HOL_MESG "unable to AC-normalize input";
                 raise ERR "norm_ac" "failed")
        end
    else if is_comm tm1 then
      if is_assoc tm2 then (regen th2',regen th1')
      else
        let val th2a = SYM th2'
        in if is_assoc (concl th2a) then (regen th2a,regen th1')
           else (HOL_MESG "unable to AC-normalize input";
                 raise ERR "norm_ac" "failed")
        end
    else (HOL_MESG "unable to AC-normalize input";
          raise ERR "norm_ac" "failed")
 end

(*---------------------------------------------------------------------------*)
(* Take an AC pair, normalize them, then prove left-commutativity            *)
(*---------------------------------------------------------------------------*)

fun MK_AC_LCOMM (th1,th2) =
   let val (a,c) = norm_ac(th1,th2)
       val lcomm = MATCH_MP (MATCH_MP LCOMM_THM a) c
   in
     (regen (SYM (SPEC_ALL a)), c, lcomm)
   end

end (* Drule *)

(* ----------------------------------------------------------------------
    HO_PART_MATCH and bound variables
   ----------------------------------------------------------------------

Given

  val th = GSYM RIGHT_EXISTS_AND_THM
         = |- P /\ (?x. Q x) = ?x. P /\ Q x

the old implementation would come back from

  HO_REWR_CONV th ``P x /\ ?y. Q y``

with

  (P x /\ ?y. Q y) = (?x'. P x /\ Q x')

This is because of the following: in HO_PART_MATCH, there is code that
attempts to rename bound variables from the rewrite theorem so that
they match the bound variables in the original term.

After performing the ho_match_term, and doing the instantiation, the
resulting theorem is

  (P x /\ ?x. Q x) = (?x'. P x /\ Q x')

The renaming on the rhs has to happen to avoid unsoundness, and
happens immediately in the name-carrying kernel, and will happen
whenever a dest_abs is done in the dB kernel.  Anyway, in the fixup
phase, the implementation first notices that ?x.Q x in the pattern
corresponds to ?y. Q y in the term.  It then passes over the term
replacing bound x's with y's.  (In the dB kernel, it can't see that
the bound variable on the right is actually still an x because
dest_abs will rename the x to x'.)

So, I thought I would fix this by doing the bound-variable fixup on
the pattern theorem before it was instantiated.  So, I look at

  P /\ ?x. Q x

compare it to P x /\ ?y. Q y ("match_bvs"), and see that bound x 
needs to be replaced by y throughout the theorem ("deep_alpha bvms"), 
giving

  (P /\ ?y. Q y) = (?y. P /\ Q y)

Then the instantiation can be done, producing

  (P x /\ ?y. Q y) = (?y. P x /\ Q y)

and it's all lovely.  (This is also more efficient than the current
method because the traversal is only of the original theorem, not its
possibly much larger instantiation.)

Unfortunately, there are still problems.  Consider, this LHS

  p /\ ?P. FINITE P

when you do the bound variable fix to the rewrite theorem early, you
get

  (P /\ ?P. Q P) = (?P'. P /\ Q P')

The free variables in the theorem itself get in the way.  The fix is
to examine whether or not the new bound variable clashes with a named
variable in the body of the theorem ("look_for_avoids bvms").  If so, then 
the theorem has that variable instantiated to a genvar.  (The instantiation 
returned by ho_kind_match_term also needs to be adjusted because it may be 
expecting to instantiate some of the pattern theorem's free variables.)

So, the code in match_bvs figures out what renamings of bound
variables need to happen, and then a traversal of the *whole* theorem
takes to see what free variables need to be instantiated into genvars.
Then, given the example, the main code in HO_PART_MATCH will produce

  (%gv /\ ?x. Q x) = (?x. %gv /\ Q x)

before then fixing the bound variables to produce

  (%gv /\ ?P. Q P) = (?P. %gv /\ Q P)

Finally, this theorem will be instantiated with bindings for Q and
%gv [%gv |-> p, Q |-> FINITE].

                    ------------------------------

Part 2.

Even with the above in place, the ho-part matcher can make a mess of
things like the congruence rule for RES_FORALL_CONG,

  |- (P = Q) ==> (!x. x IN Q ==> (f x = g x)) ==>
     (RES_FORALL P f = RES_FORALL Q g)

HO_PART_MATCH only gets called with its "partfn" being to look at the
LHS of the last equation.  Then, when the side conditions are looked
over, x gets picked as a bound variable, and any bound variable in 
what f will be instantiated with gets ignored.

The code in munge_bvars gets around this failing by searching the
whole theorem for instances of variables that are going to be
instantiated with abstractions that are next to bound variables.  (In
the example, this search will find f applied to the bound x.)  If such
a situation is found, it specifies that the bound variable be renamed
to match the bound variable of the abstraction.

In this way

   !y::P. Q y

won't get rewritten to

   !x::P'. Q' x

                    ------------------------------

Part 3. (By Peter V. Homeier)

The above code was broken for higher order rewriting, such as

val th = ASSUME ``!f:'a->'b. A (\x:'c. B (f (C x)) :'d) = (\x. f x)``;
val tm = ``A (\rose:'c. B (g (C rose :'a) (C rose) :'b) :'d) : 'a->'b``;
HO_PART_MATCH lhs th tm;

produced

   A (\rose. B (g (C rose) (C rose))) = (\gvar. g gvar gvar)

where gvar was a freshly generated "genvar", instead of the correct

   A (\rose. B (g (C rose) (C rose))) = (\rose. g rose rose)

The reason the prior code did not work was that not only was the
match of f with (\y. Q y) recognized for the Part 2 example above,
but also the match of f with (\gvar. g gvar gvar) in the "rose" example.
The code then "munged" the result by trying to change instances of the
"rose" bound variable to "gvar".

This was fixed by tightening the condition for entrance to the set of
bound variables which are to be so "munged", by adding the condition
that the bound variables ("y" in the Part 2 example, "gvar" in this one)
must all be contained within the set of bound variables within the term
"tm".  If they are not, then the "munge" operation is not needed, since
that attempts to alter bound variable names to fit the given term,
and if the suggested new variable names did not come from the term,
there is no reason to change the old ones.
*)
