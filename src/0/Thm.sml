(* ===================================================================== *)
(* FILE          : thm.sml                                               *)
(* DESCRIPTION   : The abstract data type of theorems. Mostly            *)
(*                 translated from the hol88 source.                     *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon, University of Cambridge              *)
(*                     Konrad Slind, University of Calgary               *)
(* DATE          : September 10, 1991                                    *)
(* Modified      : September 23, 1997, Ken Larsen                        *)
(* ===================================================================== *)

structure Thm :> Thm =
struct

type tag = Tag.tag
open Exception Lib Dsyntax Term;

infix 5 |->;

val EQ = Portable.pointer_eq;

local fun thm_err s1 s2 =
           HOL_ERR {origin_structure="Thm",origin_function=s1, message=s2}
in
   fun THM_ERR f m = raise thm_err f m
   fun Assert b s1 s2 = if b then () else THM_ERR s1 s2
end;

(*---------------------------------------------------------------------------*
 * The type of theorems and simple operations.                               *
 *---------------------------------------------------------------------------*)
datatype thm = THM of Tag.tag * term list * term

fun hyp  (THM(_,asl,_)) = asl
and concl(THM(_,_,c)) = c
and tag  (THM(tg,_,_))  = tg
and dest_thm(THM(_,asl,w)) = (asl,w)   (* for compatibility with old code. *)
fun make_thm R seq = (Count.inc_count R; THM seq);

(*---------------------------------------------------------------------------*
 * Miscellaneous syntax routines.                                            *
 *---------------------------------------------------------------------------*)
fun insert_hyp h asl = if exists (aconv h) asl then asl else h::asl;
fun union_hyp asl1 asl2 =
  if EQ(asl1,asl2) orelse asl2 = [] then asl1
  else itlist insert_hyp asl1 asl2;

val bool = Type.bool;
fun thm_free_vars (THM(_,asl,c)) = free_varsl (c::asl);
fun tag_hyp_union thm_list =
  (itlist (Tag.merge o tag) (tl thm_list) (tag (hd thm_list)),
   itlist (union_hyp o hyp) thm_list []);
fun dom_ty ty = fst (Type.dom_rng ty)
fun rng_ty ty = snd (Type.dom_rng ty)

(*---------------------------------------------------------------------------
 * Construct a theorem and slap the tag of the oracle on it.
 *---------------------------------------------------------------------------*)
fun mk_oracle_thm tg (asl,c) =
  (Assert (Lib.all (fn tm => type_of tm = bool) (c::asl))
          "mk_oracle_thm"  "Not a proposition!";
   make_thm Count.Oracle (tg,asl,c));


(*---------------------------------------------------------------------------*
 * Track the arbitrary assertion of theorems, the use of mk_thm in           *
 * checking validity of tactics, and use term constructors directly on raw   *
 * terms.                                                                    *
 *---------------------------------------------------------------------------*)

local val dtag = Tag.read"dummy"
      val std_tagr = ref dtag
      val mk_thm_tagr = ref dtag
      val valid_tac_tagr = ref dtag
      val read_disk_tagr = ref (fn _:string => dtag)
      val mk_ax_tagr     = ref (fn _:string ref => dtag)
      val mk_eq_nocheckr = ref (fn _:Type.hol_type => fn _:term => fn _:term =>
                            raise THM_ERR"mk_eq_nocheck" "uninitialized")
      val Combr = ref (fn {Rator:term,Rand:term} =>
                            raise THM_ERR"Combr" "uninitialized")
      val Absr  = ref (fn {Bvar:term,Body:term} =>
                            raise THM_ERR"Absr" "uninitialized")
      val Bvr   = ref (fn _:int => raise THM_ERR"Bvr" "uninitialized")
      val _ = Tag.init std_tagr mk_thm_tagr valid_tac_tagr
                read_disk_tagr mk_ax_tagr
      val mk_thm_tag    = !mk_thm_tagr
      val valid_tac_tag = !valid_tac_tagr
      val _             = Term.Thm_init mk_eq_nocheckr Combr Absr Bvr
in
  val std_tag       = !std_tagr
  val read_disk_tag = !read_disk_tagr
  val mk_ax_tag     = !mk_ax_tagr
  val mk_eq_nocheck = !mk_eq_nocheckr
  val Comb          = !Combr
  val Abs           = !Absr
  val Bv            = !Bvr
  fun mk_thm p      = mk_oracle_thm mk_thm_tag p
  fun mk_tac_thm p  = mk_oracle_thm valid_tac_tag p
end;

(*---------------------------------------------------------------------------*
 * Information hiding. The first is for Theory, the second is for Const_def. *
 *---------------------------------------------------------------------------*)

local fun mk_axiom_thm (r,c) =
         (Assert (type_of c = bool) "mk_axiom_thm"  "Not a proposition!";
          make_thm Count.Axiom (mk_ax_tag r,[],c))
      fun mk_defn_thm tag c =
         (Assert (type_of c = bool) "mk_defn_thm"  "Not a proposition!";
          make_thm Count.Definition (tag,[],c))
      val used = ref false
in
 fun Theory_init r1 r2 =
      if !used then ()
       else (r1 := mk_axiom_thm; r2 := mk_defn_thm; used := true)
end;

local val used = ref false
in
  fun Const_def_init r1 =
      if !used then ()
       else (r1 := std_tag; used := true)
end;

fun refl_nocheck ty tm =
  make_thm Count.Refl (std_tag, [], mk_eq_nocheck ty tm tm);


(*---------------------------------------------------------------------------
 *                THE PRIMITIVE RULES OF INFERENCE
 *---------------------------------------------------------------------------*)

fun ASSUME tm =
   (Assert (type_of tm = bool) "ASSUME" "not a proposition";
    make_thm Count.Assume (std_tag,[tm],tm));


fun REFL tm = make_thm Count.Refl
                  (std_tag, [], mk_eq_nocheck (type_of tm) tm tm)

fun BETA_CONV tm = make_thm Count.Beta
                   (std_tag, [], mk_eq_nocheck (type_of tm) tm (beta_conv tm))
   handle HOL_ERR _ => THM_ERR "BETA_CONV" "not a beta-redex"


(*---------------------------------------------------------------------------
 * ltheta is a substitution mapping from the template to the concl of
 * the given theorem. It checks that the template is an OK abstraction of
 * the given theorem. rtheta maps the template to another theorem, in which
 * the lhs in the first theorem have been replaced by the rhs in the second
 * theorem. The replacements provide the lhs and rhs.
 *---------------------------------------------------------------------------*)

fun SUBST replacements template (th as THM(O,asl,c)) =
     let val (ltheta, rtheta, hyps, oracles) =
         itlist (fn {redex, residue = THM(ocls,h,c)} =>
                 fn (ltheta,rtheta,hyps,Ocls) =>
                      let val _ = Lib.assert Term.is_var redex
                          val {lhs,rhs} = dest_eq c
                      in ({redex=redex, residue=lhs}::ltheta,
                          {redex=redex, residue=rhs}::rtheta,
                          union_hyp h hyps,
                          Tag.merge ocls Ocls)
                      end)
                replacements ([],[],asl,O)
     in
       if (aconv (subst ltheta template) c)
       then make_thm Count.Subst (oracles,hyps,subst rtheta template)
       else th
     end;

(*---------------------------------------------------------------------------*
 *                                                                           *
 *        A |- t1 = t2                                                       *
 *   ------------------------  ABS x            [Where x is not free in A]   *
 *    A |- (\x.t1) = (\x.t2)                                                 *
 *---------------------------------------------------------------------------*)

fun ABS v (THM(ocl,asl,c)) =
 let val {lhs,rhs} = dest_eq c handle HOL_ERR _
        => THM_ERR "ABS" "not an equality"
 in
   Assert(Term.is_var v) "ABS"          "first argument is not a variable";
   Assert(not(mem v (free_varsl asl))) "ABS" "var. is free in assumptions";
   make_thm Count.Abs (ocl,asl,
        mk_eq_nocheck (Type.--> (type_of v, type_of lhs))
                      (mk_abs{Bvar=v, Body=lhs})
                      (mk_abs{Bvar=v, Body=rhs}))
 end;


fun INST_TYPE [] th = th
  | INST_TYPE theta (THM(ocl,asl,c)) =
 let val problem_tyvars =
      intersect (type_vars_in_term c)
                (rev_itlist (union o type_vars_in_term) asl [])
 in
   Assert (null_intersection problem_tyvars (map #redex theta)) "INST_TYPE"
          "type variable(s) in assumptions would be instantiated in concl";
   make_thm Count.InstType (ocl, asl, inst theta c)
 end;


fun DISCH w (THM(ocl,asl,c)) =
 make_thm Count.Disch
         (ocl, gather (not o aconv w) asl, mk_imp{ant=w, conseq=c});


fun MP (THM(o1,asl1,c1)) (THM(o2,asl2,c2)) =
   let val {ant,conseq} = dest_imp c1 handle HOL_ERR _
        => THM_ERR "MP" "not an implication"
   in
     Assert (aconv ant c2)
       "MP" "antecedent of first thm not aconv to concl of second";
     make_thm Count.Mp (Tag.merge o1 o2, union_hyp asl1 asl2, conseq)
   end;


(*---------------------------------------------------------------------------*
 * Derived Rules -- these are here for efficiency purposes, and so that all  *
 * invocations of mk_thm are in Thm.                                         *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*
 *  Symmetry of =
 *
 *       A |- t1 = t2
 *     ----------------
 *       A |- t2 = t1
 *
 * fun SYM th =
 *   let val (t1,t2) = dest_eq(concl th)
 *       val v = genvar(type_of t1)
 *   in
 *   SUBST [(th,v)] (mk_eq(v,t1)) (REFL t1)
 *   end
 *   handle _ =>  THM_ERR "SYM" "";
 *---------------------------------------------------------------------------*)
fun SYM th =
   let val {lhs,rhs} = dest_eq (concl th) handle HOL_ERR _
        => THM_ERR "SYM" "not an equality"
   in
     make_thm Count.Sym
        (tag th, hyp th, mk_eq_nocheck (type_of lhs) rhs lhs)
   end;

(*---------------------------------------------------------------------------
 * Transitivity of =
 *
 *   A1 |- t1 = t2  ,  A2 |- t2 = t3
 *  ---------------------------------
 *        A1 u A2 |- t1=t3
 *
 *fun TRANS th1 th2 =
 *   let val (t1,t2) = dest_eq(concl th1)
 *       and (t2',t3) = dest_eq(concl th2)
 *       val v = genvar(type_of t1)
 *   in
 *   SUBST [(th2,v)] (mk_eq(t1,v)) th1
 *   end
 *   handle _ =>  THM_ERR{function = "TRANS",message = ""};
 *
 *---------------------------------------------------------------------------*)
fun TRANS th1 th2 =
   let val {lhs=lhs1, rhs=rhs1} = dest_eq (concl th1)
       and {lhs=lhs2, rhs=rhs2} = dest_eq (concl th2)
       val _ = Assert (aconv rhs1 lhs2) "" ""
       val hyps = union_hyp (hyp th1) (hyp th2)
       val ocls = Tag.merge (tag th1) (tag th2)
   in
     make_thm Count.Trans
        (ocls, hyps, mk_eq_nocheck (type_of lhs1) lhs1 rhs2)
   end
   handle HOL_ERR _ => THM_ERR "TRANS" "";


(*---------------------------------------------------------------------------
 * Equivalence of alpha-convertible terms
 *
 *     t1, t2 alpha-convertable
 *     -------------------------
 *            |- t1 = t2
 *
 * fun ALPHA t1 t2 =
 *  (if (t1=t2) then REFL t1
 *   else
 *   case (t1,t2)
 *     of (Comb(t11,t12), Comb(t21,t22))
 *          => let val th1 = ALPHA t11 t21
 *                 and th2 = ALPHA t12 t22
 *             in TRANS (AP_THM th1 t12) (AP_TERM t21 th2) end
 *      | (Abs(x1,_), Abs(x2,t2'))
 *         => let val th1 = ALPHA_CONV x2 t1
 *                val (_,t1') = dest_abs(rhs(concl th1))
 *                val th2 = ALPHA t1' t2'
 *            in TRANS th1 (ABS x2 th2) end
 *      | (_,_)  => THM_ERR "ALPHA" ""
 *  ) handle _ => THM_ERR "ALPHA" "";
 *---------------------------------------------------------------------------*)
fun ALPHA t1 t2 =
   if (aconv t1 t2)
   then make_thm Count.Alpha (std_tag, [], mk_eq_nocheck (type_of t1) t1 t2)
   else THM_ERR "ALPHA" "";


(*---------------------------------------------------------------------------
 *     A1 |- f = g    A2 |- x = y
 *     ---------------------------
 *       A1 u A2 |- f x = g y
 *
 * fun MK_COMB (funth,argth) =
 *   let val f = lhs (concl funth)
 *       and x = lhs (concl argth)
 *   in
 *   SUBS_OCCS [([2], funth), ([2], argth)] (REFL (Comb(f,x))))
 *   ? failwith `MK_COMB`;
 *---------------------------------------------------------------------------*)

fun MK_COMB (funth,argth) =
   let val (eek,L) = strip_comb(concl funth)
       val {lhs=x, rhs=y} = dest_eq (concl argth)
   in
     case (dest_const eek, L)
      of ({Name="=",Ty}, [f,g])
          => make_thm Count.MkComb
                   (Tag.merge (tag funth) (tag argth),
                    union_hyp (hyp funth) (hyp argth),
                    mk_eq_nocheck (rng_ty (dom_ty Ty))
                                  (mk_comb{Rator=f, Rand=x})
                                  (mk_comb{Rator=g, Rand=y}))
       | _ => THM_ERR "" ""
   end
   handle HOL_ERR _ => THM_ERR"MK_COMB" "";


(*---------------------------------------------------------------------------
 * Application of a term to a theorem
 *
 *    A |- t1 = t2
 * ------------------
 *  A |- t t1 = t t2
 *
 *fun AP_TERM tm th =
 *   let val (t1,_) = dest_eq(concl th)
 *       val th1 = REFL (--`^tm ^t1`--)
 *       (* th1 = |- t t1 = t t1 *)
 *       and v  = genvar(type_of t1)
 *   in
 *   SUBST [(th,v)] (--`^tm ^t1 = ^tm ^v`--) th1
 *   end
 *   handle _ =>  THM_ERR{function = "AP_TERM",message = ""};
 *---------------------------------------------------------------------------*)
fun AP_TERM tm th =
   let val {lhs,rhs} = dest_eq(concl th)
   in
     make_thm Count.ApTerm
      (tag th, hyp th,
       mk_eq_nocheck (rng_ty (type_of tm))
                     (mk_comb{Rator=tm, Rand=lhs})
                     (mk_comb{Rator=tm, Rand=rhs}))
   end
   handle HOL_ERR _ => THM_ERR "AP_TERM" "";


(*---------------------------------------------------------------------------
 * Application of a theorem to a term
 *
 *    A |- t1 = t2
 *   ----------------
 *   A |- t1 t = t2 t
 *
 *fun AP_THM th tm =
 *   let val (t1,_) = dest_eq(concl th)
 *       val th1 = REFL (--`^t1 ^tm`--)
 *       (* th1 = |- t1 t = t1 t *)
 *       and v   = genvar(type_of t1)
 *   in
 *   SUBST [(th,v)] (--`^t1 ^tm = ^v ^tm`--) th1
 *   end
 *   handle _ =>  THM_ERR{function = "AP_THM",message = ""};
 *---------------------------------------------------------------------------*)
fun AP_THM th tm =
   let val {lhs,rhs} = dest_eq(concl th)
   in
     make_thm Count.ApThm
       (tag th, hyp th,
        mk_eq_nocheck (rng_ty (type_of lhs))
                      (mk_comb{Rator=lhs, Rand=tm})
                      (mk_comb{Rator=rhs, Rand=tm}))
   end
   handle HOL_ERR _ => THM_ERR "AP_THM" "";

(*---------------------------------------------------------------------------
 *  Modus Ponens for =
 *
 *
 *   A1 |- t1 = t2  ,  A2 |- t1
 *  ----------------------------
 *        A1 u A2 |- t2
 *
 *fun EQ_MP th1 th2 =
 *   let val (t1,t2) = dest_eq(concl th1)
 *       val v = genvar(type_of t1)
 *   in
 *   SUBST [(th1,v)] v th2
 *   end
 *   handle _ =>  THM_ERR{function = "EQ_MP",message = ""};
 *---------------------------------------------------------------------------*)
fun EQ_MP th1 th2 =
   let val {lhs,rhs} = dest_eq(concl th1)
       val _ = Assert (aconv lhs (concl th2)) "" ""
   in
    make_thm Count.EqMp (Tag.merge (tag th1) (tag th2),
                         union_hyp (hyp th1) (hyp th2), rhs)
   end
   handle HOL_ERR _ => THM_ERR "EQ_MP" "";


(*---------------------------------------------------------------------------
 *              A |- t1 = t2
 *    ------------------------------------
 *     A |- t1 ==> t2      A |- t2 ==> t1
 *
 *fun EQ_IMP_RULE th =
 *   let val (t1,t2) = dest_eq(concl th)
 *   in
 *   (DISCH t1 (EQ_MP th (ASSUME t1)), DISCH t2 (EQ_MP(SYM th)(ASSUME t2)))
 *   end
 *   handle _ =>  THM_ERR{function = "EQ_IMP_RULE",message = ""};
 *---------------------------------------------------------------------------*)
fun EQ_IMP_RULE th =
   let val {lhs,rhs} = dest_eq(concl th)
   and A = hyp th
   and O = tag th
   in
     (make_thm Count.EqImpRule(O,A, mk_imp{ant=lhs, conseq=rhs}),
      make_thm Count.EqImpRule(O,A, mk_imp{ant=rhs, conseq=lhs}))
   end
   handle HOL_ERR _ => THM_ERR"EQ_IMP_RULE" "";

(*---------------------------------------------------------------------------
 * Specialization
 *
 *    A |- !(\x.u)
 *  --------------------   (where t is free for x in u)
 *    A |- u[t/x]
 *
 *fun SPEC t th =
 *   let val {Rator=F,Rand=body} = dest_comb(concl th)
 *   in
 *   if (not(#Name(dest_const F)="!"))
 *   then THM_ERR{function = "SPEC",message = ""}
 *   else let val {Bvar=x,Body=u} = dest_abs body
 *        and v1 = genvar(type_of F)
 *        and v2 = genvar(type_of body)
 *        val th1 = SUBST[{var = v1,
 *                         thm = INST_TYPE[{redex   = (==`:'a`==),
 *                                          residue = type_of x}] FORALL_DEF}]
 *                       (--`^v1 ^body`--) th
 *        (* th1 = |- (\P. P = (\x. T))(\x. t1 x) *)
 *        val th2 = BETA_CONV(concl th1)
 *        (* th2 = |- (\P. P = (\x. T))(\x. t1 x) = ((\x. t1 x) = (\x. T)) *)
 *        val th3 = EQ_MP th2 th1
 *        (* th3 = |- (\x. t1 x) = (\x. T) *)
 *        val th4 = SUBST [{var= v2, thm=th3}] (--`^body ^t = ^v2 ^t`--)
 *                        (REFL (--`^body ^t`--))
 *        (* th4 = |- (\x. t1 x)t = (\x. T)t *)
 *        val {lhs=ls,rhs=rs} = dest_eq(concl th4)
 *        val th5 = TRANS(TRANS(SYM(BETA_CONV ls))th4)(BETA_CONV rs)
 *        (* th5 = |- t1 t = T *)
 *        in
 *        EQT_ELIM th5
 *        end
 *   end
 *   handle _ => THM_ERR{function = "SPEC",message = ""};
 *
 *
 *pre-dB manner:
 *fun SPEC t th =
 *   let val {Bvar,Body} = dest_forall(concl th)
 *   in
 *   make_thm Count.(hyp th, subst[{redex = Bvar, residue = t}] Body)
 *   end
 *   handle _ => THM_ERR{function = "SPEC",message = ""};
 *---------------------------------------------------------------------------*)
fun SPEC t th =
   let val {Rator,Rand} = dest_comb(concl th)
       val _ = Assert ("!" = #Name(dest_const Rator)) "" ""
   in
     make_thm Count.Spec (tag th, hyp th,
                 beta_conv(mk_comb{Rator=Rand, Rand=t}))
   end
   handle HOL_ERR _ => THM_ERR"SPEC" "";



(*---------------------------------------------------------------------------
 * Generalization
 *
 *         A |- t
 *   -------------------   (where x not free in A)
 *       A |- !(\x.t)
 *
 *fun GEN x th =
 *   let val th1 = ABS x (EQT_INTRO th)
 *     (* th1 = |- (\x. t1 x) = (\x. T)  --ABS does not behave this way --KLS*)
 *      val abs = `\^x. ^(concl th)`
 *      and v1 = genvar `:(^(type_of x) -> bool) -> bool`
 *      and v2 = genvar `:bool`
 *      val th2 = SUBST [(INST_TYPE[(type_of x, `:'a`)]FORALL_DEF,v1)]
 *                      `($! ^abs) = (^v1 ^abs)`
 *                      (REFL `$! ^abs`)
 *      (* th2 = |- (!x. t1 x) = (\P. P = (\x. T))(\x. t1 x) *)
 *      val th3 = TRANS th2 (BETA_CONV(snd(dest_eq(concl th2))))
 *      (* th3 = |- (!x. t1 x) = ((\x. t1 x) = (\x. T)) *)
 *      in
 *      SUBST [(SYM th3, v2)] v2 th1
 *      end
 *      handle _ => THM_ERR{function = "GEN",message = ""};
 *---------------------------------------------------------------------------*)
fun GEN x th =
   (Assert (not(List.exists (free_in x) (hyp th))) "GEN" "";
    make_thm Count.Gen(tag th, hyp th, mk_forall{Bvar=x, Body=concl th})
     handle HOL_ERR _ => THM_ERR "GEN" "not a forall");

(*---------------------------------------------------------------------------
 * Simple version of alpha-conversion (needed for deriving ETA_CONV)
 *
 *       "\x1. t x1"   "\x2. t x2"   --->   |- "(\x1.t x1)=(\x2.t x2)"
 *
 * fun SIMPLE_ALPHA(t1,t2) =
 *   let val (x1,body1) = dest_abs t1
 *       and (x2,body2) = dest_abs t2
 *       val th1 = BETA_CONV `^t1 (x:^(type_of x1))`
 *       (* th1 = |- (\x1. t x1)x = t x *)
 *       and th2 = BETA_CONV `^t2 (x:^(type_of x2))`
 *       (* th2 = |- (\x2. t x2)x = t x *)
 *       and th3 = SPEC t1 (INST_TYPE [(type_of x1, `:'a`),
 *                                     (type_of body1, `:'b`)] ETA_AX)
 *       (* th3 = |- (\x. (\x1. t x1)x) = (\x1. t x1) *)
 *       and th4 = SPEC t2 (INST_TYPE [(type_of x2, `:'a`),
 *                                     (type_of body2, `:'b`)] ETA_AX)
 *       (* th4 = |- (\x. (\x2. t x2)x) = (\x2. t x2) *)
 *   in
 *   TRANS (TRANS (SYM th3)
 *                (ABS `x:^(type_of x1)` (TRANS th1 (SYM th2))))
 *         th4
 *   end
 *   handle _ => THM_ERR{function = "SIMPLE_ALPHA",message = ""};
 *
 *
 * Eta-conversion
 *
 * 	"(\x.t x)"   --->    |- (\x.t x) = t  (if x not free in t)
 *
 * fun ETA_CONV (tm as Abs(Var(vty,_), cmb as Comb(t,_))) =
 *      (let val body_ty = type_of cmb
 *           val th = SPEC t (INST_TYPE [(vty,`:'a`), (body_ty, `:'b`)] ETA_AX)
 *           (* th = |- (\x. t x) = t *)
 *       in
 *       TRANS (SIMPLE_ALPHA(tm,lhs(concl th))) th
 *       end
 *       handle _ => THM_ERR{function = "ETA_CONV",message = ""})
 *  | ETA_CONV _ = THM_ERR{function = "ETA_CONV",message = ""};
 *
 *---------------------------------------------------------------------------*)
fun ETA_CONV tm =
   make_thm Count.EtaConv
      (std_tag, [], mk_eq_nocheck (type_of tm) tm (eta_conv tm))
   handle HOL_ERR _ => THM_ERR"ETA_CONV" "";


(*---------------------------------------------------------------------------
 * Existential introduction
 *
 *    A |- t[t']
 *  --------------
 *   A |- ?x.t[x]
 *
 *  The parameters are: EXISTS("?x.t[x]", "t'") (|- t[t'])
 *
 *fun EXISTS (fm,tm) th =
 *   let val (x,t) = dest_exists fm
 *       val th1 = BETA_CONV `(\(^x). ^t) ^tm`
 *       (* th1 = |- (\x. t x)t' = t t' *)
 *       val th2 = EQ_MP (SYM th1) th
 *       (* th2 = |- (\x. t x)t' *)
 *       val th3 = SELECT_INTRO th2
 *       (* th3 = |- (\x. t x)(@x. t x) *)
 *       val th4 = AP_THM(INST_TYPE[(type_of x, `:'a`)]EXISTS_DEF) `\(^x).^t`
 *       (* th4 = |- (?x. t x) = (\P. P($@ P))(\x. t x) *)
 *       val th5 = TRANS th4 (BETA_CONV(snd(dest_eq(concl th4))))
 *       (* th5 = |- (?x. t x) = (\x. t x)(@x. t x) *)
 *   in
 *   EQ_MP (SYM th5) th3
 *   end
 *   handle _ => THM_ERR{function = "EXISTS",message = ""};
 *
 * Goes better with beta_conv
 * fun EXISTS (w,t) th =
 *    let val {Bvar,Body} = dest_exists w
 *    in
 *    if (aconv (subst [{redex = Bvar, residue = t}] Body)
 *              (concl th))
 *    then make_thm Count.(hyp th, w)
 *    else THM_ERR{function = "EXISTS",message = ""}
 *    end
 *    handle _ => THM_ERR{function = "EXISTS",message = ""};
 *---------------------------------------------------------------------------*)

fun EXISTS (w,t) th =
 let val {Rator,Rand} = dest_comb w handle _ => THM_ERR "EXISTS" ""
     val _ = Assert ("?" = #Name(dest_const Rator))
                "EXISTS" "not an existential"
     val _ = Assert (aconv (beta_conv(mk_comb{Rator=Rand, Rand=t}))
                               (concl th)) "EXISTS" "incompatible structure"
   in
     make_thm Count.Exists (tag th, hyp th, w)
   end;



(*---------------------------------------------------------------------------
 * Existential elimination
 *
 *   A1 |- ?x.t[x]   ,   A2, "t[v]" |- t'
 *   ------------------------------------     (variable v occurs nowhere)
 *            A1 u A2 |- t'
 *
 *fun CHOOSE (v,th1) th2 =
 *   let val (x,body) = dest_exists(concl th1)
 *       and t'     = concl th2
 *       and v1     = genvar `:bool`
 *       val th3 = AP_THM(INST_TYPE[(type_of v, `:'a`)]EXISTS_DEF)`\(^x).^body`
 *       (* th3 = |- (?x. t x) = (\P. P($@ P))(\x. t x) *)
 *       val th4 = EQ_MP th3 th1
 *       (* th4 = |- (\P. P($@ P))(\x. t x) *)
 *       val th5 = EQ_MP (BETA_CONV(concl th4)) th4
 *       (* th5 = |- (\x. t x)(@x. t x) *)
 *       val th6 = BETA_CONV `(\(^x).^body)^v`
 *       (* th6 = |- (\x. t x)v = t v *)
 *       val Pa = snd(dest_eq(concl th6))
 *       val th7 = UNDISCH(SUBST [(SYM th6,v1)] `^v1 ==> ^t'` (DISCH Pa th2))
 *       (* th7 = |- t' *)
 *   in
 *   SELECT_ELIM th5 (v,th7)
 *   end
 *   handle _ => THM_ERR{function = "CHOOSE",message = ""};
 *---------------------------------------------------------------------------*)

fun CHOOSE (v,xth) bth =
   let val {Bvar,Body} = dest_exists (concl xth)
       val bhyp = Dsyntax.disch(subst [Bvar |-> v] Body, hyp bth)
       val _ = Assert (is_var v andalso
                           Lib.all (not o free_in v)
                             ((concl xth::hyp xth)@(concl bth::bhyp))) "" ""
   in make_thm Count.Choose (Tag.merge (tag xth) (tag bth),
                   union_hyp (hyp xth) bhyp,  concl bth)
   end
   handle HOL_ERR _ => THM_ERR "CHOOSE" "";


(*---------------------------------------------------------------------------
 * Conjunction introduction rule
 *
 *   A1 |- t1  ,  A2 |- t2
 *  -----------------------
 *    A1 u A2 |- t1 /\ t2
 *
 *fun CONJ th1 th2 = MP (MP (SPEC (concl th2) (SPEC (concl th1) AND_INTRO_THM))
 *                          th1)
 *                      th2;
 *---------------------------------------------------------------------------*)
fun CONJ th1 th2 =
   make_thm Count.Conj(Tag.merge (tag th1) (tag th2),
                union_hyp (hyp th1) (hyp th2),
                mk_conj{conj1=concl th1, conj2=concl th2})
   handle HOL_ERR _ => THM_ERR "CONJ" "";


(*---------------------------------------------------------------------------
 * Left conjunct extraction
 *
 *   A |- t1 /\ t2
 *   -------------
 *      A |- t1
 *
 *fun CONJUNCT1 th =
 *   let val (t1,t2) = dest_conj(concl th)
 *   in
 *   MP (SPEC t2 (SPEC t1 AND1_THM)) th
 *   end
 *   handle _ => THM_ERR{function = "CONJUNCT1",message = ""};
 *
 *---------------------------------------------------------------------------*)
fun CONJUNCT1 th =
   make_thm Count.Conjunct1 (tag th, hyp th, #conj1(dest_conj(concl th)))
     handle HOL_ERR _ => THM_ERR "CONJUNCT1" "";


(*---------------------------------------------------------------------------
 *  Right conjunct extraction
 *
 *   A |- t1 /\ t2
 *   -------------
 *      A |- t2
 *
 *fun CONJUNCT2 th =
 *   let val (t1,t2) = dest_conj(concl th)
 *   in
 *   MP (SPEC t2 (SPEC t1 AND2_THM)) th
 *   end
 *   handle _ => THM_ERR{function = "CONJUNCT2",message = ""};
 *---------------------------------------------------------------------------*)
fun CONJUNCT2 th =
  make_thm Count.Conjunct2 (tag th, hyp th, #conj2(dest_conj(concl th)))
    handle HOL_ERR _ => THM_ERR "CONJUNCT2" "";


(*---------------------------------------------------------------------------
 * Left disjunction introduction
 *
 *      A |- t1
 *  ---------------
 *   A |- t1 \/ t2
 *
 *fun DISJ1 th t2 = MP (SPEC t2 (SPEC (concl th) OR_INTRO_THM1)) th
 *           handle _ => THM_ERR{function = "DISJ1",message = ""};
 *---------------------------------------------------------------------------*)
fun DISJ1 th w =
  make_thm Count.Disj1 (tag th, hyp th, mk_disj{disj1=concl th, disj2=w})
   handle HOL_ERR _ => THM_ERR "DISJ1" "";


(*---------------------------------------------------------------------------
 * Right disjunction introduction
 *
 *      A |- t2
 *  ---------------
 *   A |- t1 \/ t2
 *
 *fun DISJ2 t1 th = MP (SPEC (concl th) (SPEC t1 OR_INTRO_THM2)) th
 *          handle _ => THM_ERR{function = "DISJ2",message = ""};
 *---------------------------------------------------------------------------*)
fun DISJ2 w th =
  make_thm Count.Disj2 (tag th, hyp th, mk_disj{disj1=w, disj2=concl th})
    handle HOL_ERR _ => THM_ERR "DISJ2" "";


(*---------------------------------------------------------------------------
 * Disjunction elimination
 *
 *   A |- t1 \/ t2   ,   A1,t1 |- t   ,   A2,t2 |- t
 *   -----------------------------------------------
 *               A u A1 u A2 |- t
 *
 *fun DISJ_CASES th1 th2 th3 =
 *   let val (t1,t2) = dest_disj(concl th1)
 *       and t = concl th2
 *       val th4 = SPEC t2 (SPEC t1 (SPEC t OR_ELIM_THM))
 *   in
 *   MP (MP (MP th4 th1) (DISCH t1 th2)) (DISCH t2 th3)
 *   end
 *   handle _ => THM_ERR{function = "DISJ_CASES",message = ""};
 *---------------------------------------------------------------------------*)
fun DISJ_CASES dth ath bth =
  let val _ = Assert (is_disj(concl dth) andalso
                      aconv (concl ath) (concl bth)) "" ""
      val {disj1,disj2} = dest_disj (concl dth)
      fun mergel L = itlist Tag.merge L std_tag
  in
   make_thm Count.DisjCases
                (mergel [tag dth, tag ath, tag bth],
                 union_hyp (hyp dth) (union_hyp (disch(disj1, hyp ath))
                                                (disch(disj2, hyp bth))),
                 concl ath)
  end
  handle HOL_ERR _ => THM_ERR "DISJ_CASES" "";


(*---------------------------------------------------------------------------
 * NOT introduction
 *
 *     A |- t ==> F
 *     ------------
 *       A |- ~t
 *
 *fun NOT_INTRO th =
 *   let val (t,_) = dest_imp(concl th)
 *   in
 *   MP (SPEC t IMP_F) th
 *   end
 *   handle _ => THM_ERR{function = "NOT_INTRO",message = ""};
 *---------------------------------------------------------------------------*)

fun NOT_INTRO th =
   let val {ant,conseq} = dest_imp(concl th)
       val _ = Assert (conseq=mk_const{Name="F",Ty=bool}) "" ""
   in
      make_thm Count.NotIntro (tag th, hyp th, mk_neg ant)
   end
   handle HOL_ERR _ => THM_ERR "NOT_INTRO" "";



(*---------------------------------------------------------------------------
 * Negation elimination
 *
 *       A |- ~ t
 *     --------------
 *      A |- t ==> F
 *
 *fun NOT_ELIM th =
 *   let val (_,t) = dest_comb(concl th)
 *   in
 *   MP (SPEC t F_IMP) th
 *   end
 *   handle _ => THM_ERR{function = "NOT_ELIM",message = ""};
 *---------------------------------------------------------------------------*)
fun NOT_ELIM th =
  let val {Rator,Rand} = dest_comb(concl th)
      val _ = Assert (#Name(dest_const Rator) = "~") "" ""
  in
   make_thm Count.NotElim(tag th, hyp th,
             mk_imp{ant=Rand, conseq=mk_const{Name="F", Ty=bool}})
  end
   handle HOL_ERR _ => THM_ERR "NOT_ELIM" "";



(*---------------------------------------------------------------------------
 * Classical contradiction rule
 *
 *   A,"~t" |- F
 *   --------------
 *       A |- t
 *
 *fun CCONTR t th =
 *   let val th1 = RIGHT_BETA(AP_THM NOT_DEF t)
 *       and v   = genvar (--`:bool`--)
 *       val th2 = EQT_ELIM (ASSUME (--`^t = T`--))
 *       val th3 = SUBST [(th1,v)] (--`^v ==> F`--) (DISCH (--`~ ^t`--) th)
 *       val th4 = SUBST[(ASSUME(--`^t = F`--),v)] (--`(^v ==> F) ==> F`--) th3
 *       val th5 = MP th4 (EQT_ELIM (CONJUNCT2 IMP_CLAUSE4))
 *       val th6 = EQ_MP (SYM(ASSUME (--`^t = F`--))) th5
 *   in
 *   DISJ_CASES (SPEC t BOOL_CASES_AX) th2 th6
 *   end
 *   handle _ => THM_ERR{function = "CCONTR",message = ""};
 *---------------------------------------------------------------------------*)

fun CCONTR w fth =
  (Assert (concl fth = mk_const{Name="F",Ty=bool}) "CCONTR" "";
   make_thm Count.Ccontr(tag fth, disch(mk_neg w, hyp fth), w)
     handle HOL_ERR _ => THM_ERR "CCONTR" "");



(*---------------------------------------------------------------------------
 * Instantiate free variables in a theorem
 *---------------------------------------------------------------------------*)

fun INST [] th = th
  | INST inst_list th =
     let val asl = hyp th
         and vars = map (Lib.assert is_var o #redex) inst_list
                    handle _ => THM_ERR"INST" "non-variable in domain of subst"
         val () = if (null asl) then ()
                 else Assert (not (Lib.exists
                              (fn v => Lib.exists (free_in v) asl) vars))
              "INST" "attempt to substitute for a variable that is free in hyp"
     in
      make_thm Count.Inst (tag th, asl, subst inst_list (concl th))
       handle HOL_ERR _ => THM_ERR "INST" ""
     end


(*---------------------------------------------------------------------------
 * Derived rules optimized for computations, avoiding most of useless
 * type-checking, using pointer equality and delayed substitutions
 * (see computeLib).
 *---------------------------------------------------------------------------*)

(*    A |- t = (\x.m) n
 *  ---------------------
 *     A |- t = m{x\n}
 *)
fun Beta th =
   let val {lhs, rhs, ty} = dest_eq_ty (concl th)
   in make_thm Count.Beta (std_tag, hyp th,
			   mk_eq_nocheck ty lhs (lazy_beta_conv rhs))
   end
   handle HOL_ERR _ => THM_ERR "Beta" "";

(*    A |- t = (\x.f x)
 *  --------------------- x not free in f
 *     A |- t = f
 *)
fun Eta th =
   let val {lhs, rhs, ty} = dest_eq_ty (concl th)
   in make_thm Count.EtaConv (std_tag, hyp th,
		              mk_eq_nocheck ty lhs (eta_conv rhs))
   end
   handle HOL_ERR _ => THM_ERR "Eta" "";


(* This rule behaves like a tactic: given a goal (reducing the rhs of thm),
 * it returns two subgoals (reducing the rhs of th1 and th2), together
 * with a validation (mkthm), that builds the normal form of t from the
 * normal forms of u and v.
 * NB: we do not have to typecheck the rator u, and we replaced the alpha
 * conversion test with pointer equality.
 *
 *                     |- u = u    (th1)        |- v = v    (th2)
 *       (thm)             ...                     ...
 *    A |- t = u v    A' |- u = u' (th1')     A'' |- v = v' (th2')
 *  ----------------------------------------------------------------
 *                A u A' u A'' |- t = u' v'
 *
 * Could be implemented outside Thm as:
 *   fun Mk_comb th =
 *     let val {Rator,Rand} = dest_comb(rhs (concl th))
 *         fun mka th1 th2 = TRANS th (MK_COMB(th1,th2)) in
 *     (REFL Rator, REFL Rand, mka)
 *     end
 *)
fun Mk_comb thm =
   let val {lhs, rhs, ty} = dest_eq_ty (concl thm)
       val {Rator,Rand} = dest_comb rhs
       fun mkthm th1' th2' =
         let val {lhs=lhs1, rhs=rhs1} = dest_eq (concl th1')
             val _ = Assert (EQ(lhs1,Rator)) "" ""
             val {lhs=lhs2, rhs=rhs2} = dest_eq (concl th2')
             val _ = Assert (EQ(lhs2,Rand)) "" ""
             val (ocls,hyps) = tag_hyp_union [thm, th1', th2']
         in make_thm Count.MkComb
	   (ocls, hyps,mk_eq_nocheck ty lhs (mk_comb{Rator=rhs1,Rand=rhs2}))
         end
	 handle HOL_ERR _ => THM_ERR "Mk_comb" "";
       val aty = type_of Rand    (* typing! *)
       val th1 = refl_nocheck (Type.--> (aty,ty)) Rator
       val th2 = refl_nocheck aty Rand
   in (th1,th2,mkthm)
   end
   handle HOL_ERR _ => THM_ERR "Mk_comb" "";

(*                      |- u = u    (th1)
 *       (thm)              ...
 *    A |- t = \x.u    A' |- u = u' (th1')
 *  ---------------------------------------- x not in FV(A')
 *            A u A' |- t = \x.u'
 *
 *   fun Mk_abs th =
 *     let val {Bvar,Body} = dest_abs(rhs (concl th)) in
 *     (Bvar, REFL Body, (fn th1 => TRANS th (ABS Bvar th1)))
 *     end
 *)
fun Mk_abs thm =
   let val {lhs, rhs, ty} = dest_eq_ty (concl thm)
       val {Bvar,Body} = dest_abs rhs
       fun mkthm th1' =
         let val {lhs=lhs1, rhs=rhs1} = dest_eq (concl th1')
             val _ = Assert (EQ(lhs1,Body)) "" ""
             val _ = Assert (not(mem Bvar (free_varsl (hyp th1')))) "" ""
             val (ocls,hyps) = tag_hyp_union [thm, th1']
         in make_thm Count.Abs
	   (ocls, hyps, mk_eq_nocheck ty lhs (mk_abs{Bvar=Bvar, Body=rhs1}))
         end
	 handle HOL_ERR _ => THM_ERR "Mk_abs" ""
       val th1 = refl_nocheck (rng_ty ty) Body
   in (Bvar,th1,mkthm)
   end
   handle HOL_ERR _ => THM_ERR "Mk_abs" "";

(* Same as SPEC, but without propagating the substitution. *)
fun Spec t th =
   let val {Rator,Rand} = dest_comb(concl th)
       val _ = Assert ("!" = #Name(dest_const Rator)) "" ""
   in
     make_thm Count.Spec (tag th, hyp th,
                 lazy_beta_conv(mk_comb{Rator=Rand, Rand=t}))
   end
   handle HOL_ERR _ => THM_ERR"Spec" "";



(*---------------------------------------------------------------------------*
 * Getting theorems from disk. This is the simple parser for the "raw" hol   *
 * terms that are found in exported theory files.                            *
 *---------------------------------------------------------------------------*)

datatype lexeme = dot | lamb | lparen | rparen
                | ident of int
                | bvar  of int;

local val numeric = Char.contains "0123456789";
in
fun take_numb ss0 =
  let val (ns, ss1) = Substring.splitl numeric ss0
  in
     case Int.fromString (Substring.string ns)
      of SOME i => (i,ss1)
       | NONE   => raise THM_ERR "take_numb" ""
  end
end;

fun lexer ss0 =
 let val ss1 = Substring.dropl Char.isSpace ss0
 in
  case Substring.getc ss1
   of NONE         => NONE
    | SOME (c,ss2) =>
       case c
         of #"."  => SOME(dot,   ss2)
          | #"\\" => SOME(lamb,  ss2)
          | #"("  => SOME(lparen,ss2)
          | #")"  => SOME(rparen,ss2)
          | #"%"  => let val (n,ss3) = take_numb ss2 in SOME(ident n, ss3) end
          | #"$"  => let val (n,ss3) = take_numb ss2 in SOME(bvar n,  ss3) end
          |   _   => raise THM_ERR "raw lexer" "bad character"
  end;

fun eat_rparen ss =
  case lexer ss
   of SOME (rparen, ss') => ss'
    |   _ => raise THM_ERR "eat_rparen" "expected right parenthesis";

fun eat_dot ss =
  case lexer ss
   of SOME (dot, ss') => ss'
    |   _ => raise THM_ERR "eat_dot" "expected a \".\"";

fun parse_raw table =
 let fun index i = Vector.sub(table,i)
     fun parse (stk,ss) =
      case lexer ss
       of SOME (bvar n,  rst) => (Bv n::stk,rst)
        | SOME (ident n, rst) => (index n::stk,rst)
        | SOME (lparen,  rst) =>
           (case lexer rst
             of SOME (lamb, rst') => parse (glamb (stk,rst'))
              |    _              => parse (parsel (parse (stk,rst))))
        |  _ => (stk,ss)
     and
     parsel (stk,ss) =
        case parse (stk,ss)
         of (h1::h2::t, ss') => (Comb{Rator=h2,Rand=h1}::t, eat_rparen ss')
          |   _              => raise THM_ERR "raw.parsel" "impossible"
     and
     glamb(stk,ss) =
      case lexer ss
       of SOME (ident n, rst) =>
            (case parse (stk, eat_dot rst)
              of (h::t,rst1) => (Abs{Bvar=index n,Body=h}::t, eat_rparen rst1)
               |   _         => raise THM_ERR "glamb" "impossible")
        | _ => raise THM_ERR "glamb" "expected an identifier"
 in
  fn [QUOTE s] =>
     (case parse ([], Substring.all s)
       of ([v], _) => v
        | _ => raise THM_ERR "raw term parser" "parse failed")
   | _ => raise THM_ERR "raw term parser" "expected a quotation"
 end;

val mk_disk_thm  = make_thm Count.Disk;

fun disk_thm vect =
  let val rtp = parse_raw vect
  in
    fn (s,asl,w) => mk_disk_thm(read_disk_tag s, map rtp asl, rtp w)
  end;


end; (* THM *)
