(* ===================================================================== *)
(* FILE          : Thm.sml                                               *)
(* DESCRIPTION   : The abstract data type of theorems.                   *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon, University of Cambridge              *)
(*                     Konrad Slind, University of Calgary               *)
(*                                   University of Cambridge             *)
(*                     Bruno Barras, University of Cambridge and INRIA   *)
(* DATE          : September 10, 1991, Konrad Slind                      *)
(* Modified      : September 23, 1997, Ken Larsen                        *)
(*               : 1999, Bruno Barras                                    *)
(*               : July 2000, Konrad Slind                               *)
(* ===================================================================== *)

structure Thm : RawThm =
struct

open Feedback Lib Term KernelTypes Tag

type 'a set = 'a HOLset.set;

val --> = Type.-->;
infixr 3 -->;
infix 5 |-> ;

(*---------------------------------------------------------------------------
       Exception handling
 ---------------------------------------------------------------------------*)

val thm_err = mk_HOL_ERR "Thm"
fun ERR f m = raise thm_err f m
fun Assert b s1 s2 = if b then () else ERR s1 s2


(*---------------------------------------------------------------------------*
 * Miscellaneous syntax routines.                                            *
 *---------------------------------------------------------------------------*)

val bool      = Type.bool
val alpha     = Type.alpha
fun dom ty    = fst (Type.dom_rng ty)
fun rng ty    = snd (Type.dom_rng ty);
val EQ        = Portable.pointer_eq
val empty_tag = Tag.empty_tag


(*---------------------------------------------------------------------------
    The following are here because I didn't want to Thm to be dependent
    on some derived syntax (now in boolSyntax).
 ---------------------------------------------------------------------------*)

val F = Susp.delay (fn () => mk_thy_const{Name="F", Thy="bool", Ty=bool});

val mk_neg = Susp.delay (fn () =>
  let val notc = mk_thy_const{Name="~",Thy="bool",Ty=bool --> bool}
  in fn M => mk_comb(notc,M)
  end);

val mk_forall = Susp.delay (fn () =>
 let val forallc = prim_mk_const{Name="!", Thy="bool"}
 in fn v => fn tm =>
      mk_comb(inst[alpha |-> type_of v] forallc, mk_abs(v,tm))
 end);

val mk_tyforall = Susp.delay (fn () =>
 let val tyforallc = prim_mk_const{Name="!:", Thy="bool"}
 in fn a => fn tm =>
      mk_comb(inst_kind[Kind.kappa |-> Type.kind_of a] tyforallc, mk_tyabs(a,tm))
 end);

val mk_conj = Susp.delay (fn () =>
 let val conjc = prim_mk_const{Name="/\\", Thy="bool"}
 in fn (M,N) => list_mk_comb(conjc,[M,N])
 end);

val mk_disj = Susp.delay (fn () =>
 let val disjc = prim_mk_const{Name="\\/", Thy="bool"}
 in fn (M,N) => list_mk_comb(disjc,[M,N])
 end);


local val DEST_IMP_ERR = thm_err "dest_imp" ""
in
fun dest_imp M =
 let val (Rator,conseq) = with_exn dest_comb M DEST_IMP_ERR
 in if is_comb Rator
    then let val (Rator,ant) = dest_comb Rator
         in if eq Rator Term.imp then (ant,conseq) else raise DEST_IMP_ERR
         end
    else case with_exn dest_thy_const Rator DEST_IMP_ERR
          of {Name="~", Thy="bool",...} => (conseq,Susp.force F)
           | otherwise => raise DEST_IMP_ERR
 end
end;

local val err = thm_err "dest_exists" ""
in
fun dest_exists tm =
 let val (Rator,Rand) = with_exn dest_comb tm err
 in case with_exn dest_thy_const Rator err
     of {Name="?", Thy="bool",...} => with_exn dest_abs Rand err
      | otherwise => raise err
 end
end;

local val err = thm_err "dest_tyexists" ""
in
fun dest_tyexists tm =
 let val (Rator,Rand) = with_exn dest_comb tm err
 in case with_exn dest_thy_const Rator err
     of {Name="?:", Thy="bool",...} => with_exn dest_tyabs Rand err
      | otherwise => raise err
 end
end;


(*---------------------------------------------------------------------------*
 * The type of theorems and some basic operations on it.                     *
 *---------------------------------------------------------------------------*)

(* datatype thm = datatype KernelTypes.thm *)

fun single_hyp tm = HOLset.singleton Term.compare tm
val empty_hyp = Term.empty_tmset
fun list_hyp tml = HOLset.addList(empty_hyp,tml)

fun tag  (THM(tg,_,_))  = tg
fun concl(THM(_,_,c))   = c
fun hypset  (THM(_,asl,_)) = asl
fun hyplist (THM(_,asl,_)) = HOLset.listItems asl
val hyp = hyplist   (* backwards compatibility *)

fun dest_thm(t as THM(_,asl,w)) = (hyplist t,w) (* Compatible with old code. *)
fun sdest_thm(THM(_,asl,w)) = (asl,w)
fun make_thm R seq = (Count.inc_count R; THM seq);   (* internal only *)

fun thm_frees (t as THM(_,asl,c)) = free_varsl (c::hyplist t);

fun add_hyp h asl = HOLset.add(asl,h)
fun union_hyp asl1 asl2 = HOLset.union(asl1, asl2)

fun tag_hyp_union thm_list =
  (itlist (Tag.merge o tag) (tl thm_list) (tag (hd thm_list)),
   itlist (union_hyp o hypset) thm_list empty_hyp);

fun var_occursl v l = isSome (HOLset.find (var_occurs v) l);
fun type_var_occursl a l = isSome (HOLset.find (type_var_occurs a) l);

fun hypset_all P s = not (isSome (HOLset.find (not o P) s))
fun hypset_exists P s = isSome (HOLset.find P s)
fun hypset_map f s = HOLset.foldl(fn(i,s0) => HOLset.add(s0,f i)) empty_hyp s

fun hyp_kdvars th =
   HOLset.foldl (fn (h,kds) =>
                        List.foldl (fn (kdv,kds) => HOLset.add(kds,kdv))
                                   kds
                                   (Term.kind_vars_in_term h))
                    (HOLset.empty Kind.kind_compare)
                    (hypset th)

fun hyp_tyvars th =
   HOLset.foldl (fn (h,tys) =>
                        List.foldl (fn (tyv,tys) => HOLset.add(tys,tyv))
                                   tys
                                   (Term.type_vars_in_term h))
                    (HOLset.empty Type.compare)
                    (hypset th)

fun hyp_frees th =
  HOLset.foldl (fn (h,tms) => Term.FVL[h] tms) empty_tmset (hypset th);

fun is_bool tm = (Type.eq_ty (type_of tm) bool);


(*---------------------------------------------------------------------------
 *                THE PRIMITIVE RULES OF INFERENCE
 *---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------*
 *                                                                           *
 *       ---------  ASSUME M                           [M is boolean]        *
 *         M |- M                                                            *
 *---------------------------------------------------------------------------*)

fun ASSUME tm =
   (Assert (is_bool tm) "ASSUME" "not a proposition";
    make_thm Count.Assume (empty_tag,single_hyp tm,tm));


(*---------------------------------------------------------------------------*
 *                                                                           *
 *         ---------  REFL M                                                 *
 *         |- M = M                                                          *
 *---------------------------------------------------------------------------*)

val mk_eq_nocheck = Term.prim_mk_eq;

fun refl_nocheck ty tm =
  make_thm Count.Refl (empty_tag, empty_hyp, mk_eq_nocheck ty tm tm);

fun REFL tm = refl_nocheck (type_of tm) tm;


(*---------------------------------------------------------------------------*
 *                                                                           *
 *         ------------------------  BETA_CONV "(\v.M) N"                    *
 *         |- (\v.M) N = M [v|->N]                                           *
 *---------------------------------------------------------------------------*)

fun BETA_CONV tm =
   make_thm Count.Beta
      (empty_tag, empty_hyp, mk_eq_nocheck (type_of tm) tm (beta_conv tm))
   handle HOL_ERR _ => ERR "BETA_CONV" "not a beta-redex"


(*---------------------------------------------------------------------------*
 *                                                                           *
 *     --------------------------------  TY_BETA_CONV "(!:'a.M) [:TY:]"      *
 *     |- (!:'a.M) [:TY:] = M ['a|->TY]                                      *
 *---------------------------------------------------------------------------*)

fun TY_BETA_CONV tm =
   make_thm Count.TyBeta
      (empty_tag, empty_hyp, mk_eq_nocheck (type_of tm) tm (ty_beta_conv tm))
   handle HOL_ERR _ => ERR "TY_BETA_CONV" "not a type-beta-redex"


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
                          val (lhs,rhs,_) = Term.dest_eq_ty c
                      in ((redex |-> lhs)::ltheta,
                          (redex |-> rhs)::rtheta,
                          union_hyp h hyps,
                          Tag.merge ocls Ocls)
                      end)
                replacements ([],[],asl,O)
 in
   if aconv (subst ltheta template) c
    then make_thm Count.Subst (oracles,hyps,subst rtheta template)
      else th
 end;

(*---------------------------------------------------------------------------*
 *        A |- t1 = t2                                                       *
 *   ------------------------  ABS x            [Where x is not free in A]   *
 *    A |- (\x.t1) = (\x.t2)                                                 *
 *---------------------------------------------------------------------------*)

fun ABS v (THM(ocl,asl,c)) =
 let val (lhs,rhs,ty) = Term.dest_eq_ty c handle HOL_ERR _
                      => ERR "ABS" "not an equality"
     val vty = snd(dest_var v) handle HOL_ERR _
                      => ERR "ABS" "first argument is not a variable"
 in if var_occursl v asl
     then ERR "ABS" "The variable is free in the assumptions"
     else make_thm Count.Abs
            (ocl, asl, mk_eq_nocheck (vty --> ty)
                                     (mk_abs(v,lhs))
                                     (mk_abs(v,rhs)))
 end;

(*---------------------------------------------------------------------------*
 *         A |- t1 = t2                                                      *
 *   --------------------------  TY_ABS x      [Where 'a is not free in A]   *
 *    A |- (!'a.t1) = (!'a.t2)                                               *
 *---------------------------------------------------------------------------*)

fun TY_ABS a (THM(ocl,asl,c)) =
 let val (lhs,rhs,ty) = Term.dest_eq_ty c handle HOL_ERR _
                      => ERR "TY_ABS" "not an equality"
     val (nm,kd,rk) = Type.dest_var_type a handle HOL_ERR _
                      => ERR "TY_ABS" "first argument is not a type variable"
 in if type_var_occursl a asl
     then ERR "TY_ABS" "The type variable is free in the assumptions"
     else make_thm Count.TyAbs
            (ocl, asl, mk_eq_nocheck (Type.mk_univ_type(a, ty))
                                     (mk_tyabs(a,lhs))
                                     (mk_tyabs(a,rhs)))
 end;

(*---------------------------------------------------------------------------*
 *   A |- t1 = t2                                                            *
 *  ------------------------------------  GEN_ABS f [v1,...,vn]              *
 *   A |- (Q v1...vn.t1) = (Q v1...vn.t2)    (where no vi is free in A)      *
 *---------------------------------------------------------------------------*)

fun GEN_ABS opt vlist (th as THM(ocl,asl,c)) =
 let open HOLset
     val vset = addList(Term.empty_varset,vlist)
     val hset = hyp_frees th
 in if isEmpty (intersection(vset,hset))
    then let val (lhs,rhs,ty) = with_exn Term.dest_eq_ty c
                                  (thm_err "GEN_ABS" "not an equality")
             val lhs' = list_mk_binder opt (vlist,lhs)
             val rhs' = list_mk_binder opt (vlist,rhs)
         in make_thm Count.GenAbs
               (ocl,asl,mk_eq_nocheck (Term.type_of lhs') lhs' rhs')
         end
    else ERR "GEN_ABS" "variable(s) free in the assumptions"
 end

(*---------------------------------------------------------------------------*
 *   A |- t1 = t2                                                            *
 *  --------------------------------------  GEN_TY_ABS f [a1,...,an]         *
 *   A |- (Q a1...an.t1) = (Q a1...an.t2)      (where no ai is free in A)    *
 *---------------------------------------------------------------------------*)

fun GEN_TY_ABS opt vlist (th as THM(ocl,asl,c)) =
 let open HOLset
     val vset = addList(Type.empty_tyset,vlist)
     val hset = hyp_tyvars th
 in if isEmpty (intersection(vset,hset))
    then let val (lhs,rhs,ty) = with_exn Term.dest_eq_ty c
                                  (thm_err "GEN_TY_ABS" "not an equality")
             val lhs' = list_mk_tybinder opt (vlist,lhs)
             val rhs' = list_mk_tybinder opt (vlist,rhs)
         in make_thm Count.GenTyAbs
               (ocl,asl,mk_eq_nocheck (Term.type_of lhs') lhs' rhs')
         end
    else ERR "GEN_TY_ABS" "variable(s) free in the assumptions"
 end

(*---------------------------------------------------------------------------
 *         A |- M
 *  --------------------  INST_RANK n
 *  A[rank + n/rank] |- M[rank + n/rank]
 *
 *---------------------------------------------------------------------------*)

fun INST_RANK n (th as THM(ocl,asl,c)) =
    if n = 0 then th
    else if n < 0 then raise ERR "INST_RANK" "rank instantiation cannot lower the rank"
    else let val instfn = Term.inst_rank n
         in make_thm Count.InstRank(ocl, hypset_map instfn asl, instfn c)
         end

(*---------------------------------------------------------------------------
 *         A |- M
 *  --------------------  INST_KIND theta
 *  theta(A) |- theta(M)
 *
 *---------------------------------------------------------------------------*)

fun INST_KIND [] th = th
  | INST_KIND theta (THM(ocl,asl,c)) =
    let val instfn = Term.inst_kind theta
    in make_thm Count.InstKind(ocl, hypset_map instfn asl, instfn c)
    end

(*---------------------------------------------------------------------------
 *         A |- M
 *  --------------------  INST_TYPE theta
 *  theta(A) |- theta(M)
 *
 *---------------------------------------------------------------------------*)

fun INST_TYPE [] th = th
  | INST_TYPE theta (THM(ocl,asl,c)) =
    let val r = Type.subst_rank theta
    in if r = 0 then let
         val instfn = inst theta
       in
         make_thm Count.InstType(ocl, hypset_map instfn asl, instfn c)
       end
       else let
         val theta' = Type.inst_rank_subst r theta
         val asl'   = hypset_map (Term.inst_rank r) asl
         val c'     = Term.inst_rank r c
         val instfn = inst theta'
       in
         make_thm Count.InstType(ocl, hypset_map instfn asl', instfn c')
       end
    end

(*---------------------------------------------------------------------------
 *          A |- M
 *  ---------------------- DISCH tm
 *     A - tm |- tm ==> M
 *
 * The term tm need not occur in A. All terms in A that are
 * alpha-convertible to tm are removed.
 *---------------------------------------------------------------------------*)

fun DISCH w (THM(ocl,asl,c)) =
  (Assert (is_bool w) "DISCH" "not a proposition";
   make_thm Count.Disch
      (ocl,
       HOLset.delete(asl, w) handle HOLset.NotFound => asl,
       Term.prim_mk_imp w c));


(*---------------------------------------------------------------------------
 *          A |- M ==> N ,  B |- M'
 *  ----------------------------------  MP
 *              A u B |- N
 *
 * M and M' must be alpha-convertible
 *---------------------------------------------------------------------------*)

fun MP (THM(o1,asl1,c1)) (THM(o2,asl2,c2)) =
 let val (ant,conseq) = dest_imp c1
 in Assert (aconv ant c2) "MP"
      "antecedent of first thm not alpha-convertible to concl. of second";
    make_thm Count.Mp (Tag.merge o1 o2, union_hyp asl1 asl2, conseq)
 end;


(*---------------------------------------------------------------------------*
 * Derived Rules -- these are here for efficiency purposes, and so that all  *
 * invocations of mk_thm are in Thm. The following derived rules do not use  *
 * any axioms of boolTheory:                                                 *
 *                                                                           *
 *   ALPHA, SYM, TRANS, MK_COMB, AP_TERM, AP_THM, EQ_MP, EQ_IMP_RULE,        *
 *   Beta, Mk_comb, Mk_abs, Mk_tycomb, Mk_tyabs                              *
 *                                                                           *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * Equivalence of alpha-convertible terms
 *
 *     t1, t2 alpha-convertable
 *     -------------------------
 *            |- t1 = t2
 *
 * fun ALPHA t1 t2 = TRANS (REFL t1) (REFL t2)
 *---------------------------------------------------------------------------*)

fun ALPHA t1 t2 =
   if aconv t1 t2 then
     make_thm Count.Alpha (empty_tag, empty_hyp,
                           mk_eq_nocheck (type_of t1) t1 t2)
   else ERR "ALPHA" "Terms not alpha-convertible";

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
 *   handle _ =>  ERR "SYM" "";
 *---------------------------------------------------------------------------*)

fun SYM th =
 let val (lhs,rhs,ty) = Term.dest_eq_ty (concl th)
  in make_thm Count.Sym
        (tag th, hypset th, mk_eq_nocheck ty rhs lhs)
 end
 handle HOL_ERR _ => ERR "SYM" "";

(*---------------------------------------------------------------------------
 * Transitivity of =
 *
 *   A1 |- t1 = t2  ,  A2 |- t2 = t3
 *  ---------------------------------
 *        A1 u A2 |- t1=t3
 *
 * fun TRANS th1 th2 =
 *   let val (t1,t2) = dest_eq(concl th1)
 *       and (t2',t3) = dest_eq(concl th2)
 *       val v = genvar(type_of t1)
 *   in
 *   SUBST [(th2,v)] (mk_eq(t1,v)) th1
 *   end
 *   handle _ =>  ERR{function = "TRANS",message = ""};
 *
 *---------------------------------------------------------------------------*)

fun TRANS th1 th2 =
   let val (lhs1,rhs1,ty) = Term.dest_eq_ty (concl th1)
       and (lhs2,rhs2,_)  = Term.dest_eq_ty (concl th2)
       val   _  = Assert (aconv rhs1 lhs2) "" ""
       val hyps = union_hyp (hypset th1) (hypset th2)
       val ocls = Tag.merge (tag th1) (tag th2)
   in
     make_thm Count.Trans (ocls, hyps, mk_eq_nocheck ty lhs1 rhs2)
   end
   handle HOL_ERR e  => (print (Feedback.format_ERR e);
                           ERR "TRANS" "");


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
   let val (f,g,ty) = Term.dest_eq_ty (concl funth)
       val (x,y,_)  = Term.dest_eq_ty (concl argth)
   in
     make_thm Count.MkComb
         (Tag.merge (tag funth) (tag argth),
          union_hyp (hypset funth) (hypset argth),
          mk_eq_nocheck (rng ty) (mk_comb(f,x)) (mk_comb(g,y)))
   end
   handle HOL_ERR _ => ERR "MK_COMB" "";

(*---------------------------------------------------------------------------
 *         A |- t1 = t2
 *   --------------------------------  TY_COMB ty
 *    A |- (t1 [:ty:]) = (t2 [:ty:])
 *
 * fun TY_COMB ty th =
 *  let val (lhs,rhs,ty1) = Term.dest_eq_ty (concl th)
 *      val (bv,ty2) = Type.dest_univ_type ty1
 *      val gv = genvar ty1
 *      val lcmb = mk_tycomb(lhs,ty)
 *      val gcmb = mk_tycomb( gv,ty)
 *      val tm3 = mk_eq_nocheck (type_of lcmb) lcmb gcmb
 *  in (* SUBS_OCCS [([2], th)] (REFL (TyComb(lhs,ty))) *)
 *     SUBST [gv |-> th] tm3 (REFL lcmb)
 *  end
 *---------------------------------------------------------------------------*)

fun TY_COMB th ty =
 let val (lhs,rhs,ty1) = Term.dest_eq_ty (concl th) handle HOL_ERR _
                       => ERR "TY_COMB" "not an equality"
     val (bv,ty2) = Type.dest_univ_type ty1 handle HOL_ERR _
                       => ERR "TY_COMB" "not an equality of a universal type"
     val lcmb = mk_tycomb(lhs,ty) handle HOL_ERR {message, ...}
                       => ERR "TY_COMB" message
     val rcmb = mk_tycomb(rhs,ty) handle HOL_ERR {message, ...}
                       => ERR "TY_COMB" message
 in make_thm Count.TyComb
        (tag th,
         hypset th,
         mk_eq_nocheck (type_of lcmb) lcmb rcmb)
      handle HOL_ERR _ => ERR "TY_COMB" ""
 end;

(*---------------------------------------------------------------------------
 * Application of a term to a theorem
 *
 *    A |- t1 = t2
 * ------------------
 *  A |- t t1 = t t2
 *
 * fun AP_TERM tm th =
 *   let val (t1,_) = dest_eq(concl th)
 *       val th1 = REFL (--`^tm ^t1`--)
 *       (* th1 = |- t t1 = t t1 *)
 *       and v  = genvar(type_of t1)
 *   in
 *   SUBST [(th,v)] (--`^tm ^t1 = ^tm ^v`--) th1
 *   end
 *   handle _ =>  ERR{function = "AP_TERM",message = ""};
 *---------------------------------------------------------------------------*)

fun AP_TERM f th =
 let val (lhs,rhs,_) = Term.dest_eq_ty (concl th)
 in make_thm Count.ApTerm
       (tag th, hypset th,
        mk_eq_nocheck (rng (type_of f)) (mk_comb(f,lhs)) (mk_comb(f,rhs)))
 end
 handle HOL_ERR _ => ERR "AP_TERM" "";


(*---------------------------------------------------------------------------
 * Application of a theorem to a term
 *
 *    A |- t1 = t2
 *   ----------------
 *   A |- t1 t = t2 t
 *
 * fun AP_THM th tm =
 *   let val (t1,_) = dest_eq(concl th)
 *       val th1 = REFL (--`^t1 ^tm`--)
 *       (* th1 = |- t1 t = t1 t *)
 *       and v   = genvar(type_of t1)
 *   in
 *   SUBST [(th,v)] (--`^t1 ^tm = ^v ^tm`--) th1
 *   end
 *   handle _ =>  ERR{function = "AP_THM",message = ""};
 *---------------------------------------------------------------------------*)

fun AP_THM th tm =
 let val (lhs,rhs,ty) = Term.dest_eq_ty (concl th)
 in make_thm Count.ApThm
       (tag th, hypset th,
        mk_eq_nocheck (rng ty) (mk_comb(lhs,tm)) (mk_comb(rhs,tm)))
 end
 handle HOL_ERR _ => ERR "AP_THM" "";

(*---------------------------------------------------------------------------
 *  Modus Ponens for =
 *
 *
 *   A1 |- t1 = t2  ,  A2 |- t1
 *  ----------------------------
 *        A1 u A2 |- t2
 *
 * fun EQ_MP th1 th2 =
 *   let val (t1,t2) = dest_eq(concl th1)
 *       val v = genvar(type_of t1)
 *   in  SUBST [(th1,v)] v th2
 *   end handle _ =>  ERR{function = "EQ_MP",message = ""};
 *---------------------------------------------------------------------------*)

fun EQ_MP th1 th2 =
   let val (lhs,rhs,_) = Term.dest_eq_ty (concl th1)
       val _ = Assert (aconv lhs (concl th2)) "" ""
   in
    make_thm Count.EqMp (Tag.merge (tag th1) (tag th2),
                         union_hyp (hypset th1) (hypset th2), rhs)
   end handle HOL_ERR _ => ERR "EQ_MP" "";

(*---------------------------------------------------------------------------
 *              A |- t1 = t2
 *    ------------------------------------
 *     A |- t1 ==> t2      A |- t2 ==> t1
 *
 * fun EQ_IMP_RULE th =
 *   let val (t1,t2) = dest_eq(concl th)
 *   in
 *   (DISCH t1 (EQ_MP th (ASSUME t1)),
 *    DISCH t2 (EQ_MP (SYM th)(ASSUME t2)))
 *   end
 *   handle _ =>  ERR{function = "EQ_IMP_RULE",message = ""};
 *---------------------------------------------------------------------------*)

fun EQ_IMP_RULE th =
 let val (lhs,rhs,ty) = Term.dest_eq_ty (concl th)
     and A = hypset th
     and O = tag th
 in if ty = Type.bool
    then (make_thm Count.EqImpRule(O,A, Term.prim_mk_imp lhs rhs),
          make_thm Count.EqImpRule(O,A, Term.prim_mk_imp rhs lhs))
    else ERR "" ""
 end
 handle HOL_ERR _ => ERR "EQ_IMP_RULE" "";

(*---------------------------------------------------------------------------
 * Specialization
 *
 *    A |- !(\x.u)
 *  --------------------   (where t is free for x in u)
 *    A |- u[t/x]
 *
 * fun SPEC t th =
 *   let val {Rator=F,Rand=body} = dest_comb(concl th)
 *   in
 *   if (not(#Name(dest_const F)="!"))
 *   then ERR{function = "SPEC",message = ""}
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
 *   handle _ => ERR{function = "SPEC",message = ""};
 *
 *
 * pre-dB manner:
 * fun SPEC t th =
 *   let val {Bvar,Body} = dest_forall(concl th)
 *   in
 *   make_thm Count.(hypset th, subst[{redex = Bvar, residue = t}] Body)
 *   end
 *   handle _ => ERR{function = "SPEC",message = ""};
 *---------------------------------------------------------------------------*)

fun SPEC t th =
 let val (Rator,Rand) = dest_comb(concl th)
     val {Thy,Name,...} = dest_thy_const Rator
 in
   Assert (Name="!" andalso Thy="bool")
          "SPEC" "Theorem not universally quantified";
   make_thm Count.Spec
       (tag th, hypset th, beta_conv(mk_comb(Rand, t)))
       handle HOL_ERR _ =>
              raise thm_err "SPEC"
                    "Term argument's type not equal to bound variable's"
 end;

(*---------------------------------------------------------------------------
 * Type Specialization
 *
 *    A |- !(\:a.u)
 *  --------------------   (where ty is free for a in u)
 *    A |- u[ty/a]
 *
 * fun TY_SPEC ty th =
 *   let val (F,body) = dest_comb(concl th)
 *   in
 *   if (not(fst(dest_const F)="!:"))
 *   then raise ERR "TY_SPEC" "not a type forall"
 *   else let val (a,u) = dest_tyabs body
 *        and v1 = genvar(type_of F)
 *        and v2 = genvar(type_of body)
 *        val th1 = SUBST[v1 |-> TY_FORALL_DEF] (mk_comb(v1,body)) th
 *        (* th1 = |- (\P. P = (\:a. T))(\:a. t1 [:a:]) *)
 *        val th2 = BETA_CONV(concl th1)
 *        (* th2 = |- (\P. P = (\:a. T))(\:a. t1 [:a:]) = ((\:a. t1 [:a:]) = (\:a. T)) *)
 *        val th3 = EQ_MP th2 th1
 *        (* th3 = |- (\:a. t1 [:a:]) = (\:a. T) *)
 *        val s1 = mk_tycomb(body,ty)
 *        val s2 = mk_tycomb(v2,ty)
 *        val th4 = SUBST [v2 |-> th3] (mk_eq(s1,s2)) (* --`^body [:^ty:] = ^v2 [:^ty:]`-- *)
 *                        (REFL s1)
 *        (* th4 = |- (\:a. t1 [:a:]) [:ty:] = (\:a. T) [:ty:] *)
 *        val (ls,rs) = dest_eq(concl th4)
 *        val th5 = TRANS(TRANS(SYM(TY_BETA_CONV ls))th4)(TY_BETA_CONV rs)
 *        (* th5 = |- t1 [:ty:] = T *)
 *        in
 *        EQT_ELIM th5
 *        end
 *   end
 *   handle _ => raise ERR "TY_SPEC" "";
 *
 *
 * pre-dB manner:
 * fun TY_SPEC ty th =
 *   let val {Bvar,Body} = dest_ty_forall(concl th)
 *   in
 *   make_thm Count.(hypset th, inst[{redex = Bvar, residue = ty}] Body)
 *   end
 *   handle _ => raise ERR "TY_SPEC" "";
 *---------------------------------------------------------------------------*)

fun TY_SPEC ty th =
 let val (Rator,Rand) = dest_comb(concl th)
     val {Thy,Name,...} = dest_thy_const Rator
 in
   Assert (Name="!:" andalso Thy="bool")
          "TY_SPEC" "Theorem not universally type quantified";
   make_thm Count.TySpec
       (tag th, hypset th, ty_beta_conv(mk_tycomb(Rand, ty)))
       handle HOL_ERR _ =>
              raise thm_err "TY_SPEC"
                    "Type argument not equal to bound variable"
 end;


(*---------------------------------------------------------------------------
 * Generalization
 *
 *         A |- t
 *   -------------------   (where x not free in A)
 *       A |- !(\x.t)
 *
 * fun GEN x th =
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
 *      handle _ => ERR{function = "GEN",message = ""};
 *---------------------------------------------------------------------------*)


fun GEN x th =
  let val (asl,c) = sdest_thm th
  in if var_occursl x asl
     then ERR  "GEN" "variable occurs free in hypotheses"
     else make_thm Count.Gen(tag th, asl, Susp.force mk_forall x c)
          handle HOL_ERR _ => ERR "GEN" ""
  end;

fun GENL vs th = let
  val (asl,c) = sdest_thm th
in
  if exists (fn v => var_occursl v asl) vs then
    ERR "GENL" "variable occurs free in hypotheses"
  else
    make_thm
      Count.Gen(tag th, asl,
                list_mk_binder (SOME (prim_mk_const {Thy="bool", Name="!"}))
                               (vs,c))
    handle HOL_ERR _ => ERR "GENL" ""
end


(*---------------------------------------------------------------------------
 * Type Generalization
 *
 *         A |- t
 *   -------------------   (where a not free in A)
 *       A |- !(\:a.t)
 *
 * fun TY_GEN a th =
 *   let val th1 = TY_ABS a (EQT_INTRO th)
 *     (* th1 = |- (\:a. t1 [:a:]) = (\:a. T)  --TY_ABS does not behave this way --KLS*)
 *      val ty1 = mk_univ_type(a,bool) --> bool
 *      val abs = mk_tyabs(a,concl th)
 *      and v1 = genvar ty1
 *      and v2 = genvar bool
 *      val s1 = mk_comb(mk_thy_const{Thy="bool", Name="!:", Ty=ty1}, abs)
 *      val s2 = mk_eq(s1, mk_comb(v1, abs))
 *      val th2 = SUBST [v1 |-> TY_FORALL_DEF] s2 (REFL s1)
 *      (* th2 = |- (!:a. t1 [:a:]) = (\P. P = (\:a. T))(\:a. t1 [:a:]) *)
 *      val th3 = TRANS th2 (BETA_CONV(snd(dest_eq(concl th2))))
 *      (* th3 = |- (!:a. t1 [:a:]) = ((\:a. t1 [:a:]) = (\:a. T)) *)
 *      in
 *      SUBST [v2 |-> SYM th3] v2 th1
 *      end
 *      handle _ => ERR "TY_GEN" "";
 *---------------------------------------------------------------------------*)


fun TY_GEN a th =
  let val (asl,c) = sdest_thm th
  in if type_var_occursl a asl
     then ERR  "TY_GEN" "type variable occurs free in hypotheses"
     else make_thm Count.TyGen(tag th, asl, Susp.force mk_tyforall a c)
          handle HOL_ERR _ => ERR "TY_GEN" ""
  end;



(*---------------------------------------------------------------------------
 * Existential introduction
 *
 *    A |- t[t']
 *  --------------  EXISTS ("?x.t[x]", "t'")  ( |- t[t'] )
 *   A |- ?x.t[x]
 *
 *
 *
 * fun EXISTS (fm,tm) th =
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
 *   handle _ => ERR{function = "EXISTS",message = ""};
 *
 *---------------------------------------------------------------------------*)

local
  val mesg1 = "First argument not of form `?x. P`"
  val mesg2 = "(2nd argument)/(bound var) in body of 1st argument is not theorem's conclusion"
  val err = thm_err "EXISTS" mesg1
in
fun EXISTS (w,t) th =
 let val (ex,Rand) = with_exn dest_comb w err
     val {Name,Thy,...}  = with_exn dest_thy_const ex err
     val _ = Assert ("?"=Name andalso Thy="bool") "EXISTS" mesg1
     val _ = Assert (aconv (beta_conv(mk_comb(Rand,t))) (concl th))
                    "EXISTS" mesg2
   in make_thm Count.Exists (tag th, hypset th, w)
   end
end;


(*---------------------------------------------------------------------------
 * Type existential introduction
 *
 *      A |- t[ty]
 *  ------------------  TY_EXISTS ("?:a:k.t[a:k]", "ty:k")  ( |- t[ty] )
 *   A |- ?:a:k.t[a:k]
 *
 *
 *
 * fun TY_EXISTS (fm,ty) th =
 *   let val (a,t) = dest_tyexists fm
 *       val tm1 = mk_tyabs(a,t)
 *       val tm2 = mk_tycomb(tm1,ty)
 *       val tm3 = mk_tyabs(a,mk_const("F",bool))
 *       val tm4 = mk_eq(tm1,tm3)
 *       val th1 = TY_BETA_CONV tm2
 *       (* th1 = |- (\:a. t [:a:]) [:ty:] = t [:ty:] *)
 *       val th2 = EQ_MP (SYM th1) th
 *       (* th2 = |- (\:a. t [:a:]) [:ty:] *)
 *       val th3 = 
 *       (* th3 = |- (\x. t x)(@x. t x) *)
 *       val th4 = AP_THM TY_EXISTS_DEF tm1
 *       (* th4 = |- (?x. t x) = (\P. P($@ P))(\x. t x) *)
 *       val th5 = TRANS th4 (BETA_CONV(snd(dest_eq(concl th4))))
 *       (* th5 = |- (?x. t x) = (\x. t x)(@x. t x) *)
 *       val th6 = TRANS th5 (AP_THM NOT_DEF tm4)
 *       val th7 = TRANS th6 (BETA_CONV(snd(dest_eq(concl th6))))
 *       val th8 = TY_COMB (ASSUME tm4) ty
 *       val th9 = TRANS th8 (TY_BETA_CONV(rhs(concl th8)))
 *       val th10 = TRANS (SYM (TY_BETA_CONV(lhs(concl th8)))) th9
 *       val th11 = EQ_MP th10 th
 *       val th12 = DISCH tm4 th11
 *   in
 *   EQ_MP (SYM th7) th12
 *   end
 *   handle _ => ERR "EXISTS" "";
 *
 *---------------------------------------------------------------------------*)

local
  val mesg1 = "First argument not of form `?:a. P`"
  val mesg2 = "(2nd argument)/(bound type var) in body of 1st argument is not theorem's conclusion"
  val err = thm_err "TY_EXISTS" mesg1
in
fun TY_EXISTS (w,ty) th =
 let val (ex,Rand) = with_exn dest_comb w err
     val {Name,Thy,...}  = with_exn dest_thy_const ex err
     val _ = Assert ("?:"=Name andalso Thy="bool") "TY_EXISTS" mesg1
     val _ = Assert (aconv (ty_beta_conv(mk_tycomb(Rand,ty))) (concl th))
                    "TY_EXISTS" mesg2
   in make_thm Count.TyExists (tag th, hypset th, w)
   end
end;


(*---------------------------------------------------------------------------
 * Existential elimination
 *
 *   A1 |- ?x.t[x]   ,   A2, "t[v]" |- t'
 *   ------------------------------------     (variable v occurs nowhere)
 *            A1 u A2 |- t'
 *
 * fun CHOOSE (v,th1) th2 =
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
 *   handle _ => ERR{function = "CHOOSE",message = ""};
 *---------------------------------------------------------------------------*)

fun disch(w,wl) = HOLset.delete(wl,w) handle HOLset.NotFound => wl

fun CHOOSE (v,xth) bth =
  let val (x_asl, x_c) = sdest_thm xth
      val (b_asl, b_c) = sdest_thm bth
      val (Bvar,Body)  = dest_exists x_c
      val A2_hyps = disch (subst [Bvar |-> v] Body, b_asl)
      val newhyps = union_hyp x_asl A2_hyps
      val occursv = var_occurs v
      val _ = Assert (not(occursv x_c) andalso
                      not(occursv b_c) andalso
                      not(hypset_exists occursv A2_hyps)) "" ""
    (* Need not check for occurrence of v in A1: one can imagine
       implementing a derived rule on top of a more restrictive one that
       instantiated the occurrence of v in A1 to something else, applied
       the restrictive rule, and then instantiated it back again.

       Credit for pointing out this optimisation to Jim Grundy and
       Tom Melham. *)
  in make_thm Count.Choose
       (Tag.merge (tag xth) (tag bth), newhyps,  b_c)
  end
  handle HOL_ERR _ => ERR "CHOOSE" "";


(*---------------------------------------------------------------------------
 * Type existential elimination
 *
 *   A1 |- ?:a.t[a]   ,   A2, "t[b]" |- t'
 *   ------------------------------------     (type variable b occurs nowhere)
 *            A1 u A2 |- t'
 *
 * fun TY_CHOOSE (v,th1) th2 =
 *   let val (a,body) = dest_tyexists(concl th1)
 *       and t'     = concl th2
 *       and v1     = genvar bool
 *       val tm1 = mk_tyabs(a,body)
 *       val th3 = AP_THM TY_EXISTS_DEF tm1
 *       (* th3 = |- (?:a. t [:a:]) = (\P. ~(P = (\:a. F))) (\:a. t [:a:]) *)
 *       val th4 = EQ_MP th3 th1
 *       (* th4 = |- (\P. ~(P = (\:a. F))) (\:a. t [:a:]) *)
 *       val th5 = EQ_MP (BETA_CONV(concl th4)) th4
 *       (* th5 = |- ~((\:a. t [:a:]) = (\:a. F)) *)
 *       val th6 = TY_BETA_CONV (mk_tycomb(tm1,v))
 *       (* th6 = |- (\a. t [:a:]) [:v:] = t [:v:] *)
 *       val Pa = snd(dest_eq(concl th6))
 *       val th7 = UNDISCH(SUBST [v1 |-> SYM th6] (mk_imp(v1,t'))  (DISCH Pa th2))
 *       (* th7 = |- t' *)
 *       val tm2 = mk_eq(tm1, mk_tyabs(a,F))
 *       val th8 = AP_THM NOT_DEF tm2
 *       val th9 = TRANS th8 (BETA_CONV(snd(dest_eq(concl th8))))
 *       val th10 = TY_COMB (ASSUME tm2) v
 *       val th11 = TRANS th10 (TY_BETA_CONV(rhs(concl th10)))
 *       val th12 = TRANS (SYM (TY_BETA_CONV(lhs(concl th10)))) th11
 *       val th13 = DISCH tm2 (EQ_MP th12 (ASSUME (lhs(concl th12))))
 *       val th14 = EQ_MP th10 th)
 *       val th12 = DISCH tm4 th11
 * 
 *   in
 *   SELECT_ELIM th5 (v,th7)  ??? not right
 *   end
 *   handle _ => ERR "TY_CHOOSE" ""};
 *---------------------------------------------------------------------------*)

fun TY_CHOOSE (v,xth) bth =
  let val (x_asl, x_c) = sdest_thm xth
      val (b_asl, b_c) = sdest_thm bth
      val (Bvar,Body)  = dest_tyexists x_c
      val A2_hyps = disch (inst [Bvar |-> v] Body, b_asl)
      val newhyps = union_hyp x_asl A2_hyps
      val occursv = type_var_occurs v
      val _ = Assert (not(occursv x_c) andalso
                      not(occursv b_c) andalso
                      not(hypset_exists occursv A2_hyps)) "" ""
    (* Need not check for occurrence of v in A1: one can imagine
       implementing a derived rule on top of a more restrictive one that
       instantiated the occurrence of v in A1 to something else, applied
       the restrictive rule, and then instantiated it back again.

       Credit for pointing out this optimisation to Jim Grundy and
       Tom Melham. *)
  in make_thm Count.TyChoose
       (Tag.merge (tag xth) (tag bth), newhyps,  b_c)
  end
  handle HOL_ERR _ => ERR "TY_CHOOSE" "incorrect arguments";


(*---------------------------------------------------------------------------
 * Conjunction introduction rule
 *
 *   A1 |- t1  ,  A2 |- t2
 *  -----------------------
 *    A1 u A2 |- t1 /\ t2
 *
 * fun CONJ th1 th2 = MP (MP (SPEC (concl th2)
 *                             (SPEC (concl th1) AND_INTRO_THM))
 *                          th1)
 *                      th2;
 *---------------------------------------------------------------------------*)

fun CONJ th1 th2 =
   make_thm Count.Conj
        (Tag.merge (tag th1) (tag th2),
         union_hyp (hypset th1) (hypset th2),
         Susp.force mk_conj(concl th1, concl th2))
   handle HOL_ERR _ => ERR "CONJ" "";


(*---------------------------------------------------------------------------
 * Left conjunct extraction
 *
 *   A |- t1 /\ t2
 *   -------------
 *      A |- t1
 *
 * fun CONJUNCT1 th =
 *   let val (t1,t2) = dest_conj(concl th)
 *   in
 *   MP (SPEC t2 (SPEC t1 AND1_THM)) th
 *   end
 *   handle _ => ERR{function = "CONJUNCT1",message = ""};
 *
 *---------------------------------------------------------------------------*)

fun conj1 tm =
  let val (c,M) = dest_comb (rator tm)
      val {Name,Thy,...} = dest_thy_const c
  in
    if Name="/\\" andalso Thy="bool" then M else ERR "" ""
  end


fun CONJUNCT1 th =
  make_thm Count.Conjunct1 (tag th, hypset th, conj1 (concl th))
  handle HOL_ERR _ => ERR "CONJUNCT1" "";


(*---------------------------------------------------------------------------
 *  Right conjunct extraction
 *
 *   A |- t1 /\ t2
 *   -------------
 *      A |- t2
 *
 * fun CONJUNCT2 th =
 *   let val (t1,t2) = dest_conj(concl th)
 *   in
 *   MP (SPEC t2 (SPEC t1 AND2_THM)) th
 *   end
 *   handle _ => ERR{function = "CONJUNCT2",message = ""};
 *---------------------------------------------------------------------------*)

fun conj2 tm =
  let val (Rator,M) = dest_comb tm
      val {Name,Thy,...} = dest_thy_const (rator Rator)
  in
     if Name="/\\" andalso Thy="bool" then M else ERR "" ""
  end

fun CONJUNCT2 th =
 make_thm Count.Conjunct2 (tag th, hypset th, conj2 (concl th))
  handle HOL_ERR _ => ERR "CONJUNCT2" "";


(*---------------------------------------------------------------------------
 * Left disjunction introduction
 *
 *      A |- t1
 *  ---------------
 *   A |- t1 \/ t2
 *
 * fun DISJ1 th t2 = MP (SPEC t2 (SPEC (concl th) OR_INTRO_THM1)) th
 *           handle _ => ERR{function = "DISJ1",message = ""};
 *---------------------------------------------------------------------------*)

fun DISJ1 th w = make_thm Count.Disj1
 (tag th, hypset th, Susp.force mk_disj (concl th, w))
 handle HOL_ERR _ => ERR "DISJ1" "";


(*---------------------------------------------------------------------------
 * Right disjunction introduction
 *
 *      A |- t2
 *  ---------------
 *   A |- t1 \/ t2
 *
 * fun DISJ2 t1 th = MP (SPEC (concl th) (SPEC t1 OR_INTRO_THM2)) th
 *          handle _ => ERR{function = "DISJ2",message = ""};
 *---------------------------------------------------------------------------*)

fun DISJ2 w th = make_thm Count.Disj2
 (tag th, hypset th, Susp.force mk_disj(w,concl th))
 handle HOL_ERR _ => ERR "DISJ2" "";


(*---------------------------------------------------------------------------
 * Disjunction elimination
 *
 *   A |- t1 \/ t2   ,   A1,t1 |- t   ,   A2,t2 |- t
 *   -----------------------------------------------
 *               A u A1 u A2 |- t
 *
 * fun DISJ_CASES th1 th2 th3 =
 *   let val (t1,t2) = dest_disj(concl th1)
 *       and t = concl th2
 *       val th4 = SPEC t2 (SPEC t1 (SPEC t OR_ELIM_THM))
 *   in
 *   MP (MP (MP th4 th1) (DISCH t1 th2)) (DISCH t2 th3)
 *   end
 *   handle _ => ERR{function = "DISJ_CASES",message = ""};
 *---------------------------------------------------------------------------*)

fun dest_disj tm =
  let val (Rator,N) = dest_comb tm
      val (c,M)     = dest_comb Rator
      val {Name,Thy,...}   = dest_thy_const c
  in
    if Name="\\/" andalso Thy="bool" then (M,N) else ERR "" ""
  end


fun DISJ_CASES dth ath bth =
  let val _ = Assert (aconv (concl ath) (concl bth)) "" ""
      val (disj1,disj2) = dest_disj (concl dth)
  in
   make_thm Count.DisjCases
       (itlist Tag.merge [tag dth, tag ath, tag bth] empty_tag,
        union_hyp (hypset dth) (union_hyp (disch(disj1, hypset ath))
                                       (disch(disj2, hypset bth))),
        concl ath)
  end
  handle HOL_ERR _ => ERR "DISJ_CASES" "";


(*---------------------------------------------------------------------------
 * NOT introduction
 *
 *     A |- t ==> F
 *     ------------
 *       A |- ~t
 *
 * fun NOT_INTRO th =
 *   let val (t,_) = dest_imp(concl th)
 *   in MP (SPEC t IMP_F) th
 *   end
 *   handle _ => ERR{function = "NOT_INTRO",message = ""};
 *---------------------------------------------------------------------------*)

fun NOT_INTRO th =
  let val (ant,c) = dest_imp(concl th)
  in Assert (eq c (Susp.force F)) "" "";
     make_thm Count.NotIntro  (tag th, hypset th, Susp.force mk_neg ant)
  end
  handle HOL_ERR _ => ERR "NOT_INTRO" "";


(*---------------------------------------------------------------------------
 * Negation elimination
 *
 *       A |- ~ t
 *     --------------
 *      A |- t ==> F
 *
 * fun NOT_ELIM th =
 *   let val (_,t) = dest_comb(concl th)
 *   in MP (SPEC t F_IMP) th
 *   end
 *   handle _ => ERR{function = "NOT_ELIM",message = ""};
 *---------------------------------------------------------------------------*)

local fun dest M =
        let val (Rator,Rand)  = dest_comb M
        in (dest_thy_const Rator, Rand)
        end
in
fun NOT_ELIM th =
  case with_exn dest (concl th) (thm_err "NOT_ELIM" "")
   of ({Name="~", Thy="bool",...},Rand)
       => make_thm Count.NotElim
             (tag th, hypset th, Term.prim_mk_imp Rand (Susp.force F))
    | otherwise => ERR "NOT_ELIM" ""
end;


(*---------------------------------------------------------------------------*
 * Classical contradiction rule                                              *
 *                                                                           *
 *   A,"~t" |- F                                                             *
 *   --------------                                                          *
 *       A |- t                                                              *
 *                                                                           *
 * fun CCONTR t th =                                                         *
 * let val th1 = RIGHT_BETA(AP_THM NOT_DEF t)                                *
 *     and v   = genvar (--`:bool`--)                                        *
 *     val th2 = EQT_ELIM (ASSUME (--`^t = T`--))                            *
 *     val th3 = SUBST [(th1,v)] (--`^v ==> F`--) (DISCH (--`~ ^t`--) th)    *
 *     val th4 = SUBST[(ASSUME(--`^t = F`--),v)] (--`(^v ==>F)==>F`--)th3    *
 *     val th5 = MP th4 (EQT_ELIM (CONJUNCT2 IMP_CLAUSE4))                   *
 *     val th6 = EQ_MP (SYM(ASSUME (--`^t = F`--))) th5                      *
 * in                                                                        *
 * DISJ_CASES (SPEC t BOOL_CASES_AX) th2 th6                                 *
 * end handle _ => ERR{function = "CCONTR",message = ""}                     *
 *---------------------------------------------------------------------------*)

fun CCONTR w fth =
  (Assert (eq (concl fth) (Susp.force F)) "CCONTR" "";
   make_thm Count.Ccontr
       (tag fth, disch(Susp.force mk_neg w, hypset fth), w)
     handle HOL_ERR _ => ERR "CCONTR" "");


(*---------------------------------------------------------------------------*
 * Instantiate free variables in a theorem                                   *
 *---------------------------------------------------------------------------*)

fun INST [] th = th
  | INST theta th =
      if List.all (is_var o #redex) theta then
        let
          val substf = subst theta
        in
          make_thm Count.Inst
            (tag th, hypset_map substf (hypset th), substf (concl th))
          handle HOL_ERR _ => ERR "INST" ""
        end
      else
        raise ERR "INST" "can only instantiate variables"


(*---------------------------------------------------------------------------*
 * Now some derived rules optimized for computations, avoiding most          *
 * of useless type-checking, using pointer equality and delayed              *
 * substitutions. See computeLib for further details.                        *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*
 *    A |- t = (\x.m) n                                                      *
 *  --------------------- Beta                                               *
 *     A |- t = m{x\n}                                                       *
 *                                                                           *
 * Other implementation (less efficient not using explicit subst.):          *
 *   val Beta = Drule.RIGHT_BETA                                             *
 *---------------------------------------------------------------------------*)

fun Beta th =
   let val (lhs, rhs, ty) = Term.dest_eq_ty (concl th)
   in make_thm Count.Beta
        (tag th, hypset th, mk_eq_nocheck ty lhs (Term.lazy_beta_conv rhs))
   end
   handle HOL_ERR _ => ERR "Beta" "";


(*---------------------------------------------------------------------------*
 * This rule behaves like a tactic: given a goal (reducing the rhs of thm),  *
 * it returns two subgoals (reducing the rhs of th1 and th2), together       *
 * with a validation (mkthm), that builds the normal form of t from the      *
 * normal forms of u and v.                                                  *
 * NB: we do not have to typecheck the rator u, and we replaced the alpha    *
 * conversion test with pointer equality.                                    *
 *                                                                           *
 *                     |- u = u    (th1)        |- v = v    (th2)            *
 *       (thm)             ...                     ...                       *
 *    A |- t = u v    A' |- u = u' (th1')     A'' |- v = v' (th2')           *
 *  ----------------------------------------------------------------         *
 *                A u A' u A'' |- t = u' v'                                  *
 *                                                                           *
 * Could be implemented outside Thm as:                                      *
 *   fun Mk_comb th =                                                        *
 *     let val {Rator,Rand} = dest_comb(rhs (concl th))                      *
 *         fun mka th1 th2 = TRANS th (MK_COMB(th1,th2)) in                  *
 *     (REFL Rator, REFL Rand, mka)                                          *
 *     end                                                                   *
 *---------------------------------------------------------------------------*)

fun Mk_comb thm =
   let val (lhs, rhs, ty) = Term.dest_eq_ty (concl thm)
       val (Rator,Rand) = dest_comb rhs
       fun mkthm th1' th2' =
         let val (lhs1, rhs1, _) = Term.dest_eq_ty (concl th1')
             val _ = Assert (EQ(lhs1,Rator)) "" ""
             val (lhs2, rhs2, _) = Term.dest_eq_ty (concl th2')
             val _ = Assert (EQ(lhs2,Rand)) "" ""
             val (ocls,hyps) = tag_hyp_union [thm, th1', th2']
         in make_thm Count.MkComb
	   (ocls, hyps, mk_eq_nocheck ty lhs (mk_comb(rhs1,rhs2)))
         end
	 handle HOL_ERR _ => ERR "Mk_comb" "";
       val aty = type_of Rand    (* typing! *)
       val th1 = refl_nocheck (aty --> ty) Rator
       val th2 = refl_nocheck aty Rand
   in (th1,th2,mkthm)
   end
   handle HOL_ERR _ => ERR "Mk_comb" "";

(*---------------------------------------------------------------------------*
 *                      |- u = u    (th1)                                    *
 *       (thm)              ...                                              *
 *    A |- t = \x.u    A' |- u = u' (th1')                                   *
 *  ---------------------------------------- x not in FV(A')                 *
 *            A u A' |- t = \x.u'                                            *
 *                                                                           *
 * Could be implemented outside Thm as:                                      *
 *   fun Mk_abs th =                                                         *
 *     let val {Bvar,Body} = dest_abs(rhs (concl th)) in                     *
 *     (Bvar, REFL Body, (fn th1 => TRANS th (ABS Bvar th1)))                *
 *     end                                                                   *
 *---------------------------------------------------------------------------*)

fun Mk_abs thm =
   let val (lhs, rhs, ty) = Term.dest_eq_ty (concl thm)
       val (Bvar,Body) = dest_abs rhs
       fun mkthm th1' =
         let val (lhs1, rhs1, _) = Term.dest_eq_ty (concl th1')
             val _ = Assert (EQ(lhs1,Body)) "" ""
             val _ = Assert (not (var_occursl Bvar (hypset th1'))) "" ""
             val (ocls,hyps) = tag_hyp_union [thm, th1']
         in make_thm Count.Abs
	   (ocls, hyps, mk_eq_nocheck ty lhs (mk_abs(Bvar, rhs1)))
         end
	 handle HOL_ERR _ => ERR "Mk_abs" ""
       val th1 = refl_nocheck (rng ty) Body
   in (Bvar,th1,mkthm)
   end
   handle HOL_ERR _ => ERR "Mk_abs" "";


(*---------------------------------------------------------------------------*
 * This rule behaves like a tactic: given a goal (reducing the rhs of thm),  *
 * it returns a subgoal (reducing the rhs of th1), together with a           *
 * validation (mkthm), that builds the normal form of t from the normal form *
 * of u.                                                                     *
 * NB: we do not have to typecheck the rator u, and we replaced the alpha    *
 * conversion test with pointer equality.                                    *
 *                                                                           *
 *                          |- u = u    (th1)                                *
 *       (thm)                  ...                                          *
 *    A |- t = u [:ty:]    A' |- u = u' (th1')                               *
 *  ----------------------------------------------------------------         *
 *                A u A' |- t = u' [:ty:]                                    *
 *                                                                           *
 * Could be implemented outside Thm as:                                      *
 *   fun Mk_tycomb th =                                                      *
 *     let val {Rator,Rand} = dest_tycomb(rhs (concl th))                    *
 *         fun mka th1 th2 = TRANS th (MK_COMB(th1,th2)) in                  *
 *     (REFL Rator, REFL Rand, mka)                                          *
 *     end                                                                   *
 *---------------------------------------------------------------------------*)

fun Mk_tycomb thm =
   let val (lhs, rhs, ty) = Term.dest_eq_ty (concl thm)
       val (Rator,Rand) = dest_tycomb rhs
       fun mkthm th1' =
         let val (lhs1, rhs1, ty1) = Term.dest_eq_ty (concl th1')
             val _ = Assert (EQ(lhs1,Rator)) "" ""
             val (ocls,hyps) = tag_hyp_union [thm, th1']
         in make_thm Count.TyComb
	   (ocls, hyps, mk_eq_nocheck ty lhs (mk_tycomb(rhs1,Rand)))
         end
	 handle HOL_ERR _ => ERR "Mk_tycomb" "";
       val th1 = refl_nocheck (type_of Rator) Rator
   in (th1,Rand,mkthm)
   end
   handle HOL_ERR _ => ERR "Mk_tycomb" "";

(*---------------------------------------------------------------------------*
 *                        |- u = u    (th1)                                  *
 *         (thm)              ...                                            *
 *    A |- t = \:'a.u    A' |- u = u' (th1')                                 *
 *  ------------------------------------------ 'a not in FTV(A')             *
 *            A u A' |- t = \:'a.u'                                          *
 *                                                                           *
 * Could be implemented outside Thm as:                                      *
 *   fun Mk_tyabs th =                                                       *
 *     let val {Bvar,Body} = dest_tyabs(rhs (concl th)) in                   *
 *     (Bvar, REFL Body, (fn th1 => TRANS th (TY_ABS Bvar th1)))             *
 *     end                                                                   *
 *---------------------------------------------------------------------------*)

fun Mk_tyabs thm =
   let val (lhs, rhs, ty) = Term.dest_eq_ty (concl thm)
       val (Bvar,Body) = dest_tyabs rhs
       fun mkthm th1' =
         let val (lhs1, rhs1, _) = Term.dest_eq_ty (concl th1')
             val _ = Assert (EQ(lhs1,Body)) "" ""
             val _ = Assert (not (type_var_occursl Bvar (hypset th1'))) "" ""
             val (ocls,hyps) = tag_hyp_union [thm, th1']
         in make_thm Count.TyAbs
	   (ocls, hyps, mk_eq_nocheck ty lhs (mk_tyabs(Bvar, rhs1)))
         end
	 handle HOL_ERR _ => ERR "Mk_tyabs" ""
       val (_,bty) = Type.dest_univ_type ty
       val th1 = refl_nocheck bty Body
   in (Bvar,th1,mkthm)
   end
   handle HOL_ERR _ => ERR "Mk_tyabs" "";


(*---------------------------------------------------------------------------*
 * Same as SPEC, but without propagating the substitution.  Spec = SPEC.     *
 *---------------------------------------------------------------------------*)

fun Specialize t th =
   let val (Rator,Rand) = dest_comb(concl th)
       val {Name,Thy,...} = dest_thy_const Rator
   in
     Assert (Thy="bool" andalso Name="!") "" "";
     make_thm Count.Spec
        (tag th, hypset th, Term.lazy_beta_conv(mk_comb(Rand,t)))
   end
   handle HOL_ERR _ => ERR "Specialize" "";

(*---------------------------------------------------------------------------*
 * Construct a theorem directly and attach the given tag to it.              *
 *---------------------------------------------------------------------------*)

fun mk_oracle_thm tg (asl,c) =
  (Assert (Lib.all is_bool (c::asl)) "mk_oracle_thm"  "not a proposition"
   ; Assert (tg <> "DISK_THM") "mk_oracle_thm"  "invalid user tag"
   ; make_thm Count.Oracle (Tag.read tg,list_hyp asl,c));


val mk_thm = mk_oracle_thm "MK_THM"

fun add_tag (tag1, THM(tag2, h,c)) = THM(Tag.merge tag1 tag2, h, c)

(*---------------------------------------------------------------------------*
 *    The following two are only used in Theory, and are not                 *
 *     externally available.                                                 *
 *---------------------------------------------------------------------------*)

fun mk_axiom_thm (r,c) =
   (Assert (type_of c = bool) "mk_axiom_thm"  "Not a proposition!";
    make_thm Count.Axiom (Tag.ax_tag r, empty_hyp, c))

fun mk_defn_thm (witness_tag, c) =
   (Assert (type_of c = bool) "mk_defn_thm"  "Not a proposition!";
    make_thm Count.Definition (witness_tag,empty_hyp,c))


local open Type in
fun debug_type ty =
    case ty of TyBv i => print ("TyBv"^Int.toString i)
             | _      =>
    if is_vartype ty then let
        val (s,kd,rk) = dest_var_type ty
      in print s
      end 
    else if is_bvartype ty then let
      in print "<bound type var>"
      end
    else if (can dom_rng ty) then let
        val (dty,rty) = dom_rng ty
      in print "("; debug_type dty; print " -> "; debug_type rty; print ")"
      end
    else if is_con_type ty then let
        val {Tyop,Thy,Kind,Rank} = dest_thy_con_type ty
      in print Tyop
      end
    else if is_app_type ty then let
        val (f,a) = dest_app_type ty
      in print "("; debug_type a; print " ";
         debug_type f; print ")"
      end
    else if is_abs_type ty then let
        val (v,b) = dest_abs_type ty
      in print "(\\"; debug_type v; print ". ";
         debug_type b; print ")"
      end
    else if is_univ_type ty then let
        val (v,b) = dest_univ_type ty
      in print "(!"; debug_type v; print ". ";
         debug_type b; print ")"
      end
    else print "debug_type: unrecognized type"
end

local open Term in
fun debug_term tm =
    case tm of Bv i => print ("Bv"^Int.toString i)
             | _    =>
    if is_var tm then let
        val (s,ty) = dest_var tm
      in print s
      end
    else if is_const tm then let
        val (s,ty) = dest_const tm
      in print s
      end
    else if is_comb tm then let
        val (f,a) = dest_comb tm
      in print "("; debug_term f; print " ";
         debug_term a; print ")"
      end
    else if is_abs tm then let
        val (v,b) = dest_abs tm
      in print "(\\"; debug_term v; print ". ";
         debug_term b; print ")"
      end
    else if is_tycomb tm then let
        val (f,a) = dest_tycomb tm
      in print "("; debug_term f; print " ";
         print "[:"; debug_type a;
         print ":]"; print ")"
      end
    else if is_tyabs tm then let
        val (v,b) = dest_tyabs tm
      in print "(\\:";
         debug_type v; print ". ";
         debug_term b; print ")"
      end
    else print "debug_term: unrecognized term"
end


(*---------------------------------------------------------------------------*
 * Fetching theorems from disk. The following parses the "raw" term          *
 * representation found in exported theory files.                            *
 *---------------------------------------------------------------------------*)

datatype lexeme
   = dot
   | lamb
   | tylamb
   | exclam
   | lparen
   | rparen
   | tyapp
   | var
   | const
   | pconst
   | ident of int
   | bvar  of int
   | name  of string;

local val numeric = Char.contains "0123456789"
in
fun take_numb ss0 =
  let val (ns, ss1) = Substring.splitl numeric ss0
  in case Int.fromString (Substring.string ns)
      of SOME i => (i,ss1)
       | NONE   => ERR "take_numb" ""
  end
end;

local fun is_quote c = (c <> #"\"")
in
fun take_name ss0 =
  let val (ns, ss1) = Substring.splitl is_quote ss0
      val ss2 = Substring.triml 1 ss1
  in (Substring.string ns, ss2)
  end
end;


(* don't allow numbers to be split across fragments *)

fun lexer (ss1,qs1) =
  case Substring.getc (Lib.deinitcommentss ss1)
                      (* was: (Substring.dropl Char.isSpace ss1) *)
   of NONE => (case qs1
                of (QUOTE s::qs2) => lexer (Substring.full s,qs2)
                 | []             => NONE
                 | _              => ERR "raw lexer" "expected a quotation")
    | SOME (c,ss2) =>
       case c
        of #"."  => SOME(dot,   (ss2,qs1))
         | #"\\" => SOME(lamb,  (ss2,qs1))
         | #"/"  => SOME(tylamb,(ss2,qs1))
         | #"!"  => SOME(exclam,(ss2,qs1))
         | #"("  => SOME(lparen,(ss2,qs1))
         | #")"  => SOME(rparen,(ss2,qs1))
         | #":"  => SOME(tyapp, (ss2,qs1))
         | #"@"  => SOME(var,   (ss2,qs1))
         | #"-"  => SOME(const, (ss2,qs1))
         | #"="  => SOME(pconst,(ss2,qs1))
         | #"%"  => let val (n,ss3) = take_numb ss2 in SOME(ident n, (ss3,qs1)) end
         | #"$"  => let val (n,ss3) = take_numb ss2 in SOME(bvar n,  (ss3,qs1)) end
         | #"\"" => let val (n,ss3) = take_name ss2 in SOME(name n,  (ss3,qs1)) end
         |   _   => ERR "raw lexer" "bad character";

fun eat_rparen ss =
  case lexer ss
   of SOME (rparen, ss') => ss'
    |   _ => ERR "eat_rparen" "expected right parenthesis";

fun eat_dot ss =
  case lexer ss
   of SOME (dot, ss') => ss'
    |   _ => ERR "eat_dot" "expected a \".\"";

datatype stackitem = Tm of term | Ty of hol_type

fun parse_raw tytable table =
 let fun tyindex i = Vector.sub(tytable,i)
     fun index i = Vector.sub(table,i)
     fun tmof (Tm tm) = tm
       | tmof (Ty _ ) = raise ERR "tmof" "not a term"
     fun tyof (Ty ty) = ty
       | tyof (Tm _ ) = raise ERR "tyof" "not a type"
     val tvof = Type.dest_var_type
     fun parsety (stk,ss) =
      case lexer ss
       of SOME (bvar n,  rst) => (Ty(TyBv n)::stk,rst)
        | SOME (ident n, rst) => (Ty(tyindex n)::stk,rst)
        | SOME (lparen,  rst) =>
           (case lexer rst
             of SOME (lamb,   rst') => glambty (stk,rst')
              | SOME (exclam, rst') => gallty  (stk,rst')
              |    _                => parsetyl (parsety (stk,rst)))
        |  _ => (stk,ss)
     and
     parsetyl (stk,ss) =
        case parsety (stk,ss)
         of (h1::h2::t, ss') => (Ty(TyApp(tyof h1,tyof h2))::t, eat_rparen ss')
          |   _              => ERR "raw.parsetyl" "impossible"
     and
     glambty (stk,ss) =
      case lexer ss
       of SOME (ident n, rst) =>
            (case parsety (stk, eat_dot rst)
              of (h::t,rst1) => (Ty(TyAbs(tvof(tyindex n),tyof h))::t, eat_rparen rst1)
               |   _         => ERR "glambty" "impossible")
        | _ => ERR "glambty" "expected an identifier"
     and
     gallty (stk,ss) =
      case lexer ss
       of SOME (ident n, rst) =>
            (case parsety (stk, eat_dot rst)
              of (h::t,rst1) => (Ty(TyAll(tvof(tyindex n),tyof h))::t, eat_rparen rst1)
               |   _         => ERR "gallty" "impossible")
        | _ => ERR "gallty" "expected an identifier"
     fun parse (stk,ss) =
      case lexer ss
       of SOME (bvar n,  rst) => (Tm(Bv n)::stk,rst)
        | SOME (ident n, rst) => (Tm(index n)::stk,rst)
        | SOME (lparen,  rst) =>
           (case lexer rst
             of SOME (lamb,   rst') => glamb (stk,rst')
              | SOME (tylamb, rst') => gtylamb (stk,rst')
              | SOME (var,    rst') => gvar (stk,rst')
              | SOME (const,  rst') => gconst false (stk,rst')
              | SOME (pconst, rst') => gconst true  (stk,rst')
              | SOME (tyapp,  rst') => gtyapp (parse (stk,rst'))
              |    _                => parsel (parse (stk,rst)))
        |  _ => (stk,ss)
     and
     parsel (stk,ss) =
        case parse (stk,ss)
         of (h1::h2::t, ss') => (Tm(Comb(tmof h2,tmof h1))::t, eat_rparen ss')
          |   _              => ERR "raw.parsel" "impossible"
     and
     gvar (stk,ss) =
        case lexer ss
         of SOME (name n, rst) =>
              (case parsety (stk, rst)
                of (h::t,rst1) => (Tm(Fv(n,tyof h))::t, eat_rparen rst1)
                 |   _         => ERR "gvar" "impossible")
          | _ => ERR "gvar" "expected a name"
     and
     gconst poly (stk,ss) =
        case lexer ss
         of SOME (name n, rst) =>
              (case lexer rst
                of SOME (name thy, rst1) =>
                     (case parsety (stk, rst1)
                       of (h::t,rst2) => let val ty = tyof h
                                             val ty' = if poly then POLY ty else GRND ty
                                             val id = case prim_mk_const{Name=n,Thy=thy}
                                                       of Const(id,_) => id
                                                        | _ => ERR "gconst" "impossible const"
                                         in (Tm(Const(id,ty'))::t, eat_rparen rst2)
                                         end
                        |   _         => ERR "gconst" "impossible")
                 |   _         => ERR "gconst" "expected a theory name")
          | _ => ERR "gconst" "expected a constant name"
     and
     gtyapp (stk,ss) =
        case parsety (stk,ss)
         of (h1::h2::t, ss') => (Tm(TComb(tmof h2,tyof h1))::t, eat_rparen ss')
          |   _              => ERR "raw.gtyapp" "impossible"
     and
     glamb (stk,ss) =
      case parse (stk, ss) (* parse the bound variable, push on stack *)
       of (stk1,rst) =>
            (case parse (stk1, eat_dot rst) (* parse the body *)
              of (h::v::t,rst1) => (Tm(Abs(tmof v,tmof h))::t, eat_rparen rst1)
               |   _            => ERR "glamb" "impossible")
     and
     gtylamb (stk,ss) =
      case lexer ss
       of SOME (ident n, rst) =>
            (case parse (stk, eat_dot rst)
              of (h::t,rst1) => (Tm(TAbs(tvof(tyindex n),tmof h))::t, eat_rparen rst1)
               |   _         => ERR "gtylamb" "impossible")
        | _ => ERR "gtylamb" "expected an identifier"
 in
  fn (QUOTE s::qs) =>
       (case parse ([], (Substring.full s,qs))
         of ([Tm v], _)  => v
          | otherwise => ERR "raw term parser" "parse failed")
   | otherwise => ERR "raw term parser" "expected a quotation"
 end;

local val mk_disk_thm = make_thm Count.Disk
in
fun disk_thm tyvect vect =
  let val rtp = parse_raw tyvect vect
  in fn (s,asl,w) =>
        mk_disk_thm(Tag.read_disk_tag s,list_hyp (map rtp asl),rtp w)
  end
end;

end (* Thm *)
