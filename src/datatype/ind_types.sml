(* ========================================================================= *)
(* Inductive (or free recursive) types.                                      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(* ========================================================================= *)

(* ported from Caml Light source by Michael Norrish, November 1999           *)

(* app load ["HOLSimps", "Q", "numLib", "IndDefLib", "tautLib"] *)

open HolKernel basicHol90Lib Parse Psyntax
open numTheory arithmeticTheory prim_recTheory simpLib boolSimps
open jrh_simplelib ind_typeTheory

infix F_F THEN THENC THENL |-> ORELSEC

(* ------------------------------------------------------------------------- *)
(* Handy utility to produce "SUC o SUC o SUC ..." form of numeral.           *)
(* ------------------------------------------------------------------------- *)

val (Type,Term) = parse_from_grammars arithmeticTheory.arithmetic_grammars
fun -- q x = Term q
fun == q x = Type q

val sucivate = let
  val zero = Term`0` and suc = Term`SUC`
in
  fn n => funpow n (curry mk_comb suc) zero
end

(* ------------------------------------------------------------------------- *)
(* Eliminate local "definitions" in hyps.                                    *)
(* ------------------------------------------------------------------------- *)

fun SCRUB_EQUATION eq th = let
  val (l,r) = dest_eq eq
in
  MP (Rsyntax.INST [l |-> r] (DISCH eq th)) (REFL r)
end

(* ------------------------------------------------------------------------- *)
(* Proves existence of model (inductively); use pseudo-constructors.         *)
(*                                                                           *)
(* Returns suitable definitions of constructors in terms of CONSTR, and the  *)
(* rule and induction theorems from the inductive relation package.          *)
(* ------------------------------------------------------------------------- *)


val justify_inductive_type_model = let
  val aty = Type.alpha
  val T_tm = Term`T` and n_tm = Term`n:num` and beps_tm = Term`@x:bool. T`
  fun munion s1 s2 =
    if s1 = [] then s2
    else let
      val h1 = hd s1
      and s1' = tl s1
    in
      let
        val (_,s2') = Lib.pluck (fn h2 => h2 = h1) s2
      in
         h1::(munion s1' s2')
      end handle HOL_ERR _ => h1::(munion s1' s2)
    end
in
  fn def => let
    val (newtys,rights) = unzip def
    val tyargls = itlist (curry op@ o map snd) rights []
    val alltys = itlist (munion o C set_diff newtys) tyargls []
    val epstms = map (fn ty => mk_select(mk_var("v",ty),T_tm)) alltys
    val pty =
      end_itlist (fn ty1 => fn ty2 => mk_type("prod",[ty1,ty2])) alltys
      handle HOL_ERR _ => Type.bool
    val recty = mk_type("recspace",[pty])
    val constr = mk_const("CONSTR",[aty |-> pty])
    val fcons = mk_const("FCONS",[aty |-> recty])
    val bot = mk_const("BOTTOM",[aty |-> pty])
    val  bottail = mk_abs(n_tm,bot)
    fun mk_constructor n (cname,cargs) = let
      val ttys = map (fn ty => if mem ty newtys then recty else ty) cargs
      val args = make_args "a" [] ttys
      val (rargs,iargs) = partition (fn t => type_of t = recty) args
      fun mk_injector epstms alltys iargs =
        if alltys = [] then []
        else let
          val ty = hd alltys
        in
          let
            val (a,iargs') = Lib.pluck (fn t => type_of t = ty) iargs
          in
            a::(mk_injector (tl epstms) (tl alltys) iargs')
          end handle HOL_ERR _ =>
            (hd epstms)::(mk_injector (tl epstms) (tl alltys) iargs)
        end
      val iarg =
        end_itlist (curry mk_pair) (mk_injector epstms alltys iargs)
        handle HOL_ERR _ => beps_tm
      val rarg = itlist (mk_binop fcons) rargs bottail
      val conty = itlist (curry Type.-->) (map type_of args) recty
      val condef = list_mk_comb(constr,[sucivate n, iarg, rarg])
    in
      mk_eq(mk_var(cname,conty),list_mk_abs(args,condef))
    end
    fun mk_constructors n rights =
      if rights = [] then []
      else
        (mk_constructor n (hd rights))::(mk_constructors (n + 1) (tl rights))
    val condefs = mk_constructors 0 (itlist (curry op@) rights [])
    val conths = map ASSUME condefs
    val predty = Type.-->(recty, Type.bool)
    val rels = map (fn s => mk_var(dest_vartype s,predty)) newtys
    val edefs =
      itlist (fn (x,l) => fn acc => map (fn t => (x,t)) l @ acc) def []
    val idefs =
      map2 (fn (r,(_,atys)) => fn def => ((r,atys),def)) edefs condefs
    fun mk_rule ((r,a),condef) = let
      val (left,right) = dest_eq condef
      val (args,bod) = strip_abs right
      val lapp = list_mk_comb(left,args)
      val  conds = itlist2
        (fn arg => fn argty => fn sofar =>
         if mem argty newtys then
           mk_comb(mk_var(dest_vartype argty,predty),arg)::sofar
         else sofar) args a []
      val conc = mk_comb(mk_var(dest_vartype r,predty),lapp)
      val rule = if conds = [] then conc
                 else mk_imp(list_mk_conj conds,conc)
    in
      list_mk_forall(args,rule)
    end
    val rules = list_mk_conj (map mk_rule idefs)
    val th0 =
      IndDefLib.derive_nonschematic_inductive_relations rules
    val th1 = IndDefLib.prove_monotonicity_hyps IndDefLib.bool_monoset th0
    val (th2a,th2bc) = CONJ_PAIR th1
    val th2b = CONJUNCT1 th2bc
  in
    (conths,th2a,th2b)
  end
end

(* ------------------------------------------------------------------------- *)
(* Shows that the predicates defined by the rules are all nonempty.          *)
(* (This could be done much more efficiently/cleverly, but it's OK.)         *)
(* ------------------------------------------------------------------------- *)


fun prove_model_inhabitation rth = let
  val srules = map SPEC_ALL (CONJUNCTS rth)
  val (imps,bases) = partition (is_imp o concl) srules
  val concs = map concl bases @ map (rand o concl) imps
  val preds = mk_set (map (repeat rator) concs)
  fun exhaust_inhabitations ths sofar = let
    val dunnit = mk_set(map (fst o strip_comb o concl) sofar)
    val useful = filter
      (fn th => not (mem (fst(strip_comb(rand(concl th)))) dunnit)) ths
  in
    if null useful then sofar
    else let
      fun follow_horn thm = let
        val preds = map (fst o strip_comb) (strip_conj(lhand(concl thm)))
        val asms =
          map (fn p =>
               valOf (List.find (fn th =>
                                 fst(strip_comb(concl th)) = p) sofar))
          preds
      in
        MATCH_MP thm (end_itlist CONJ asms)
      end
      val newth = tryfind follow_horn useful
    in
      exhaust_inhabitations ths (newth::sofar)
    end
  end
  val ithms = exhaust_inhabitations imps bases
  val exths = map
    (fn p => valOf (List.find (fn th => fst(strip_comb(concl th)) = p) ithms))
    preds
in
  exths
end

(* ------------------------------------------------------------------------- *)
(* Makes a type definition for one of the defined subsets.                   *)
(* ------------------------------------------------------------------------- *)

fun define_inductive_type cdefs exth = let
  val extm = concl exth
  val epred = fst(strip_comb extm)
  val ename = String.extract(fst(dest_var epred), 1, NONE)
  val th1 = ASSUME (valOf (List.find (fn eq => lhand eq = epred) (hyp exth)))
  val th2 = TRANS th1 (SUBS_CONV cdefs (rand(concl th1)))
  val th3 = EQ_MP (AP_THM th2 (rand extm)) exth
  val th4 = itlist SCRUB_EQUATION (hyp th3) th3
  val mkname = "mk_"^ename and destname = "dest_"^ename
  val (bij1,bij2) = new_basic_type_definition ename (mkname,destname) th4
  val bij2a = AP_THM th2 (rand(rand(concl bij2)))
  val bij2b = TRANS bij2a bij2
in
  (bij1,bij2b)
end

(* ------------------------------------------------------------------------- *)
(* Defines a type constructor corresponding to current pseudo-constructor.   *)
(* ------------------------------------------------------------------------- *)


fun define_inductive_type_constructor defs consindex th = let
  val (avs,bod) = strip_forall(concl th)
  val (asms,conc) =
    if is_imp bod then (strip_conj(lhand bod),rand bod) else ([],bod)
  val asmlist = map dest_comb asms
  val (cpred,cterm) = dest_comb conc
  val (oldcon,oldargs) = strip_comb cterm
  fun modify_arg v = let
    val dest = snd(assoc (rev_assoc v asmlist) consindex)
    val ty' = hd(snd(dest_type(type_of dest)))
    val v' = mk_var(fst(dest_var v),ty')
  in
    (mk_comb(dest,v'),v')
  end handle HOL_ERR _ => (v,v)
  val (newrights,newargs) = unzip(map modify_arg oldargs)
  val retmk = fst(assoc cpred consindex)
  val defbod = mk_comb(retmk,list_mk_comb(oldcon,newrights))
  val defrt = list_mk_abs(newargs,defbod)
  val expth = valOf (List.find (fn th => lhand(concl th) = oldcon) defs)
  val rexpth = SUBS_CONV [expth] defrt
  val deflf = mk_var(fst(dest_var oldcon),type_of defrt)
  val defth = new_definition(fst (dest_var oldcon) ^ "_def",
                             mk_eq(deflf,rand(concl rexpth)))
in
  TRANS defth (SYM rexpth)
end

(* ------------------------------------------------------------------------- *)
(* Instantiate the induction theorem on the representatives to transfer      *)
(* it to the new type(s). Uses "\x. rep-pred(x) /\ P(mk x)" for "P".         *)
(* ------------------------------------------------------------------------- *)

fun instantiate_induction_theorem consindex ith = let
  val (avs,bod) = strip_forall(concl ith)
  val corlist =
    map((repeat rator F_F repeat rator) o dest_imp o body o rand)
    (strip_conj(rand bod))
  val consindex' =
    map (fn v => let val w = rev_assoc v corlist in (w,assoc w consindex) end)
    avs
  val recty = (hd o snd o dest_type o type_of o fst o snd o hd) consindex
  val newtys = map (hd o snd o dest_type o type_of o snd o snd) consindex'
  val ptypes = map (C mk_fun_ty Type.bool) newtys
  val preds = make_args "P" [] ptypes
  val args = make_args "x" [] (map (K recty) preds)
  val lambs = map2 (fn (r,(m,d)) => fn (p,a) =>
                     mk_abs(a,mk_conj(mk_comb(r,a),mk_comb(p,mk_comb(m,a)))))
                   consindex' (zip preds args)
in
  SPECL lambs ith
end

(* ------------------------------------------------------------------------- *)
(* Reduce a single clause of the postulated induction theorem (old_ver) back *)
(* to the kind wanted for the new type (new_ver); |- new_ver ==> old_ver     *)
(* ------------------------------------------------------------------------- *)

fun pullback_induction_clause tybijpairs conthms = let
  val PRERULE =
    GEN_REWRITE_RULE (funpow 3 RAND_CONV) (map SYM conthms)
  val IPRULE =
    SYM o GEN_REWRITE_RULE I (map snd tybijpairs)
in
  fn rthm => fn tm => let
    val (avs,bimp) = strip_forall tm
  in
    if is_imp bimp then let
      val (ant,con) = dest_imp bimp
      val ths = map (CONV_RULE BETA_CONV) (CONJUNCTS (ASSUME ant))
      val (tths,pths) = unzip (map CONJ_PAIR ths)
      val tth = MATCH_MP (SPEC_ALL rthm) (end_itlist CONJ tths)
      val mths = map IPRULE (tth::tths)
      val conth1 = BETA_CONV con
      val contm1 = rand(concl conth1)
      val conth2 = TRANS conth1
        (AP_TERM (rator contm1) (SUBS_CONV (tl mths) (rand contm1)))
      val conth3 = PRERULE conth2
      val lctms = map concl pths
      val asmin = mk_imp(list_mk_conj lctms,rand(rand(concl conth3)))
      val argsin = map rand (strip_conj(lhand asmin))
      val argsgen =
        map (fn tm => mk_var(fst(dest_var(rand tm)),type_of tm)) argsin
      val asmgen =
        Term.subst (map2 (fn l => fn r => (l |-> r)) argsin argsgen) asmin
      val asmquant =
        list_mk_forall(snd(strip_comb(rand(rand asmgen))),asmgen)
      val th1 =
        Rsyntax.INST (map2 (curry op |->) argsgen argsin)
        (SPEC_ALL (ASSUME asmquant))
      val th2 = MP th1 (end_itlist CONJ pths)
      val th3 = EQ_MP (SYM conth3) (CONJ tth th2)
    in
      DISCH asmquant (GENL avs (DISCH ant th3))
    end
    else let
      val con = bimp
      val conth2 = BETA_CONV con
      val tth = Ho_match.PART_MATCH I rthm (lhand(rand(concl conth2)))
      val conth3 = PRERULE conth2
      val asmgen = rand(rand(concl conth3))
      val asmquant = list_mk_forall(snd(strip_comb(rand asmgen)),asmgen)
      val th2 = SPEC_ALL (ASSUME asmquant)
      val th3 = EQ_MP (SYM conth3) (CONJ tth th2)
    in
      DISCH asmquant (GENL avs th3)
    end
  end
end

(* ------------------------------------------------------------------------- *)
(* Finish off a consequence of the induction theorem.                        *)
(* ------------------------------------------------------------------------- *)


fun finish_induction_conclusion consindex tybijpairs = let
  val (tybij1,tybij2) = unzip tybijpairs
  val PRERULE =
    GEN_REWRITE_RULE (LAND_CONV o LAND_CONV o RAND_CONV) tybij1 o
    GEN_REWRITE_RULE LAND_CONV tybij2
  and FINRULE = GEN_REWRITE_RULE RAND_CONV tybij1
in
  fn th => let
    val (av,bimp) = dest_forall(concl th)
    val pv = lhand(body(rator(rand bimp)))
    val (p,v) = dest_comb pv
    val (mk,dest) = assoc p consindex
    val ty = hd(snd(dest_type(type_of dest)))
    val v' = mk_var(fst(dest_var v),ty)
    val dv = mk_comb(dest,v')
    val th1 = PRERULE (SPEC dv th)
    val th2 = MP th1 (REFL (rand(lhand(concl th1))))
    val th3 = CONV_RULE BETA_CONV th2
  in
    GEN v' (FINRULE (CONJUNCT2 th3))
  end
end;

(* ------------------------------------------------------------------------- *)
(* Derive the induction theorem.                                             *)
(* ------------------------------------------------------------------------- *)

val conjuncts = strip_conj

fun derive_induction_theorem consindex tybijpairs conthms iith rth = let
  val bths = map2
    (pullback_induction_clause tybijpairs conthms)
    (CONJUNCTS rth) (conjuncts(lhand(concl iith)))
  val asm = list_mk_conj(map (lhand o concl) bths)
  val ths = map2 MP bths (CONJUNCTS (ASSUME asm))
  val th1 = MP iith (end_itlist CONJ ths)
  val th2 = end_itlist CONJ (map
    (finish_induction_conclusion consindex tybijpairs) (CONJUNCTS th1))
  val th3 = DISCH asm th2
  val preds = map (rator o body o rand) (conjuncts(rand(concl th3)))
  val th4 = GENL preds th3
  val pasms = filter (C mem (map fst consindex) o lhand) (hyp th4)
  val th5 = itlist DISCH pasms th4
  val th6 = itlist SCRUB_EQUATION (hyp th5) th5
  val th7 = UNDISCH_ALL th6
in
  itlist SCRUB_EQUATION (hyp th7) th7
end

(* ------------------------------------------------------------------------- *)
(* Create the recursive functions and eliminate pseudo-constructors.         *)
(* (These are kept just long enough to derive the key property.)             *)
(* ------------------------------------------------------------------------- *)


fun create_recursive_functions tybijpairs consindex conthms rth = let
  val domtys = map (hd o snd o dest_type o type_of o snd o snd) consindex
  val recty = (hd o snd o dest_type o type_of o fst o snd o hd) consindex
  val ranty = mk_vartype "'Z"
  val fnn = mk_var("fn",mk_fun_ty recty ranty)
  and fns = make_args "fn" [] (map (C mk_fun_ty ranty) domtys)
  val args = make_args "a" [] domtys
  val rights =
    map2 (fn (_,(_,d)) => fn a =>
          mk_abs(a,mk_comb(fnn,mk_comb(d,a))))
    consindex args
  val eqs = map2 (curry mk_eq) fns rights
  val fdefs = map ASSUME eqs
  val fxths1 =
    map (fn th1 => tryfind (fn th2 => MK_COMB(th2,th1)) fdefs)
    conthms
  val fxths2 = map (fn th => TRANS th (BETA_CONV (rand(concl th)))) fxths1
  fun mk_tybijcons (th1,th2) = let
    val th3 =
      Rsyntax.INST [rand(lhand(concl th2)) |-> rand(lhand(concl th1))] th2
    val th4 = AP_TERM (rator(lhand(rand(concl th2)))) th1
  in
    EQ_MP (SYM th3) th4
  end
  val SCONV = GEN_REWRITE_CONV I (map mk_tybijcons tybijpairs)
  and ERULE = GEN_REWRITE_RULE I (map snd tybijpairs)
  fun simplify_fxthm rthm fxth = let
    val pat = funpow 4 rand (concl fxth)
  in
    if is_imp(repeat (snd o dest_forall) (concl rthm)) then let
      val th1 = PART_MATCH (rand o rand) rthm pat
      val tms1 = conjuncts(lhand(concl th1))
      val ths2 = map (fn t => EQ_MP (SYM(SCONV t)) TRUTH) tms1
    in
      ERULE (MP th1 (end_itlist CONJ ths2))
    end
    else
      ERULE (PART_MATCH rand rthm pat)
  end
  val fxths3 = map2 simplify_fxthm (CONJUNCTS rth) fxths2
  val fxths4 = map2 (fn th1 => TRANS th1 o AP_TERM fnn) fxths2 fxths3
  fun cleanup_fxthm cth fxth = let
    val tms = snd(strip_comb(rand(rand(concl fxth))))
    val kth = RIGHT_BETAS tms (ASSUME (hd(hyp cth)))
  in
    TRANS fxth (AP_TERM fnn kth)
  end
  val fxth5 = end_itlist CONJ (map2 cleanup_fxthm conthms fxths4)
  val pasms = filter (C mem (map fst consindex) o lhand) (hyp fxth5)
  val fxth6 = itlist DISCH pasms fxth5
  val fxth7 =
    itlist SCRUB_EQUATION (itlist (union o hyp) conthms []) fxth6
  val fxth8 = UNDISCH_ALL fxth7
in
  itlist SCRUB_EQUATION (subtract (hyp fxth8) eqs) fxth8
end

(* ------------------------------------------------------------------------- *)
(* Create a function for recursion clause.                                   *)
(* ------------------------------------------------------------------------- *)

fun SUBS ths = CONV_RULE (SUBS_CONV ths)
fun upto n = let
  fun down l n = if n < 0 then l else down (n::l) (n - 1)
in
  down [] n
end
local
  val s = Term`s:num->'Z`
  val zty = Type`:'Z`
  val numty = Type`:num`
  fun extract_arg tup v =
    if v = tup then REFL tup
    else let
      val (t1,t2) = dest_pair tup
      val PAIR_th = ISPECL [t1,t2] (if free_in v t1 then pairTheory.FST
                                    else pairTheory.SND)
      val tup' = rand(concl PAIR_th)
    in
      if tup' = v then PAIR_th
      else let
        val th = extract_arg (rand(concl PAIR_th)) v
      in
        SUBS[SYM PAIR_th] th
      end
    end
in
  fun create_recursion_iso_constructor consindex = let
    val recty = hd(snd(dest_type(type_of(fst(hd consindex)))))
    val domty = hd(snd(dest_type recty))
    val i = mk_var("i",domty)
    and r = mk_var("r",mk_fun_ty numty recty)
    val mks = map (fst o snd) consindex
    val mkindex = map (fn t => (hd(tl(snd(dest_type(type_of t)))),t)) mks
  in
    fn cth => let
      val artms = snd(strip_comb(rand(rand(concl cth))))
      val artys = mapfilter (type_of o rand) artms
      val (args,bod) = strip_abs(rand(hd(hyp cth)))
      val (ccitm,rtm) = dest_comb bod
      val (cctm,itm) = dest_comb ccitm
      val (rargs,iargs) = partition (C free_in rtm) args
      val xths = map (extract_arg itm) iargs
      val cargs' = map (Rsyntax.subst [itm |-> i] o lhand o concl) xths
      val indices = map sucivate (upto (length rargs - 1))
      val rindexed = map (curry mk_comb r) indices
      val rargs' =
        map2 (fn a => fn rx => mk_comb(assoc a mkindex,rx))
        artys rindexed
      val sargs' = map (curry mk_comb s) indices
      val allargs = cargs'@ rargs' @ sargs'
      val funty = itlist (mk_fun_ty o type_of) allargs zty
      val funname = fst(dest_const(repeat rator (lhand(concl cth))))^"'"
      val funarg = mk_var(funname,funty)
    in
      list_mk_abs([i,r,s],list_mk_comb(funarg,allargs))
    end
  end
end

(* ------------------------------------------------------------------------- *)
(* Derive the recursion theorem.                                             *)
(* ------------------------------------------------------------------------- *)

val EXISTS_EQUATION =
    let val pth = prove
     (--`!P t. (!x:'a. (x = t) ==> P x) ==> $? P`--,
      REPEAT GEN_TAC THEN DISCH_TAC THEN
      SUBST1_TAC(SYM (ETA_CONV (--`\x. (P:'a->bool) x`--))) THEN
      EXISTS_TAC (--`t:'a`--) THEN FIRST_ASSUM MATCH_MP_TAC THEN REFL_TAC)
    in fn tm => fn th =>
        let val (l,r) = dest_eq tm
            val P = mk_abs(l,concl th)
            val th1 = BETA_CONV(mk_comb(P,l))
            val th2 = ISPECL [P, r] pth
            val th3 = EQ_MP (SYM th1) th
            val th4 = GEN l (DISCH tm th3)
        in MP th2 th4
        end
    end;

val bndvar = #Bvar o Term.dest_abs
local
  val CCONV = funpow 3 RATOR_CONV (REPEATC (GEN_REWRITE_CONV I [FCONS]))
in
  fun  derive_recursion_theorem tybijpairs consindex conthms rath = let
    val isocons = map (create_recursion_iso_constructor consindex) conthms
    val ty = type_of(hd isocons)
    val fcons = mk_const("FCONS",[Type.alpha |-> ty])
    and fnil = mk_const("FNIL",[Type.alpha |-> ty])
    val bigfun = itlist (mk_binop fcons) isocons fnil
    val eth = ISPEC bigfun CONSTR_REC
    val fnn = rator(rand(hd(conjuncts(concl rath))))
    val betm = let
      val (v,bod) = dest_abs(rand(concl eth))
    in
      Rsyntax.subst[v |-> fnn] bod
    end
    val LCONV = REWR_CONV (ASSUME betm)
    val fnths =
      map (fn t => RIGHT_BETAS [bndvar(rand t)] (ASSUME t)) (hyp rath)
    val SIMPER = SIMP_RULE bool_ss
      (map SYM fnths @ map fst tybijpairs @ [pairTheory.FST,
                                             pairTheory.SND, FCONS, BETA_THM])
    fun hackdown_rath th = let
      val (ltm,rtm) = dest_eq(concl th)
      val wargs = snd(strip_comb(rand ltm))
      val th1 = TRANS th (LCONV rtm)
      val th2 = TRANS th1 (CCONV (rand(concl th1)))
      val th3 = TRANS th2 (funpow 2 RATOR_CONV BETA_CONV (rand(concl th2)))
      val th4 = TRANS th3 (RATOR_CONV BETA_CONV (rand(concl th3)))
      val th5 = TRANS th4 (BETA_CONV (rand(concl th4)))
    in
      GENL wargs (SIMPER th5)
    end
    val rthm = end_itlist CONJ (map hackdown_rath (CONJUNCTS rath))
    val seqs = let
      val unseqs = filter is_eq (hyp rthm)
      val tys = map (hd o snd o dest_type o type_of o snd o snd) consindex
    in
      map (fn ty => valOf (List.find
        (fn t => hd(snd(dest_type(type_of(lhand t)))) = ty) unseqs)) tys
    end
    val rethm = itlist EXISTS_EQUATION seqs rthm
    val fethm = CHOOSE(fnn,eth) rethm
    val pcons =
      map (repeat rator o rand o repeat (snd o dest_forall))
      (conjuncts(concl rthm))
  in
    GENL pcons fethm
  end
end

(* ------------------------------------------------------------------------- *)
(* Basic function: returns induction and recursion separately. No parser.    *)
(* ------------------------------------------------------------------------- *)

fun define_type_raw def = let
  val (defs,rth,ith) = justify_inductive_type_model def
  val neths = prove_model_inhabitation rth
  val tybijpairs = map (define_inductive_type defs) neths
  val preds = map (repeat rator o concl) neths
  val mkdests =
    map
    (fn (th,_) =>
     let val tm = lhand(concl th) in (rator tm,rator(rand tm)) end)
    tybijpairs
  val consindex = zip preds mkdests
  val condefs = map (define_inductive_type_constructor defs consindex)
                    (CONJUNCTS rth)
  val conthms = map
    (fn th => let val args = fst(strip_abs(rand(concl th))) in
     RIGHT_BETAS args th end) condefs
  val iith = instantiate_induction_theorem consindex ith
  val fth = derive_induction_theorem consindex tybijpairs conthms iith rth
  val rath = create_recursive_functions tybijpairs consindex conthms rth
  val kth = derive_recursion_theorem tybijpairs consindex conthms rath
in
  (fth,kth)
end

(* Test the above with:

   val def = [(Type`:'foo`, [("C1", []), ("C2", [Type`:num`])])];
   define_type_raw def;

   val def = [(Type`:'bar`, [("D1", [Type`:num`]), ("D2", [Type`:'bar`])])]
   define_type_raw def;

   val def = [(Type`:'qux`, [("F1", []), ("F2", [Type`:'a`, Type`:'qux`])])];
   define_type_raw def;

   val def = [(Type`:'qwerty`, [("G1", [Type`:num`]),
                                ("G2", [Type`:'asdf`])]),
              (Type`:'asdf`,   [("H1", []), ("H2", [Type`:'qwerty`])])];

   Form of recursion equation is not quite what hol98 expects.  It doesn't
   use ?! and it puts the recursive calls last as arguments, not first.
   So, the list equivalent gets a theorem along the lines of:
      !nil cons.
         ?fn.
            (fn NIL = nil) /\ (!x xs. fn (CONS x xs) = cons x xs (fn xs))
   not,
      !nil cons.
          ?!fn.
            (fn NIL = nil) /\ (!x xs. fn (CONS x xs) = cons (fn xs) x xs)

*)

(* ------------------------------------------------------------------------- *)
(* Temporary non-mutual version, just to define sum type.                    *)
(* ------------------------------------------------------------------------- *)


val sum_tyinfo = valOf (TypeBase.read "sum")
val sum_INDUCT = TypeBase.induction_of sum_tyinfo
val sum_RECURSION = TypeBase.axiom_of sum_tyinfo

val OUTL = sumTheory.OUTL;
val OUTR = sumTheory.OUTR;

(* ------------------------------------------------------------------------- *)
(* Generalize the recursion theorem to multiple domain types.                *)
(* (We needed to use a single type to justify it via a proforma theorem.)    *)
(*                                                                           *)
(* NB! Before this is called nontrivially (i.e. more than one new type)      *)
(*     the type constructor ":sum", used internally, must have been defined. *)
(* ------------------------------------------------------------------------- *)

val generalize_recursion_theorem = let
  val ELIM_OUTCOMBS = GEN_REWRITE_RULE TOP_DEPTH_CONV [OUTL, OUTR]
  fun mk_sum tys = let
    val k = length tys
  in
    if k = 1 then hd tys
    else let
      val (tys1,tys2) = chop_list (k div 2) tys
    in
      mk_type("sum", [mk_sum tys1, mk_sum tys2])
    end
  end
  val mk_inls = let
    fun mk_inls ty =
      if is_vartype ty then [mk_var("x",ty)]
      else let
        val (_,[ty1,ty2]) = dest_type ty
        val inls1 = mk_inls ty1
        and inls2 = mk_inls ty2
        val inl = mk_const("INL",[(Type.alpha |-> ty1), (Type.beta |-> ty2)])
        and inr = mk_const("INR",[(Type.alpha |-> ty1), (Type.beta |-> ty2)])
      in
        map (curry mk_comb inl) inls1 @ map (curry mk_comb inr) inls2
      end
  in
    fn ty => let
      val bods = mk_inls ty
    in
      map (fn t => mk_abs(find_term is_var t,t)) bods
    end
  end
  val mk_outls = let
    fun mk_inls sof ty =
      if is_vartype ty then [sof]
      else let
        val (_,[ty1,ty2]) = dest_type ty
        val outl = mk_const("OUTL",[(Type.alpha |-> ty1), (Type.beta |-> ty2)])
        and outr = mk_const("OUTR",[(Type.alpha |-> ty1), (Type.beta |-> ty2)])
      in
        mk_inls (mk_comb(outl,sof)) ty1 @ mk_inls (mk_comb(outr,sof)) ty2
      end
  in
    fn ty => let
      val x = mk_var("x",ty)
    in
      map (curry mk_abs x) (mk_inls x ty)
    end
  end
  fun mk_newfun fnn outl = let
    val (s,ty) = dest_var fnn
    val dty = hd(snd(dest_type ty))
    val x = mk_var("x",dty)
    val (y,bod) = dest_abs outl
    val r = mk_abs(x,Rsyntax.subst[y |-> mk_comb(fnn,x)] bod)
    val l = mk_var(s,type_of r)
    val th1 = ASSUME (mk_eq(l,r))
  in
    RIGHT_BETAS [x] th1
  end
in
  fn th => let
    val (avs,ebod) = strip_forall(concl th)
    val (evs,bod) = strip_exists ebod
    val n = length evs
  in
    if n = 1 then th
    else let
      val tys =
        map (fn i => mk_vartype ("'Z"^Int.toString i)) (upto (n - 1))
      val sty = mk_sum tys
      val inls = mk_inls sty
      and outls = mk_outls sty
      val zty = type_of(rand(snd(strip_forall(hd(conjuncts bod)))))
      val ith = Thm.INST_TYPE [zty |-> sty] th
      val (avs,ebod) = strip_forall(concl ith)
      val (evs,bod) = strip_exists ebod
      val fns' = map2 mk_newfun evs outls
      val fnalist = zip evs (map (rator o lhs o concl) fns')
      and inlalist = zip evs inls
      and outlalist = zip evs outls
      fun hack_clause tm = let
        val (avs,bod) = strip_forall tm
        val (l,r) = dest_eq bod
        val (fnn,args) = strip_comb r
        val pargs = map
          (fn a => let
            val g = genvar(type_of a)
          in
            if is_var a then (g,g)
            else let
              val outl = assoc (rator a) outlalist
            in
              (mk_comb(outl,g),g)
            end
          end) args
        val (args',args'') = unzip pargs
        val inl = assoc (rator l) inlalist
        val rty = hd(snd(dest_type(type_of inl)))
        val nty = itlist (mk_fun_ty o type_of) args' rty
        val fn' = mk_var(fst(dest_var fnn),nty)
        val r' = list_mk_abs(args'',mk_comb(inl,list_mk_comb(fn',args')))
      in
        (r',fnn)
      end
      val defs = map hack_clause (conjuncts bod)
      val jth = BETA_RULE (SPECL (map fst defs) ith)
      val bth = ASSUME (snd(strip_exists(concl jth)))
      fun finish_clause th = let
        val (avs,bod) = strip_forall (concl th)
        val outl = assoc (rator (lhand bod)) outlalist
      in
        GENL avs (BETA_RULE (AP_TERM outl (SPECL avs th)))
      end
      val cth = end_itlist CONJ (map finish_clause (CONJUNCTS bth))
      val dth = ELIM_OUTCOMBS cth
      val eth = GEN_REWRITE_RULE ONCE_DEPTH_CONV (map SYM fns') dth
      val fth = itlist SIMPLE_EXISTS (map snd fnalist) eth
      val dtms = map (hd o hyp) fns'
      val gth =
        itlist (fn e => fn th => let
          val (l,r) = dest_eq e
        in
                MP (Thm.INST [l |-> r] (DISCH e th)) (REFL r)
        end) dtms fth
      val hth = PROVE_HYP jth (itlist SIMPLE_CHOOSE evs gth)
      val xvs =
        map (fst o strip_comb o rand o snd o strip_forall)
        (conjuncts(concl eth))
    in
      GENL xvs hth
    end
  end
end

fun define_type_mutual def = let
  val (ith,rth) = define_type_raw def
in
  (ith,generalize_recursion_theorem rth)
end

(* Test the above with:

   val def = [(Type`:'foo`, [("C1", []), ("C2", [Type`:num`])])];
   define_type_mutual def;

   val def = [(Type`:'bar`, [("D1", [Type`:num`]), ("D2", [Type`:'bar`])])];
   define_type_mutual def;

   val def = [(Type`:'qux`, [("F1", []), ("F2", [Type`:'a`, Type`:'qux`])])];
   define_type_mutual def;

   val def = [(Type`:'qwerty`, [("G1", [Type`:num`]),
                                ("G2", [Type`:'asdf`])]),
              (Type`:'asdf`,   [("H1", []), ("H2", [Type`:'qwerty`])])];
   define_type_mutual def;

   (* HOL Light equivalent *)
   let def =
     let q = mk_vartype("qwerty")
     and a = mk_vartype("asdf") in
     [(q, [("G1", [`:num`]); ("G2", [a])]); (a, [("H1", []); ("H2", [q])])];;
   define_type_mutual def;;



*)


(* ------------------------------------------------------------------------- *)
(* Now deal with nested recursion.                                           *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Convenient functions for manipulating types.                              *)
(* ------------------------------------------------------------------------- *)

val dest_fun_ty  = Type.dom_rng

fun occurs_in ty bigty =
  bigty = ty orelse
  (not (is_vartype bigty) andalso
   exists (occurs_in ty) (snd(dest_type bigty)))

fun tysubst alist ty =
  rev_assoc ty alist
  handle HOL_ERR _ =>
    if is_vartype ty then ty
    else let
      val (tycon,tyvars) = dest_type ty
    in
      mk_type(tycon,map (tysubst alist) tyvars)
    end

(* ------------------------------------------------------------------------- *)
(* Dispose of trivial antecedent.                                            *)
(* ------------------------------------------------------------------------- *)

val TRIV_ANTE_RULE = let
  fun TRIV_IMP_CONV tm = let
    val (avs,bod) = strip_forall tm
    val bth =
      if is_eq bod then REFL (rand bod)
      else let
        val (ant,con) = dest_imp bod
        val ith = SUBS_CONV (CONJUNCTS(ASSUME ant)) (lhs con)
      in
        DISCH ant ith
      end
  in
    GENL avs bth
  end
in
  fn th => let
    val tm = concl th
  in
    if is_imp tm then let
      val (ant,con) = dest_imp(concl th)
      val cjs = conjuncts ant
      val cths = map TRIV_IMP_CONV cjs
    in
      MP th (end_itlist CONJ cths)
    end
    else th
  end
end

(* ------------------------------------------------------------------------- *)
(* Lift type bijections to "arbitrary" (well, free rec or function) type.    *)
(* ------------------------------------------------------------------------- *)

val CONJ_ACI_CONV = EQT_ELIM o AC_CONV (CONJ_ASSOC, CONJ_COMM);
val ISO_EXPAND_CONV = PURE_ONCE_REWRITE_CONV[ISO];

fun lift_type_bijections iths cty = let
  val itys = map (hd o snd o dest_type o type_of o lhand o concl) iths
in
  assoc cty (zip itys iths)
  handle HOL_ERR _ =>
    if not (List.exists (C occurs_in cty) itys) then
      Thm.INST_TYPE [Type.alpha |-> cty] ISO_REFL
    else let
      val (tycon,isotys) = dest_type cty
    in
      if tycon = "fun" then
        MATCH_MP ISO_FUN
        (end_itlist CONJ (map (lift_type_bijections iths) isotys))
      else
        raise HOL_ERR
          {origin_function = "lift_type_bijections",
           origin_structure = "ind_types",
           message = ("Unexpected type operator \""^tycon^"\"")}
    end
end

(* ------------------------------------------------------------------------- *)
(* Prove isomorphism of nested types where former is the smaller.            *)
(* ------------------------------------------------------------------------- *)

val T_tm = Term.mk_const{Name = "T", Ty = Type.bool};

val DE_EXISTENTIALIZE_RULE = let
  val pth = prove(
    Term`$? P ==> (c:'a = $@ P) ==> P c`,
    CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX)))) THEN
    DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SELECT_AX THEN POP_ASSUM ACCEPT_TAC)
  val USE_PTH = MATCH_MP pth
  fun DE_EXISTENTIALIZE_RULE th =
    if not (is_exists(concl th)) then ([],th)
    else let
      val th1 = USE_PTH th
      val v1 = rand(rand(concl th1))
      val gv = genvar(type_of v1)
      val th2 = CONV_RULE BETA_CONV (UNDISCH (Thm.INST [v1 |-> gv] th1))
      val (vs,th3) = DE_EXISTENTIALIZE_RULE th2
    in
      (gv::vs,th3)
    end
in
  DE_EXISTENTIALIZE_RULE
end

val grab_type = type_of o rand o lhand o snd o strip_forall;;

fun clause_corresponds cl0 = let
  val (f0,ctm0) = dest_comb (lhs cl0)
  val c0 = fst(dest_const(fst(strip_comb ctm0)))
  val (dty0,rty0) = dest_fun_ty (type_of f0)
in
  fn cl1 => let
    val (f1,ctm1) = dest_comb (lhs cl1)
    val c1 = fst(dest_const(fst(strip_comb ctm1)))
    val (dty1,rty1) = dest_fun_ty (type_of f1)
  in
    (c0 = c1) andalso (dty0 = rty1) andalso (rty0 = dty1)
  end
end

fun jrh_inst_flip theta = map (fn (l,r) => r |-> l) theta
fun INSTANTIATE (tmsubst, tysubst) thm = INST tmsubst (INST_TYPE tysubst thm)

fun find P l =
  case List.find P l of
    NONE => raise HOL_ERR {origin_function = "find",
                           origin_structure = "ind_types",
                           message = "No element satisfying predicate"}
  | SOME x => x


fun prove_inductive_types_isomorphic n k (ith0,rth0) (ith1,rth1) = let
  val sth0 = SPEC_ALL rth0
  and sth1 = SPEC_ALL rth1
  val (pevs0,pbod0) = strip_exists (concl sth0)
  and (pevs1,pbod1) = strip_exists (concl sth1)
  val (pcjs0,qcjs0) = chop_list k (conjuncts pbod0)
  and (pcjs1,qcjs1) = chop_list k (snd(chop_list n (conjuncts pbod1)))
  val tyal0 = mk_set (zip (map grab_type pcjs1) (map grab_type pcjs0))
  val tyal1 = map (fn (a,b) => (b,a)) tyal0
  val tyins0 = map
   (fn f => let
     val (domty,ranty) = dest_fun_ty (type_of f)
   in
     (tysubst tyal0 domty,ranty)
   end) pevs0
  and tyins1 = map
   (fn f => let
     val (domty,ranty) = dest_fun_ty (type_of f)
   in
     (tysubst tyal1 domty,ranty)
   end) pevs1
  val tth0 = Thm.INST_TYPE (jrh_inst_flip tyins0) sth0
  and tth1 = Thm.INST_TYPE (jrh_inst_flip tyins1) sth1
  val (evs0,bod0) = strip_exists(concl tth0)
  and (evs1,bod1) = strip_exists(concl tth1)
  val (lcjs0,rcjs0) = chop_list k (map (snd o strip_forall) (conjuncts bod0))
  and (lcjs1,rcjsx) = chop_list k (map (snd o strip_forall)
                                   (snd(chop_list n (conjuncts bod1))))
  val rcjs1 =  map (fn t => find (clause_corresponds t) rcjsx) rcjs0
  fun proc_clause tm0 tm1 = let
    val (l0,r0) = dest_eq tm0
    and (l1,r1) = dest_eq tm1
    val (vc0,wargs0) = strip_comb r0
    val (con0,vargs0) = strip_comb(rand l0)
    val gargs0 = map (genvar o type_of) wargs0
    val nestf0 =
      map (fn a => can (find (fn t => is_comb t andalso rand t = a))
           wargs0) vargs0
    val targs0 =
      map2 (fn a => fn f =>
            if f then
              find (fn t => is_comb t andalso rand t = a) wargs0
            else a)
      vargs0 nestf0
    val gvlist0 = zip wargs0 gargs0
    val xargs = map (fn v => assoc v gvlist0) targs0
    val inst0 =
      (vc0 |->
       list_mk_abs(gargs0,list_mk_comb(fst(strip_comb(rand l1)),xargs)))
    val (vc1,wargs1) = strip_comb r1
    val (con1,vargs1) = strip_comb(rand l1)
    val gargs1 = map (genvar o type_of) wargs1
    val targs1 =
      map2 (fn a => fn f =>
            if f then find (fn t => is_comb t andalso rand t = a) wargs1
            else a)
      vargs1 nestf0
    val gvlist1 = zip wargs1 gargs1
    val xargs = map (fn v => assoc v gvlist1) targs1
    val inst1 =
      (vc1 |->
       list_mk_abs(gargs1,list_mk_comb(fst(strip_comb(rand l0)),xargs)))
  in
    (inst0,inst1)
  end
  val (insts0,insts1) = unzip (map2 proc_clause (lcjs0@rcjs0) (lcjs1@rcjs1))
  val uth0 = BETA_RULE(Thm.INST insts0 tth0)
  and uth1 = BETA_RULE(Thm.INST insts1 tth1)
  val (efvs0,sth0) = DE_EXISTENTIALIZE_RULE uth0
  and (efvs1,sth1) = DE_EXISTENTIALIZE_RULE uth1
  val efvs2 =
    map (fn t1 => find (fn t2 =>
                        hd(tl(snd(dest_type(type_of t1)))) =
                        hd(snd(dest_type(type_of t2))))
         efvs1)
    efvs0
  val isotms = map2 (fn ff => fn gg =>
                     list_mk_icomb "ISO" [ff,gg])
    efvs0 efvs2
  val ctm = list_mk_conj isotms
  val cth1 = ISO_EXPAND_CONV ctm
  val ctm1 = rand(concl cth1)
  val cjs = conjuncts ctm1
  val eee = map (fn n => n mod 2 = 0) (upto (length cjs - 1))
  val (cjs1,cjs2) = partition fst (zip eee cjs)
  val ctm2 = mk_conj(list_mk_conj (map snd cjs1),
                     list_mk_conj (map snd cjs2))
  val cth2 = CONJ_ACI_CONV (mk_eq(ctm1,ctm2))
  val cth3 = TRANS cth1 cth2
  val DETRIV_RULE = TRIV_ANTE_RULE o REWRITE_RULE[sth0, sth1]
  val jth0 = let
    val itha = SPEC_ALL ith0
    val icjs = conjuncts(rand(concl itha))
    val cinsts =
      map (fn tm => tryfind (fn vtm => Ho_match.match_term [] vtm tm) icjs)
      (conjuncts (rand ctm2))
    val tvs = subtract (fst(strip_forall(concl ith0)))
                (itlist (fn (x,_) => union (map snd x)) cinsts [])
    val ctvs =
      map (fn p => let val x = mk_var("x",hd(snd(dest_type(type_of p))))
      in (p |-> mk_abs(x,T_tm)) end) tvs
  in
    DETRIV_RULE (BETA_RULE (Thm.INST ctvs (itlist INSTANTIATE cinsts itha)))
  end
  and jth1 = let
    val itha = SPEC_ALL ith1
    val icjs = conjuncts(rand(concl itha))
    val cinsts = map (fn tm => tryfind
                      (fn vtm => Ho_match.match_term [] vtm tm) icjs)
                     (conjuncts (lhand ctm2))
    val tvs = subtract (fst(strip_forall(concl ith1)))
      (itlist (fn (x,_) => union (map snd x)) cinsts [])
    val ctvs =
      map (fn p => let val x = mk_var("x",hd(snd(dest_type(type_of p)))) in
           (p |-> mk_abs(x,T_tm)) end) tvs
  in
    DETRIV_RULE (BETA_RULE (Thm.INST ctvs (itlist INSTANTIATE cinsts itha)))
  end
  val cths4 = map2 CONJ (CONJUNCTS jth0) (CONJUNCTS jth1)
  val cths5 = map (PURE_ONCE_REWRITE_RULE[GSYM ISO]) cths4
  val cth6 = end_itlist CONJ cths5
in
  (cth6,CONJ sth0 sth1)
end

(* ------------------------------------------------------------------------- *)
(* Define nested type by doing a 1-level unwinding.                          *)
(* ------------------------------------------------------------------------- *)

fun SCRUB_ASSUMPTION th = let
  val hyps = hyp th
  val eqn =
    find
    (fn t => let
      val x = lhs t
    in
      List.all (fn u => not (free_in x (rand u))) hyps
    end) hyps
  val (l,r) = dest_eq eqn
in
  MP (Thm.INST [l |-> r] (DISCH eqn th)) (REFL r)
end

val safeid_genvar = let
  val count = ref 0
  fun vary_to_avoid_constants () = let
    val nm = "ii_internal" ^ current_theory() ^ Int.toString (!count)
  in
    if (can const_decl nm) then (count := !count + 100;
                                   vary_to_avoid_constants())
    else (count := !count + 1; nm)
  end
in
  fn ty => Term.mk_var{Name = vary_to_avoid_constants(), Ty = ty}
end

fun define_type_basecase def = let
  fun add_id s = fst(dest_var(safeid_genvar Type.bool))
  val def' = map (I F_F (map (add_id F_F I))) def
in
  define_type_mutual def'
end

val SIMPLE_BETA_RULE = GSYM o SIMP_RULE bool_ss [Ho_theorems.FUN_EQ_THM];
val ISO_USAGE_RULE = MATCH_MP ISO_USAGE;
val SIMPLE_ISO_EXPAND_RULE = CONV_RULE(REWR_CONV ISO);

fun REWRITE_FUN_EQ_RULE thl = SIMP_RULE bool_ss (Ho_theorems.FUN_EQ_THM::thl)


fun get_nestedty_info tyname =
  case TypeBase.read tyname of
    SOME tyinfo => SOME (length (TypeBase.constructors_of tyinfo),
                         TypeBase.induction_of tyinfo,
                         TypeBase.axiom_of tyinfo)
  | NONE => NONE

(* JRH's package returns the list type's induction theorem as:
      !P. P [] /\ (!h t. P t ==> P (h::t)) ==> !l. P l
   hol90 tradition is to have induction theorems where the universal
   variables in the hypotheses are pushed as far to the right as possible, so
   that the above appears as:
      !P. P [] /\ (!t. P t ==> !h. P (h::t)) ==> !l. P l
   A small difference you might think, but it causes the venerable
   INDUCT_THEN code to cark, and who am I to fiddle with INDUCT_THEN?
   And haven't I already introduced enough gratuitous incompatibilities?
   So, push_in_vars below performs this conversion.

   Further, the old induction theorems automatically proved by
   prove_induction_thm picked names for bound variables that were appropriate
   for the type (the first letter of the type, basically).  So, rename_bvars
   below does this too.

   Finally, munge_ind_thm composes the two functions.
*)
local
  fun CONJUNCTS_CONV c tm =
    if is_conj tm then BINOP_CONV (CONJUNCTS_CONV c) tm else c tm
  fun SWAP_TILL_BOTTOM_THEN c t =
    ((SWAP_VARS_CONV THENC BINDER_CONV (SWAP_TILL_BOTTOM_THEN c)) ORELSEC c) t
  fun app_letter ty =
    if is_vartype ty then String.sub(dest_vartype ty, 1)
    else String.sub(#1 (dest_type ty), 0)
  fun new_name ctxt ty = let
    fun nvary ctxt nm n = let
      val fullname = nm ^ Int.toString n
    in
      if Lib.mem fullname ctxt then nvary ctxt nm (n + 1) else fullname
    end
    val name = str (app_letter ty)
  in
    if Lib.mem name ctxt then nvary ctxt name 0 else name
  end
in
  fun push_in_vars thm = let
    fun each_conj tm =
      if is_forall tm then let
        val (vs, body) = strip_forall tm
      in
        if is_imp body then let
          val (ant,con) = Psyntax.dest_imp body
        in
          if mem (hd vs) (free_vars ant) then
            BINDER_CONV each_conj tm
          else
            (SWAP_TILL_BOTTOM_THEN FORALL_IMP_CONV THENC each_conj) tm
        end
        else REFL tm
      end
      else REFL tm
    val c =
      STRIP_QUANT_CONV (RATOR_CONV (RAND_CONV (CONJUNCTS_CONV each_conj)))
  in
    CONV_RULE c thm
  end

  fun rename_bvars thm = let
    fun renCONV ctxt tm =
      if is_forall tm orelse is_exists tm then let
        val dest = if is_forall tm then dest_forall else dest_exists
        val (Bvar, Body) = dest tm
        val vname = new_name ctxt (type_of Bvar)
      in
        (RENAME_VARS_CONV [vname] THENC
         BINDER_CONV (renCONV (vname::ctxt))) tm
      end
      else if is_abs tm then ABS_CONV (renCONV ctxt) tm
      else if is_comb tm then (RATOR_CONV (renCONV ctxt) THENC
                               RAND_CONV (renCONV ctxt)) tm
      else REFL tm
    val Pvars = map (#1 o dest_var) (#1 (strip_forall (concl thm)))
  in
    CONV_RULE (STRIP_QUANT_CONV (renCONV Pvars)) thm
  end

  val munge_ind_thm = rename_bvars o push_in_vars

end

local
  fun is_nested vs ty =
    not (is_vartype ty) andalso not (intersect (type_vars ty) vs = [])
  fun modify_type alist ty =
    rev_assoc ty alist
    handle HOL_ERR _ =>
      (let
        val (tycon,tyargs) = dest_type ty
      in
         mk_type(tycon,map (modify_type alist) tyargs)
      end handle HOL_ERR _ => ty)
  fun modify_item alist (s,l) = (s,map (modify_type alist) l)
  fun modify_clause alist (l,lis) = (l,map (modify_item alist) lis)
  fun recover_clause id tm = let
    val (con,args) = strip_comb tm
  in
    (fst(dest_const con)^id, map type_of args)
  end
  fun create_auxiliary_clauses nty = let
    val id = fst(dest_var(safeid_genvar Type.bool))
    val (tycon,tyargs) = dest_type nty
    val (k,ith,rth) =
      valOf (get_nestedty_info tycon)
      handle Option.Option =>
        raise HOL_ERR {origin_function = "define_type_nested",
                       origin_structure = "ind_types",
                       message = ("Can't find definition for nested type: "^
                                  tycon)}
    val (evs,bod) = strip_exists(snd(strip_forall(concl rth)))
    val cjs = map (lhand o snd o strip_forall) (conjuncts bod)
    val rtys = map (hd o snd o dest_type o type_of) evs
    val tyins = tryfind (fn vty => Type.match_type vty nty) rtys
    val cjs' = map (Term.inst tyins o rand) (fst(chop_list k cjs))
    val mtys = itlist (insert o type_of) cjs' []
    val pcons = map (fn ty => filter (fn t => type_of t = ty) cjs') mtys
    val cls' = zip mtys (map (map (recover_clause id)) pcons)
    val tyal =
      map (fn ty => (mk_vartype("'"^fst(dest_type ty)^id),ty)) mtys
    val cls'' = map (modify_type tyal F_F map (modify_item tyal)) cls'
  in
    (k,tyal,cls'',Thm.INST_TYPE tyins ith, Thm.INST_TYPE tyins rth)
  end
  fun define_type_nested def = let
    val n = length(itlist (curry op@) (map (map fst o snd) def) [])
    val newtys = map fst def
    val utys = Union (itlist (union o map snd o snd) def [])
    val rectys = filter (is_nested newtys) utys
  in
    if rectys = [] then let
      val (th1,th2) = define_type_basecase def
    in
      (n,th1,th2)
    end else let
      val nty = hd rectys
      val (k,tyal,ncls,ith,rth) = create_auxiliary_clauses nty
      val cls = map (modify_clause tyal) def @ ncls
      val (_,ith1,rth1) = define_type_nested cls
      val xnewtys =
        map (hd o snd o dest_type o type_of)
        (fst(strip_exists(snd(strip_forall(concl rth1)))))
      val xtyal =
        map
        (fn ty => let
          val s = dest_vartype ty
        in
          (ty |-> find (fn t => "'"^fst(dest_type t) = s) xnewtys)
        end) (map fst cls)
      val ith0 = Thm.INST_TYPE xtyal ith
      and rth0 = Thm.INST_TYPE xtyal rth
      val (isoth,rclauses) =
        prove_inductive_types_isomorphic n k (ith0,rth0) (ith1,rth1)
      val irth3 = CONJ ith1 rth1
      val vtylist = itlist (insert o type_of) (variables(concl irth3)) []
      val isoths = CONJUNCTS isoth
      val isotys =
        map (hd o snd o dest_type o type_of o lhand o concl) isoths
      val ctylist = filter
        (fn ty => List.exists (fn t => occurs_in t ty) isotys) vtylist
      val atylist = itlist (union o striplist dest_fun_ty) ctylist []
      val isoths' = map (lift_type_bijections isoths)
        (filter (fn ty => List.exists
                 (fn t => occurs_in t ty) isotys) atylist)
      val cisoths = map (BETA_RULE o lift_type_bijections isoths') ctylist
      val uisoths = map ISO_USAGE_RULE cisoths
      val visoths = map (ASSUME o concl) uisoths
      val irth4 =
        itlist PROVE_HYP uisoths (REWRITE_FUN_EQ_RULE visoths irth3)
      val irth5 = REWRITE_RULE
        (rclauses :: map SIMPLE_ISO_EXPAND_RULE isoths') irth4
      val irth6 = repeat SCRUB_ASSUMPTION irth5
      val ncjs = filter (fn t =>
                         List.exists (not o is_var)
                         (snd(strip_comb(rand(lhs(snd(strip_forall t)))))))
        (conjuncts(snd(strip_exists
                       (snd(strip_forall(rand(concl irth6)))))))
      val id = fst(dest_var(genvar Type.bool))
      fun mk_newcon tm = let
        val (vs,bod) = strip_forall tm
        val rdeb = rand(lhs bod)
        val rdef = list_mk_abs(vs,rdeb)
        val newname = fst(dest_var(safeid_genvar Type.bool))
        val def = mk_eq(mk_var(newname,type_of rdef),rdef)
        val dth = new_definition (newname, def)
      in
        SIMPLE_BETA_RULE dth
      end
      val dths = map mk_newcon ncjs
      val (ith6,rth6) = CONJ_PAIR(PURE_REWRITE_RULE dths irth6)
    in
      (n,ith6,rth6)
    end
  end
in
  val define_type_nested = fn def => let
    val newtys = map fst def
    val truecons = itlist (curry op@) (map (map fst o snd) def) []
    val (p,ith0,rth0) = define_type_nested def
    val (avs,etm) = strip_forall(concl rth0)
    val allcls = conjuncts(snd(strip_exists etm))
    val relcls = fst(chop_list (length truecons) allcls)
    val gencons =
      map (repeat rator o rand o lhand o snd o strip_forall) relcls
    val cdefs =
      map2 (fn s => fn r =>
            SYM(new_definition (s, mk_eq(mk_var(s,type_of r),r))))
      truecons gencons
    val tavs = make_args "f" [] (map type_of avs)
    val ith1 = SUBS cdefs ith0
    and rth1 = GENL tavs (SUBS cdefs (SPECL tavs rth0))
    val retval = (p,ith1,rth1)
    val newentries = map (fn s => (String.extract(dest_vartype s, 1, NONE),
                                   retval)) newtys
  in
    (fn (a,b,c) => (munge_ind_thm b,c)) retval
  end
end

val define_type = define_type_nested

(* test this with:

   val def = [(Type`:'foo`, [("C1", []), ("C2", [Type`:num`])])];
   (* HOL Light equivalent:
    let def =
      let foo = mk_vartype "foo" in
      [(foo, [("C1", []); ("C2", [`:num`])])];;
    *)

   define_type_nested def;

   val def = [(Type`:'bar`, [("D1", [Type`:num`]), ("D2", [Type`:'bar`])])];
   define_type_nested def;

   val def = [(Type`:'qux`, [("F1", []), ("F2", [Type`:'qux option`])])];
   (* HOL Light equivalent :
       let def =
         let qux = mk_vartype "qux" in
         [(qux, [("F1", []); ("F2", [mk_type("option", [qux])])])];; *)
   define_type_nested def;

   val def = [(Type`:'bozz`, [("G1", [Type`:num`, Type`:'fozz`])]),
              (Type`:'fozz`, [("G2", [Type`:'bozz option`]),
                              ("G3", [Type`:num + 'fozz`])])]
   (* HOL Light equivalent :
       let def =
         let bozz = mk_vartype "bozz"
         and fozz = mk_vartype "fozz" in
         [(bozz, [("G1", [`:num`; fozz])]);
          (fozz, [("G2", [mk_type("option", [bozz])]);
                  ("G3", [mk_type("sum", [`:num`; fozz])])])];;
       let (bozz_ind, bozz_rec) = define_type_nested def;;
   *)

   val (bozz_ind, bozz_rec) = define_type_nested def;

*)
