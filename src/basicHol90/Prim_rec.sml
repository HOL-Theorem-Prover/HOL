(* ===================================================================== *)
(* FILE          : prim_rec.sml                                          *)
(* DESCRIPTION   : Primitive recursive definitions on arbitrary recursive*)
(*                 types.  Assumes the type is defined by an axiom of    *)
(*                 the form proved by the recursive types package.       *)
(*                 Translated from hol88.                                *)
(*                                                                       *)
(* AUTHOR        : (c) T. F. Melham, University of Cambridge             *)
(* DATE	         : 87.08.23                                              *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                   *)
(* DATE          : September 11, 1991                                    *)
(* REVISED       : 17.1.98                                               *)
(* REVISION      : Added Induct_then and prove_induction_thm and         *)
(*                 prove_cases_thm from former Rec_type_support.         *)
(* ===================================================================== *)


structure Prim_rec :> Prim_rec =
struct
open HolKernel Parse boolTheory Drule Tactical Tactic
     Rewrite Conv Resolve Thm_cont;
infix THEN THENL ORELSE ## |->;


type term = Term.term
type thm = Thm.thm
type tactic = Abbrev.tactic

fun ERR function message =
  HOL_ERR{origin_structure = "Prim_rec",
          origin_function = function,
          message = message}

(* remove x satisfying p from l.... giving x and the thing and rest of l*)
fun pr_remove p [] = raise ERR "pr_remove" "[]"
  | pr_remove p (a::A) =
     if p a then (a, A) else (I##(fn r => (a :: r))) (pr_remove p A);


(*----------------------------------------------------------------------*)
(* derive_existence_thm th tm						*)
(*									*)
(* If th is a rec type axiom and tm is a term giving a prim rec 	*)
(* definition, derive an existence theorem for doing the definition.	*)
(* The existence theorem has cases corresponding to those in tm and	*)
(* is suitably type-instantiated.					*)
(*									*)
(* E.g. Input								*)
(*									*)
(* |- !f0 f1 f2 e. ?! fn.						*)
(*    (!x0 x1 t t'. fn(C1 t x0 t' x1) = f0(fn t)(fn t')x0 x1 t t') /\	*)
(*    (!t. fn(C2 t) = f1(fn t)t) /\             			*)
(*    (!x. fn(C3 x) = f2 x) /\     					*)
(*     (fn C4 = e)							*)
(*									*)
(*  "(!n b. Fn n C4 b = ...) /\						*)
(*   (!b n m t x t'. Fn n (C1 t' b t m) x = ...) /\			*)
(*   (!m x q. Fn m (C3 x) q = ...)"					*)
(*									*)
(* Output:								*)
(*									*)
(* |- !e f0 f2. ?fn.							*)
(*    (!g1 g2. fn C4 g1 g2 = e g1 g2) /\				*)
(*    (!g3 g4 g5 g6 g7 g8. fn(C1 g5 g3 g6 g4) g7 g8 = 			*)
(*		       f0(fn g5)(fn g6)g3 g4 g5 g6) g7 g8 /\	        *)
(*    (!g9 g10 g11. fn(C3 g9) g10 g11 = f2 g9 g10 g11)			*)
(*									*)
(* Note: the g's are genvars	(so are e ... f2)			*)
(*----------------------------------------------------------------------*)


(* val derive_existence_thm = fn : thm -> term -> thm   *)

fun derive_existence_thm th tm : thm =
   let val vars = map (genvar o type_of) (Lib.fst(strip_forall(concl th)))
       val exists = CONJUNCT1(CONV_RULE EXISTS_UNIQUE_CONV(SPECL vars th))
       val e_fn = #Bvar(dest_exists(concl exists))
       and conjs = strip_conj tm
       fun splt (h::t) =
              if (is_var h)
              then let val (bv,C,av) = splt t
                   in ((h::bv), C, av)
                   end
              else if (is_const h orelse is_comb h)
                   then ([], h, t)
                   else raise ERR "derive_existence_thm" "1"
       val(bv,Con,av) = splt(snd(strip_comb(lhs(snd(strip_forall(hd conjs))))))
       val rhsfn = let val cv = genvar(type_of Con)
                       val r = rhs(snd(strip_forall(hd conjs)))
                   in list_mk_abs(cv::(bv @ av),r)
                   end
       val th_inst = INST_TYPE (Lib.snd(Term.match_term e_fn rhsfn)) exists
       fun get_c t =
          let val args = Lib.snd(strip_comb(lhs(Lib.snd(strip_forall t))))
              val c = Lib.fst(strip_comb(Lib.first
                                  (fn t => is_const t orelse is_comb t) args))
          in if (is_const c) then c
           else raise ERR "derive_existence_thm" "2"
          end
       val cs  = map get_c conjs
       and exl = CONJUNCTS (SELECT_RULE th_inst)
       and fn1 = #Bvar(dest_exists(concl th_inst))
       fun same_c c cl =
          (c = fst (strip_comb (rand (lhs (snd (strip_forall (concl cl)))))))
       fun get_ths [] exl = []
         | get_ths (a::A) exl =
              let val (c, ex) = pr_remove (same_c a) exl
              in (c :: (get_ths A ex))
              end
       val ths = get_ths cs exl
       val argvars = map (genvar o type_of) (bv @ av)
       fun ap_ths th =
          let val v = map (genvar o type_of) (Lib.fst(strip_forall(concl th)))
              val th1 = Lib.rev_itlist (Lib.C AP_THM) argvars (SPECL v th)
          in
          GENL (v @ argvars) th1
          end
       val th1 = LIST_CONJ (map ap_ths ths)
       val sel = mk_select(dest_exists (concl th_inst))
   in
   GEN_ALL(EXISTS(mk_exists{Bvar = fn1, Body = subst[sel |-> fn1] (concl th1)},
                  sel) th1)
   end handle (e as HOL_ERR{origin_structure = "Prim_rec",
                            origin_function = "derive_existence_thm",...})
               => raise e
        |  HOL_ERR _ => raise ERR "derive_existence_thm" "";



(*------------------------------------------------------------------------*)
(* mk_fn: make the function for the rhs of a clause in the existence thm  *)
(*                                                                        *)
(* returns:  1) the function                                              *)
(*      2) a list of variables that the clause should be SPECL            *)
(*      3) a pre-done beta-conversion of the rhs.                         *)
(*------------------------------------------------------------------------*)

fun mk_fn (cl, Fn, bv, C, ((av, r):Abbrev.goal)) =
 let val (lcl::lclvars) = Lib.snd(strip_comb (lhs (Lib.snd (strip_forall cl))))
     val m = (Lib.fst(Term.match_term lcl C))
            @(Lib.map2 (fn res => fn red => (red |-> res)) (bv@av) lclvars)
       val cl'= subst m (Lib.snd(strip_forall cl))
       val z1 = Lib.snd(strip_comb(rhs cl'))
       val nonrec = Lib.filter (is_var)  z1
       and rec1 = Lib.filter (is_comb) z1
       val recvars = map (genvar o type_of) rec1
       val basepat = list_mk_comb(Fn, (map (genvar o type_of) bv))
       fun find t =
            find_terms
              (fn tm => Lib.can(Term.match_term
                                  (mk_comb{Rator=basepat,Rand=t})) tm
                        andalso (Lib.fst (strip_comb tm) = Fn)
                        andalso (rand tm = t))
       fun do_subst (new,old) tm =
          if (tm = old)
          then new
          else if (is_abs tm)
               then let val {Bvar,Body} = dest_abs tm
                    in mk_abs{Bvar = Bvar, Body = do_subst(new,old) Body}
                    end
               else if (is_comb tm)
                    then let val {Rator,Rand} = dest_comb tm
                             val f = do_subst(new,old)
                         in mk_comb{Rator = f Rator, Rand = f Rand}
                         end
                    else tm
       fun mk_substs (rc,rcv) t =
          let val occs = find (rand rc) t
              fun args tm = Lib.snd(strip_comb (rator tm))
              val news = map (fn tm => list_mk_comb(rcv,args tm)) occs
          in itlist do_subst (zip news occs) t
          end
       val r'= Lib.itlist mk_substs (Lib.zip rec1 recvars) r
       val varsub = map (fn v => (v |-> genvar (type_of v))) (recvars@nonrec)
       val fn1 = list_mk_abs(map #residue varsub,subst varsub r')
       fun subst_assoc _ [] = NONE
         | subst_assoc v ({redex,residue}::L) =
                if (v = redex) then SOME residue else subst_assoc v L
       val specl =
             map (fn v => case (subst_assoc v m) of (SOME x) => x | NONE => v)
                 (fst(strip_forall cl))
       val beta = LIST_BETA_CONV(list_mk_comb(fn1,snd(strip_comb(rhs cl'))))
   in
   (fn1, specl, beta)
   end;


fun MK_FN (cl, (Fn, bv, C, g)) = mk_fn (cl, Fn, bv, C, g);


(* instantiate_existence_thm eth tm : instantiate eth to match tm   *)
(*                                                                  *)
(* E.g. INPUT:                                                      *)
(*                                                                  *)
(* |- !e f0 f2. ?fn.                                                *)
(*    (!g1 g2. fn C4 g1 g2 = e g1 g2) /\                            *)
(*    (!g3 g4 g5 g6 g7 g8. fn(C1 g5 g3 g6 g4) g7 g8 =               *)
(*           f0(fn g5)(fn g6)g3 g4 g5 g6) g7 g8 /\                  *)
(*    (!g9 g10 g11. fn(C3 g9) g10 g11 = f2 g9 g10 g11)              *)
(*                                                                  *)
(*                                                                  *)
(*  "(!n b. Fn n C4 b = ...) /\                                     *)
(*   (!b n m t x t'. Fn n (C1 t' b t m) x = ...) /\                 *)
(*   (!m x q. Fn m (C3 x) q = ...)"                                 *)
(*                                                                  *)
(* OUTPUT:                                                          *)
(*  |- ?fn. (!n b. fn C4 n b = ...) /\                              *)
(*          (!b n m t x t'. fn (C1 t' b t m) n x = ...) /\          *)
(*      (!m x q. fn (C3 x) m q = ...)                               *)



local fun z3 [] A B C = (A, rev B, rev C)
        | z3 ((a, b, c)::L) A B C = z3 L (a::A) (b::B) (c::C)
in
fun unzip3 L = z3 L [] [] []
end;

fun instantiate_existence_thm eth tm :thm =
   let val cls = map (Lib.snd o strip_forall) (strip_conj tm)
       fun splt [] = raise ERR "instantiate_existence_thm" "splt.[]"
         | splt (a::A) =
             if (is_var a)
             then let val (bv,C,av) = splt A
                  in ((a :: bv),C,av)
                  end
             else if (is_const a) orelse (is_comb a)
                  then ([], a, A)
                  else raise ERR "instantiate_existence_thm" "splt.non-empty"
       fun dest tm =
          let val {lhs,rhs = r} = dest_eq tm
              val (Fn,(bv,C,av)) = ((I ## splt) o strip_comb) lhs
          in (Fn,bv,C,((av,r):Abbrev.goal))
          end
       val destcl = map dest cls
       val ecls = strip_conj(#Body(dest_exists
                      (Lib.snd(strip_forall(concl eth)))))
       val (fns,spec,beta) = unzip3 (map MK_FN (Lib.zip ecls destcl))
       val ethsp = SPECL fns eth
       val conjs = map (Lib.uncurry SPECL)
                       (Lib.combine(spec,CONJUNCTS(SELECT_RULE ethsp)))
       fun rule (th1,th2) = CONV_RULE (RAND_CONV (REWR_CONV th1)) th2
       val th = LIST_CONJ (map (GEN_ALL o rule) (Lib.zip beta conjs))
       val fn1 = #Bvar(dest_exists (concl ethsp))
       and fsel = mk_select(dest_exists(concl ethsp))
   in
   EXISTS(mk_exists{Bvar=fn1, Body=subst[fsel |-> fn1] (concl th)},fsel) th
   end handle (e as HOL_ERR{origin_structure = "Prim_rec",
                            origin_function = "instantiate_existence_thm",...})
               => raise e
        | HOL_ERR _ => raise ERR "instantiate_existence_thm" "";


(* prove_rec_fn_exists th tm                               *)
(*                                                         *)
(* Given 1) th, a recursion theorem (type axiom)           *)
(*       2) tm, the specification of a recursive function  *)
(*                                                         *)
(* proves that such a function exists.                     *)

(* Quantify the equations of the function spec.            *)

fun closeup tm =
   let fun lvars t =
          set_diff (free_varsl(snd(strip_comb(lhs(snd (strip_forall t))))))
                   (fst(strip_forall t))
   in list_mk_conj(map (fn tm => list_mk_forall(lvars tm,tm)) (strip_conj tm))
   end;


(*---------------------------------------------------------------------------
 * MJCG 17/1/89: added test for attempted redefinition of a constant and
 * code to propagate failure message.
 *
 * KLS 22/10/97: removed test for attempted redefinition of constants.
 * This is OK, because of the tagging scheme on theorems.
 *---------------------------------------------------------------------------*)

fun prove_rec_fn_exists th tm : thm =
 let val eth = derive_existence_thm th tm
     val ith = instantiate_existence_thm eth tm
     val cl = Lib.snd(strip_forall(hd(strip_conj tm)))
     val fn0 = Lib.fst(strip_comb(lhs cl))
     val fn1 = if (is_const fn0) then mk_var(dest_const fn0) else fn0
     fun get_avars tm  =
	 if (is_var (rand tm))
         then get_avars (rator tm)
         else (Lib.snd(strip_comb (rator tm)),rand tm)
     val (av,tv) = ((map (genvar o type_of)) ## (genvar o type_of))
	             (get_avars (lhs cl))
     val goal = ([],mk_exists{Bvar=fn1, Body=closeup tm})
     fun etac th =
           let val efn = fst(strip_comb(lhs(snd(strip_forall(concl th)))))
           in EXISTS_TAC (list_mk_abs(av@[tv],list_mk_comb(efn,tv::av)))
           end
     fun fn_beta th (A,gl) =
       let val efn = Lib.fst(strip_comb(lhs
                              (Lib.snd(strip_forall(concl th)))))
           val eabs = list_mk_abs(av@[tv],list_mk_comb(efn, tv::av))
           val epat = list_mk_comb(eabs, map (genvar o type_of) (av @ [tv]))
           val tms = find_terms(fn tm => Lib.can(Term.match_term epat) tm) gl
       in PURE_ONCE_REWRITE_TAC (map LIST_BETA_CONV tms) (A,gl)
       end
   in
     GEN_ALL(TAC_PROOF(goal,
              STRIP_ASSUME_TAC ith THEN
                FIRST_ASSUM etac THEN
                REPEAT STRIP_TAC THEN
                FIRST_ASSUM fn_beta THEN
                FIRST_ASSUM MATCH_ACCEPT_TAC))
   end
   handle (e as HOL_ERR{origin_structure = "Prim_rec",
                        origin_function = "prove_rec_fn_exists",...})
           => raise e
        | HOL_ERR _ => raise ERR "prove_rec_fn_exists"
                                 "Can't solve recursion equation";

(* Make a new recursive function definition.				*)
fun new_recursive_definition {name,fixity,rec_axiom,def} =
 let val thm = prove_rec_fn_exists rec_axiom def
 in
 new_specification
    {name = name, sat_thm = thm,
     consts =  [{fixity = fixity,
                 const_name = #Name(dest_var(#Bvar(dest_exists(concl thm))))}]}
 end;



(*---------------------------------------------------------------------------
 * Addition 17.1.98: Induct_then, prove_induction_thm, and prove_cases_thm
 * moved here.
 *---------------------------------------------------------------------------*)

fun ERR function message =
    Exception.HOL_ERR{origin_structure = "Prim_rec.Induct_then",
		      origin_function = function,
		      message = message}

(* ---------------------------------------------------------------------*)
(* Internal function: 							*)
(*									*)
(* BETAS "f" tm : returns a conversion that, when applied to a term with*)
(*		 the same structure as the input term tm, will do a	*)
(*		 beta reduction at all top-level subterms of tm which	*)
(*		 are of the form "f <arg>", for some argument <arg>.	*)
(*									*)
(* ---------------------------------------------------------------------*)

fun BETAS fnn body =
   if ((is_var body) orelse (is_const body))
   then REFL
   else if (is_abs body)
        then ABS_CONV (BETAS fnn (#Body(dest_abs body)))
        else let val {Rator,Rand} = dest_comb body
             in
             if (Rator = fnn)
             then BETA_CONV
             else let val cnv1 = BETAS fnn Rator
                      and cnv2 = BETAS fnn Rand
                      fun f {Rator,Rand} = (cnv1 Rator, cnv2 Rand)
                  in
	          (MK_COMB o (f o dest_comb))
                  end
             end;

(* ---------------------------------------------------------------------*)
(* Internal function: GTAC						*)
(*									*)
(*   !x. tm[x]  							*)
(*  ------------  GTAC "y"   (primes the "y" if necessary).		*)
(*     tm[y]								*)
(*									*)
(* NB: the x is always a genvar, so optimized for this case.		*)
(* ---------------------------------------------------------------------*)

fun GTAC y (A,g) =
   let val {Bvar,Body} = dest_forall g
       and y' = variant (free_varsl (g::A)) y
   in
   ([(A,subst[{redex = Bvar, residue = y'}]Body)],
    fn [th] => GEN Bvar (INST [{redex = y', residue = Bvar}] th))
   end;

(* ---------------------------------------------------------------------*)
(* Internal function: TACF						*)
(*									*)
(* TACF is used to generate the subgoals for each case in an inductive 	*)
(* proof.  The argument tm is formula which states one generalized	*)
(* case in the induction. For example, the induction theorem for num is:*)
(*									*)
(*   |- !P. P 0 /\ (!n. P n ==> P(SUC n)) ==> !n. P n			*)
(*									*)
(* In this case, the argument tm will be one of:			*)
(*									*)
(*   1:  "P 0"   or   2: !n. P n ==> P(SUC n)				*)
(*   									*)
(* TACF applied to each these terms to construct a parameterized tactic *)
(* which will be used to further break these terms into subgoals.  The  *)
(* resulting tactic takes a variable name x and a user supplied theorem *)
(* continuation ttac.  For a base case, like case 1 above, the resulting*)
(* tactic just throws these parameters away and passes the goal on 	*)
(* unchanged (i.e. \x ttac. ALL_TAC).  For a step case, like case 2, the*)
(* tactic applies GTAC x as many times as required.  It then strips off *)
(* the induction hypotheses and applies ttac to each one.  For example, *)
(* if tac is the tactic generated by:					*)
(*									*)
(*    TACF "!n. P n ==> P(SUC n)" "x:num" ASSUME_TAC			*)
(*									*)
(* then applying tac to the goal A,"!n. P[n] ==> P[SUC n] has the same 	*)
(* effect as applying:							*)
(*									*)
(*    GTAC "x:num" THEN DISCH_THEN ASSUME_TAC				*)
(*									*)
(* TACF is a strictly local function, used only to define TACS, below.	*)
(* ---------------------------------------------------------------------*)
local
fun ctacs tm =
   if (is_conj tm)
   then let val tac2 = ctacs (#conj2(dest_conj tm))
        in
        fn ttac => CONJUNCTS_THEN2 ttac (tac2 ttac)
        end
   else fn ttac => ttac
in
fun TACF tm =
   let val (vs,body) = strip_forall tm
   in
   if (is_imp body)
   then let val TTAC = ctacs (#ant(dest_imp body))
        in
        fn x => fn ttac =>
           MAP_EVERY (GTAC o Lib.K x) vs THEN
           DISCH_THEN (TTAC ttac)
        end
   else
   fn x => fn ttac => Tactical.ALL_TAC
   end
end;

(* ---------------------------------------------------------------------*)
(* Internal function: TACS						*)
(*									*)
(* TACS uses TACF to generate a parameterized list of tactics, one for  *)
(* each conjunct in the hypothesis of an induction theorem.		*)
(*									*)
(* For example, if tm is the hypothesis of the induction thoerem for the*)
(* natural numbers---i.e. if:						*)
(*									*)
(*   tm = "P 0 /\ (!n. P n ==> P(SUC n))"				*)
(*									*)
(* then TACS tm yields the paremterized list of tactics:		*)
(*									*)
(*   \x ttac. [TACF "P 0" x ttac; TACF "!n. P n ==> P(SUC n)" x ttac]   *)
(*									*)
(* TACS is a strictly local function, used only in INDUCT_THEN.		*)
(* ---------------------------------------------------------------------*)

fun f {conj1,conj2} = (TACF conj1, TACS conj2)
and
    TACS tm =
      let val (cf,csf) = f(dest_conj tm)
                         handle HOL_ERR _ => (TACF tm, Lib.K(Lib.K[]))
      in
      fn x => fn ttac => (cf x ttac)::(csf x ttac)
      end;

(* ---------------------------------------------------------------------*)
(* Internal function: GOALS						*)
(*									*)
(* GOALS generates the subgoals (and proof functions) for all the cases *)
(* in an induction. The argument A is the common assumption list for all*)
(* the goals, and tacs is a list of tactics used to generate subgoals 	*)
(* from these goals.							*)
(*									*)
(* GOALS is a strictly local function, used only in INDUCT_THEN.	*)
(* ---------------------------------------------------------------------*)
fun GOALS A [] tm = raise ERR "GOALS" "empty list"
  | GOALS A [t] tm =
      let val (sg,pf) = t (A,tm)
      in
      ([sg],[pf])
      end
  | GOALS A (h::t) tm =
      let val {conj1,conj2} = dest_conj tm
          val (sgs,pfs) = GOALS A t conj2
          val (sg,pf) = h (A,conj1)
      in
      ((sg::sgs),(pf::pfs))
      end;

(* --------------------------------------------------------------------- *)
(* Internal function: GALPH						*)
(* 									*)
(* GALPH "!x1 ... xn. A ==> B":   alpha-converts the x's to genvars.	*)
(* --------------------------------------------------------------------- *)
local
fun rule v =
   let val gv = genvar(type_of v)
   in
   fn eq => let val th = FORALL_EQ v eq
            in
            TRANS th (GEN_ALPHA_CONV gv (rhs(concl th)))
            end
   end
in
fun GALPH tm =
   let val (vs,hy) = strip_forall tm
   in
   if (is_imp hy)
   then Lib.itlist rule vs (REFL hy)
   else REFL tm
   end
end;

(* ---------------------------------------------------------------------*)
(* Internal function: GALPHA						*)
(* 									*)
(* Applies the conversion GALPH to each conjunct in a sequence.		*)
(* ---------------------------------------------------------------------*)

local val AND = --`$/\`--
in
fun f {conj1,conj2} = (GALPH conj1, GALPHA conj2)
and GALPHA tm =
   let val (c,cs) = f(dest_conj tm)
   in
    MK_COMB(AP_TERM AND c, cs)
   end
   handle HOL_ERR _ => GALPH tm
end;

(* ---------------------------------------------------------------------*)
(* Internal function: mapshape						*)
(* 									*)
(* Applies the functions in fl to argument lists obtained by splitting  *)
(* the list l into sublists of lengths given by nl.			*)
(* ---------------------------------------------------------------------*)

fun mapshape [] _ _ =  [] |
    mapshape (n1::nums) (f1::funcs) args =
       let val (f1_args,args') = Lib.split_after n1 args
       in
       (f1 f1_args)::(mapshape nums funcs args')
       end;

(* --------------------------------------------------------------------- *)
(* INDUCT_THEN : general induction tactic for concrete recursive types.	 *)
(* --------------------------------------------------------------------- *)
local val bool = genvar Type.bool
in
fun INDUCT_THEN th =
   let val {Bvar,Body} = dest_forall(concl th)
       val {ant = hy, ...} = dest_imp Body
       val bconv = BETAS Bvar hy
       and tacsf = TACS hy
       val v = genvar (type_of Bvar)
       val eta_th = CONV_RULE(RAND_CONV ETA_CONV) (UNDISCH(SPEC v th))
       val ([asm],con) = dest_thm eta_th
       val dis = DISCH asm eta_th
       val ind = GEN v (SUBST [bool |-> GALPHA asm]
                              (mk_imp{ant = bool, conseq = con}) dis)
   in
   fn ttac => fn (A,t) =>
      let val lam = #Rand(dest_comb t)
          val spec = SPEC lam (INST_TYPE (Lib.snd(Term.match_term v lam)) ind)
          val {ant,conseq} = dest_imp(concl spec)
          val beta = SUBST [bool |-> bconv ant]
                           (mk_imp{ant=bool, conseq=conseq}) spec
          val tacs = tacsf (#Bvar(dest_abs lam)) ttac
          val (gll,pl) = GOALS A tacs (#ant(dest_imp(concl beta)))
          val pf = ((MP beta) o LIST_CONJ) o mapshape(map length gll)pl
      in
        (Lib.flatten gll, pf)
      end
      handle HOL_ERR_ => raise ERR "INDUCT_THEN" "tactic application error"
   end
   handle (e as Exception.HOL_ERR
	           {origin_structure = "Induct_then",
		    origin_function = "INDUCT_THEN",...}) => raise e
        | HOL_ERR _ => raise ERR "INDUCT_THEN" "ill-formed induction theorem"
end;

(*---------------------------------------------------------------------------
 * Now prove_induction_thm and prove_cases_thm.
 *---------------------------------------------------------------------------*)

fun ERR function message =
      HOL_ERR{origin_structure = "Prim_rec",
	      origin_function = function,
	      message = message}
infixr 3 ==;
infixr 3 ==>;
infixr 3 /\;
infixr 3 \/;
infixr 3 -->;
infixr 3 THENC;
infixr 3 ORELSEC;

fun (x == y)  = mk_eq{lhs=x,    rhs=y};
fun (x ==> y) = mk_imp{ant=x, conseq=y}
fun (x /\ y)  = mk_conj{conj1=x, conj2=y};
fun (x \/ y)  = mk_disj{disj1=x, disj2=y};


(* =====================================================================*)
(* STRUCTURAL INDUCTION				      (c) T Melham 1990	*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Internal function: UNIQUENESS					*)
(*									*)
(* This function derives uniqueness from unique existence:		*)
(* 									*)
(*        |- ?!x. P[x]							*)
(* --------------------------------------- 				*)
(*  |- !v1 v2. P[v1] /\ P[v2] ==> (v1=v2)				*)
(* 									*)
(* The variables v1 and v2 are genvars.					*)
(* ---------------------------------------------------------------------*)
val AP_AND = AP_TERM (--`$/\`--);

local val P = mk_var{Name="P", Ty = Type`:'a->bool`}
      val alpha = Type`:'a`
      val v = genvar Type.bool
      and v1 = genvar alpha
      and v2 = genvar alpha
      val th1 = SPEC P (CONV_RULE (X_FUN_EQ_CONV P) EXISTS_UNIQUE_DEF)
      val th2 = CONJUNCT2(UNDISCH(fst(EQ_IMP_RULE(RIGHT_BETA th1))))
      val imp = GEN P (DISCH (--`$?! ^P`--) (SPECL [v1, v2] th2))
      fun AND (e1,e2) = MK_COMB(AP_AND e1, e2)
      fun beta_conj{conj1,conj2} = (BETA_CONV conj1, BETA_CONV conj2)
      fun conv tm = AND (beta_conj (dest_conj tm))
      val check = assert (fn c => (#Name(dest_const c) = "?!"))
in
fun UNIQUENESS th =
  let val {Rator,Rand} = dest_comb(concl th)
      val _ = check Rator
      val s = [alpha |-> type_of (bvar Rand)]
      val uniq = MP (SPEC Rand (INST_TYPE s imp)) th
      val red = conv (#ant(dest_imp(concl uniq)))
      val (V1,V2) = let val i = Term.inst s in (i v1,i v2) end
  in
    GEN V1 (GEN V2 (SUBST[v |-> red] (v ==> (V1 == V2)) uniq))
  end
  handle HOL_ERR _ => raise ERR "UNIQUENESS" ""
end;

(* ---------------------------------------------------------------------*)
(* Internal function: DEPTH_FORALL_CONV					*)
(*									*)
(* DEPTH_FORALL_CONV conv `!x1...xn. tm` applies the conversion conv to *)
(* the term tm to yield |- tm = tm', and then returns:			*)
(*									*)
(*    |- (!x1...xn. tm)  =  (!x1...xn. tm')				*)
(*									*)
(* ---------------------------------------------------------------------*)

fun DEPTH_FORALL_CONV conv tm =
   let val (vs,th) = (I ## conv) (strip_forall tm)
   in itlist FORALL_EQ vs th
   end;

(* ---------------------------------------------------------------------*)
(* Internal function: CONJS_CONV					*)
(*									*)
(* CONJS_CONV conv `t1 /\ t2 /\ ... /\ tn` applies conv to each of the  *)
(* n conjuncts t1,t2,...,tn and then rebuilds the conjunction from the  *)
(* results.								*)
(*									*)
(* ---------------------------------------------------------------------*)

fun CONJS_CONV conv tm =
   let val {conj1,conj2} = dest_conj tm
   in MK_COMB(AP_AND (conv conj1), CONJS_CONV conv conj2)
   end handle HOL_ERR _ => conv tm;


(* ---------------------------------------------------------------------*)
(* Internal function: CONJS_SIMP					*)
(*									*)
(* CONJS_SIMP conv `t1 /\ t2 /\ ... /\ tn` applies conv to each of the  *)
(* n conjuncts t1,t2,...,tn.  This should reduce each ti to `T`.  I.e.  *)
(* executing conv ti should return |- ti = T.  The result returned by   *)
(* CONJS_SIMP is then: |- (t1 /\ t2 /\ ... /\ tn) = T			*)
(*									*)
(* ---------------------------------------------------------------------*)

local val T_AND_T = CONJUNCT1 (SPEC (--`T`--) AND_CLAUSES)
in
val CONJS_SIMP  =
   let fun simp conv tm =
          let val {conj1,conj2} = dest_conj tm
          in TRANS (MK_COMB(AP_AND (conv conj1), simp conv conj2))
                   (T_AND_T)
          end handle HOL_ERR _ => conv tm
   in simp
   end
end;

(* ---------------------------------------------------------------------*)
(* Internal function: T_AND_CONV					*)
(*									*)
(* T_AND_CONV `T /\ t` returns |- T /\ t = t				*)
(*									*)
(* ---------------------------------------------------------------------*)

local val T_AND = GEN_ALL (CONJUNCT1 (SPEC_ALL AND_CLAUSES))
in
fun T_AND_CONV tm = SPEC (#conj2(dest_conj tm)) T_AND
end;

(* ---------------------------------------------------------------------*)
(* Internal function: GENL_T						*)
(*									*)
(* GENL_T [x1;...;xn] returns |- (!x1...xn.T) = T			*)
(*									*)
(* ---------------------------------------------------------------------*)

local val t = --`T`--      val t_eq_t = REFL t
in
fun GENL_T [] = t_eq_t
  | GENL_T l =
      let val gen = list_mk_forall(l,t)
          val imp1 = DISCH gen (SPECL l (ASSUME gen))
          val imp2 = DISCH t (GENL l (ASSUME t))
      in IMP_ANTISYM_RULE imp1 imp2
      end
end;

(* ---------------------------------------------------------------------*)
(* Internal function: SIMP_CONV						*)
(*									*)
(* SIMP_CONV is used by prove_induction_thm to simplify to `T` terms of *)
(* the following two forms:						*)
(*									*)
(*   1: !x1...xn. (\x.T)v = (\x1...xn.T) x1 ... xn			*)
(*									*)
(*   2: !x1...xn. (\x.T)v = 						*)
(*      (\y1...ym x1..xn. (y1 /\.../\ ym) \/ t) ((\x.T)u1)...((\x.T)um) *)
(*      					       x1 ... xn	*)
(*									*)
(* If tm, a term of one of these two forms, is the argument to SIMP_CONV*)
(* then the theorem returned is |- tm = T.				*)
(* ---------------------------------------------------------------------*)

local val v = genvar Type.bool
      and tr = --`T`--
      val T_OR = GEN v (CONJUNCT1 (SPEC v OR_CLAUSES))
      fun DISJ_SIMP tm =
         let val {disj1,disj2} = dest_disj tm
             val eqn = SYM(CONJS_SIMP BETA_CONV disj1)
         in
         SUBST[v |-> eqn] ((v \/ disj2) == tr) (SPEC disj2 T_OR)
         end
      val eq = --`$= :bool->bool->bool`--
      and T_EQ_T = EQT_INTRO(REFL tr)
in
fun SIMP_CONV tm =
   let val (vs,{lhs,rhs}) = (I ## dest_eq) (strip_forall tm)
       val rsimp = (LIST_BETA_CONV THENC (DISJ_SIMP ORELSEC REFL)) rhs
       and lsimp = AP_TERM eq (BETA_CONV lhs)
       and gent  = GENL_T vs
       val eqsimp = TRANS (MK_COMB(lsimp,rsimp)) T_EQ_T
   in
   TRANS (itlist FORALL_EQ vs eqsimp) gent
   end
end;

(* ---------------------------------------------------------------------*)
(* Internal function: HYP_SIMP						*)
(*									*)
(* HYP_SIMP is used by prove_induction_thm to simplify induction 	*)
(* hypotheses according to the following scheme:			*)
(*									*)
(*   1: !x1...xn. P t = (\x1...xn.T) x1...xn				*)
(*									*)
(*         simplifies to    						*)
(*									*)
(*      !x1...xn. P t							*)
(*									*)
(*   2: !x1...xn. P t = 						*)
(*        ((\y1..ym x1..xn. y1 /\ ... /\ ym) \/ P t) v1 ... vm x1 ... xn*)
(*									*)
(*         simplifies to						*)
(*									*)
(*      !x1...xn. (v1 /\ ... /\ vm) ==> P t				*)
(*									*)
(* ---------------------------------------------------------------------*)

local val v = genvar Type.bool
      and tr = --`T`--
      val EQ_T = GEN v (CONJUNCT1 (CONJUNCT2 (SPEC v EQ_CLAUSES)))
      fun R_SIMP tm =
         let val {lhs,rhs} = dest_eq tm
         in if (rhs = tr)
            then SPEC lhs EQ_T
            else SPECL [lhs, #disj1(dest_disj rhs)] OR_IMP_THM
         end
      val eq = --`$= :bool->bool->bool`--
in
fun HYP_SIMP tm =
   let val (vs,{lhs,rhs}) = (I ## dest_eq) (strip_forall tm)
       val eqsimp = AP_TERM (mk_comb{Rator = eq, Rand = lhs})
                            (LIST_BETA_CONV rhs)
       val rsimp = CONV_RULE (RAND_CONV R_SIMP) eqsimp
   in itlist FORALL_EQ vs rsimp
   end
end;

(* ---------------------------------------------------------------------*)
(* Internal function: ANTE_ALL_CONV					*)
(*									*)
(* ANTE_ALL_CONV `!x1...xn. P ==> Q` restricts the scope of as many of	*)
(* the quantified x's as possible to the term Q.  			*)
(* ---------------------------------------------------------------------*)

fun ANTE_ALL_CONV tm =
   let val (vs,{ant,...}) = (I ## dest_imp) (strip_forall tm)
       val (ov,iv) = partition (C free_in ant) vs
       val thm1 = GENL iv (UNDISCH (SPECL vs (ASSUME tm)))
       val thm2 = GENL ov (DISCH ant thm1)
       val asm = concl thm2
       val thm3 = SPECL iv (UNDISCH (SPECL ov (ASSUME asm)))
       val thm4 = GENL vs (DISCH ant thm3)
   in
   IMP_ANTISYM_RULE (DISCH tm thm2) (DISCH asm thm4)
   end;

(* ---------------------------------------------------------------------*)
(* Internal function: CONCL_SIMP					*)
(*									*)
(* CONCL_SIMP `\x.T = P` returns: |- (\x.T = P) = (!y. P y) where y is	*)
(* an appropriately chosen variable.					*)
(* ---------------------------------------------------------------------*)

local val v = genvar Type.bool
      val T_EQ = GEN v (CONJUNCT1 (SPEC v EQ_CLAUSES))
in
fun CONCL_SIMP tm =
   let val eq = FUN_EQ_CONV tm
       val {Bvar,Body} = dest_forall(rhs(concl eq))
       val eqn = RATOR_CONV(RAND_CONV BETA_CONV) Body
       and simp = SPEC (rhs Body) T_EQ
   in
   TRANS eq (FORALL_EQ Bvar (TRANS eqn simp))
  end
end;

(* ---------------------------------------------------------------------*)
(* prove_induction_thm: prove a structural induction theorem from a type*)
(* axiom of the form returned by define_type.				*)
(*									*)
(* EXAMPLE: 								*)
(*									*)
(* Input: 								*)
(* 									*)
(*    |- !x f. ?! fn. (fn[] = x) /\ (!h t. fn(CONS h t) = f(fn t)h t) 	*)
(* 									*)
(* Output:								*)
(* 									*)
(*    |- !P. P [] /\ (!t. P t ==> (!h. P(CONS h t))) ==> (!l. P l)	*)
(* 									*)
(* ---------------------------------------------------------------------*)

local val B = Type.bool
      val tr = --`T`--
      fun gen 0 = []
        | gen n = genvar B::gen (n-1)
      fun mk_fn P ty tm =
         let val {lhs,rhs} = dest_eq(snd(strip_forall tm))
             val c = rand lhs
             val args = snd(strip_comb rhs)
             val vars = filter is_var args
             val n = length(filter (fn t => type_of t = ty) vars)
         in if (n=0)
            then list_mk_abs (vars, tr)
            else let val bools = gen n
                     val term = list_mk_conj bools \/ mk_comb{Rator=P, Rand=c}
                 in list_mk_abs((bools@vars),term)
                 end
         end
      val LCONV = RATOR_CONV o RAND_CONV
      val conv1 = LCONV(CONJS_SIMP SIMP_CONV) THENC T_AND_CONV
      and conv2 = CONJS_CONV (HYP_SIMP THENC TRY_CONV ANTE_ALL_CONV)
in
fun prove_induction_thm th =
   let val {Bvar,Body} = dest_abs(rand(snd(strip_forall(concl th))))
       val {Args = [ty, rty],...} = dest_type (type_of Bvar)
       val inst = INST_TYPE [rty |-> B] th
       val P = mk_primed_var{Name = "P", Ty = ty --> B}
       and v = genvar ty
       and cases = strip_conj Body
       val uniq = let val (vs,tm) = strip_forall(concl inst)
                      val thm = UNIQUENESS(SPECL vs inst)
                  in GENL vs (SPECL [mk_abs{Bvar=v, Body=tr}, P] thm)
                  end
      val spec = SPECL (map (mk_fn P ty) cases) uniq
      val simp =  CONV_RULE (LCONV(conv1 THENC conv2)) spec
   in
     GEN P (CONV_RULE (RAND_CONV CONCL_SIMP) simp)
   end
   handle HOL_ERR _ => raise ERR "prove_induction_thm" ""
end;


(* ---------------------------------------------------------------------*)
(* Internal function: NOT_ALL_THENC					*)
(*									*)
(* This conversion first moves negation inwards through an arbitrary	*)
(* number of nested universal quantifiers. It then applies the supplied	*)
(* conversion to the resulting inner negation.  For example if:		*)
(*									*)
(*	conv "~tm" ---> |- ~tm = tm'					*)
(* then									*)
(*									*)
(*       NOT_ALL_THENC conv "~(!x1 ... xn. tm)"				*)
(*									*)
(* yields:								*)
(*									*)
(*       |- ~(!x1...xn.tm) = ?x1...xn.tm'				*)
(* ---------------------------------------------------------------------*)

fun NOT_ALL_THENC conv tm =
   (NOT_FORALL_CONV THENC
    (RAND_CONV (ABS_CONV (NOT_ALL_THENC conv)))) tm
    handle HOL_ERR _ => conv tm;

(* ---------------------------------------------------------------------*)
(* Internal function: BASE_CONV						*)
(*									*)
(* This conversion does the following simplification:			*)
(*									*)
(*    BASE_CONV "~((\x.~tm)y)"  --->  |- ~((\x.~tm)y) = tm[y/x]		*)
(*									*)
(* ---------------------------------------------------------------------*)

local val NOT_NOT = CONJUNCT1 NOT_CLAUSES
      and neg = --`$~`--
in
fun BASE_CONV tm =
   let val beta = BETA_CONV (dest_neg tm)
       val simp = SPEC (rand(rhs(concl beta))) NOT_NOT
   in TRANS (AP_TERM neg beta) simp
   end
end;

(* ---------------------------------------------------------------------*)
(* Internal function: STEP_CONV						*)
(*									*)
(* This conversion does the following simplification:			*)
(*									*)
(*    STEP_CONV "~(tm' ==> !x1..xn.(\x.~tm)z"  				*)
(*									*)
(* yields:								*)
(*									*)
(*   |- ~(tm' ==> !x1..xn.(\x.~tm)z = tm' /\ ?x1..xn.tm[z/x]  		*)
(* ---------------------------------------------------------------------*)

local val v1 = genvar Type.bool
      and v2 = genvar Type.bool
in
fun STEP_CONV tm =
   let val {ant,conseq} = dest_imp(dest_neg tm)
       val th1 = SPEC conseq (SPEC ant NOT_IMP)
       val simp = NOT_ALL_THENC BASE_CONV (mk_neg conseq)
   in
   SUBST [v2 |-> simp] (tm == (ant /\ v2)) th1
   end
end;

(* ---------------------------------------------------------------------*)
(* Internal function: NOT_IN_CONV					*)
(*									*)
(* This first conversion moves negation inwards through conjunction and	*)
(* universal quantification:						*)
(*									*)
(*   NOT_IN_CONV  "~(!x1..xn.c1 /\ ... /\ !x1..xm.cn)"			*)
(*									*)
(* to transform the input term into:					*)
(*									*)
(*   ?x1..xn. ~c1 \/ ... \/ ?x1..xm. ~cn				*)
(*									*)
(* It then applies either BASE_CONV or STEP_CONV to each subterm ~ci.	*)
(* ---------------------------------------------------------------------*)

local val A = mk_var{Name="A",Ty = Type.bool}
      val B = mk_var{Name="B",Ty = Type.bool}
      val DE_MORG = GENL [A,B] (CONJUNCT1(SPEC_ALL DE_MORGAN_THM))
      and cnv = BASE_CONV ORELSEC STEP_CONV
      and v1 = genvar Type.bool
      and v2 = genvar Type.bool
in
fun NOT_IN_CONV tm =
   let val {conj1,conj2} = dest_conj(dest_neg tm)
       val thm = SPEC conj2 (SPEC conj1 DE_MORG)
       val cth = NOT_ALL_THENC cnv (mk_neg conj1)
       and csth = NOT_IN_CONV (mk_neg conj2)
   in
     SUBST[v1 |-> cth, v2 |-> csth] (tm == (v1 \/ v2)) thm
   end
   handle HOL_ERR _ => NOT_ALL_THENC cnv tm
end;


(* ---------------------------------------------------------------------*)
(* Internal function: STEP_SIMP						*)
(*									*)
(* This rule does the following simplification:				*)
(*									*)
(*    STEP_RULE "?x1..xi. tm1 /\ ?xj..xn. tm2"				*)
(*									*)
(* yields:								*)
(*									*)
(*   ?x1..xi.tm1 /\ ?xj..xn.tm2 |- ?x1..xn.tm2				*)
(*									*)
(* For input terms of other forms, the rule yields:			*)
(*									*)
(*   STEP_RULE "tm" ---> tm |- tm					*)
(* ---------------------------------------------------------------------*)

local fun EX tm th = EXISTS (mk_exists{Bvar = tm, Body = concl th},tm) th
      fun CH tm th = CHOOSE (tm,ASSUME(mk_exists{Bvar=tm, Body=hd(hyp th)})) th
in
fun STEP_SIMP tm =
   let val (vs,body) = strip_exists tm
   in itlist (fn t => CH t o EX t) vs (CONJUNCT2 (ASSUME body))
   end handle HOL_ERR _ => ASSUME tm
end;


(* ---------------------------------------------------------------------*)
(* Internal function: DISJ_CHAIN					*)
(*									*)
(* Suppose that 							*)
(*									*)
(*    rule "tmi"  --->   tmi |- tmi'		(for 1 <= i <= n)	*)
(*									*)
(* then:								*)
(*									*)
(*       |- tm1 \/ ... \/ tmn						*)
(*    ---------------------------   DISJ_CHAIN rule			*)
(*      |- tm1' \/ ... \/ tmn' 						*)
(* ---------------------------------------------------------------------*)

fun DISJS_CHAIN rule th =
   let val concl_th = concl th
   in let val {disj1,disj2} = dest_disj concl_th
          val i1 = rule disj1
          and i2 = DISJS_CHAIN rule (ASSUME disj2)
      in
      DISJ_CASES th (DISJ1 i1 (concl i2)) (DISJ2 (concl i1) i2)
      end
      handle HOL_ERR _ => MP (DISCH concl_th (rule concl_th)) th
   end;


(* --------------------------------------------------------------------- *)
(* prove_cases_thm: prove a cases or "exhaustion" theorem for a concrete *)
(* recursive type from a structural induction theorem of the form 	 *)
(* returned by prove_induction_thm.					 *)
(*									 *)
(* EXAMPLE: 								 *)
(*									 *)
(* Input: 								 *)
(* 									 *)
(*    |- !P. P[] /\ (!t. P t ==> (!h. P(CONS h t))) ==> (!l. P l)	 *)
(* 									 *)
(* Output:								 *)
(* 									 *)
(*    |- !l. (l = []) \/ (?t h. l = CONS h t)				 *)
(* 									 *)
(* --------------------------------------------------------------------- *)

fun prove_cases_thm th =
 let val {Bvar,Body} =
          dest_forall(#conseq(dest_imp(#Body(dest_forall(concl th)))))
     val v = genvar (type_of Bvar)
     val pred = mk_abs{Bvar=v, Body=mk_neg(Bvar == v)}
     val th1 = CONV_RULE BETA_CONV (SPEC Bvar (UNDISCH (SPEC pred th)))
     val th2 = NOT_INTRO (DISCH_ALL (MP th1 (REFL Bvar)))
     val th3 = CONV_RULE NOT_IN_CONV th2
 in
     GEN Bvar (DISJS_CHAIN STEP_SIMP th3)
 end
 handle HOL_ERR _ => raise ERR"prove_cases_thm" "";



(*---------------------------------------------------------------------------
      Need to special-case on whether the current pattern is
      actually a numeric literal.
 ---------------------------------------------------------------------------*)

(*
fun dest_constr_app tm =
 let val (r as (c,args)) = strip_comb tm
 in case dest_const c
     of {Name = "NUMERAL", ...} => (tm, [])
      | _ => r
 end;
*)

fun strip_vars tm = let
  fun pull_off_var tm acc = let
    val {Rator, Rand} = dest_comb tm
  in
    if is_var Rand then
      pull_off_var Rator (Rand::acc)
    else
      (tm, acc)
  end handle HOL_ERR _ => (tm, acc)
in
  pull_off_var tm []
end

(*---------------------------------------------------------------------------
    Proving case congruence:

     |- (M = M') /\
        (!x1,...,xk. (M' = C1 x1..xk) ==> (f1 x1..xk = f1' x1..xk))
         /\ ... /\
        (!x1,...,xj. (M' = Cn x1..xj) ==> (fn x1..xj = fn' x1..xj))
        ==>
       (ty_case f1..fn M = ty_case f1'..fn' m')

 ---------------------------------------------------------------------------*)

fun case_cong_term case_def =
 let val clauses = (strip_conj o concl) case_def
     val clause1 = Lib.trye hd clauses
     val left = (#lhs o dest_eq o #2 o strip_forall) clause1
     val ty = type_of (rand left)
     val allvars = all_varsl clauses
     val M = variant allvars (mk_var{Name = "M", Ty = ty})
     val M' = variant (M::allvars) (mk_var{Name = "M", Ty = ty})
     val lhsM = mk_comb{Rator=rator left, Rand=M}
     val c = #1(strip_comb left)
     fun mk_clause clause =
       let val {lhs,rhs} = (dest_eq o #2 o strip_forall) clause
           val func = (#1 o strip_comb) rhs
           val {Name,Ty} = dest_var func
           val func' = variant allvars (mk_var{Name=Name^"'", Ty=Ty})
           val capp = rand lhs
           val (constr,xbar) = strip_vars capp
       in (func',
           list_mk_forall
           (xbar, mk_imp{ant = mk_eq{lhs=M',rhs=capp},
                         conseq = mk_eq{lhs=list_mk_comb(func,xbar),
                                        rhs=list_mk_comb(func',xbar)}}))
       end
     val (funcs',clauses') = unzip (map mk_clause clauses)
 in
 mk_imp{ant = list_mk_conj(mk_eq{lhs=M, rhs=M'}::clauses'),
        conseq = mk_eq{lhs=lhsM, rhs=list_mk_comb(c,(funcs'@[M']))}}
 end;

(*---------------------------------------------------------------------------*
 *                                                                           *
 *        A, v = M[x1,...,xn] |- N                                           *
 *  ------------------------------------------                               *
 *     A, ?x1...xn. v = M[x1,...,xn] |- N                                    *
 *                                                                           *
 *---------------------------------------------------------------------------*)

fun EQ_EXISTS_LINTRO (thm,(vlist,theta)) =
  let val [veq] = filter (can dest_eq) (hyp thm)
      fun CHOOSER v (tm,thm) =
        let val w = (case (subst_assoc (fn w => v=w) theta)
                      of SOME w => w
                       | NONE => v)
            val ex_tm = mk_exists{Bvar=w, Body=tm}
        in (ex_tm, CHOOSE(w, ASSUME ex_tm) thm)
        end
  in snd(itlist CHOOSER vlist (veq,thm))
  end;


fun OKform case_def =
  let val clauses = (strip_conj o concl) case_def
      val left = (rator o #lhs o dest_eq o #2 o strip_forall)
                 (Lib.trye hd clauses)
      val opvars = #2 (strip_comb left)
      fun rhs_head c = fst(strip_comb(rhs(snd(strip_forall c))))
      val rhs_heads = map rhs_head clauses
      fun check [] = true
        | check ((x,y)::rst) = (x=y) andalso check rst
  in
     check (zip opvars rhs_heads)
  end


fun case_cong_thm nchotomy case_def =
 let val _ = assert OKform case_def
     val gl = case_cong_term case_def
     val {ant,conseq} = dest_imp gl
     val imps = CONJUNCTS (ASSUME ant)
     val M_eq_M' = hd imps
     val {lhs=M, rhs=M'} = dest_eq (concl M_eq_M')
     fun get_asm tm = (#ant o dest_imp o #2 o strip_forall) tm handle _ => tm
     val case_assms = map (ASSUME o get_asm o concl) imps
     val {lhs=lconseq, rhs=rconseq} = dest_eq conseq
     val lconseq_thm = SUBST_CONV[M |-> M_eq_M'] lconseq lconseq
     val lconseqM' = rhs(concl lconseq_thm)
     val nchotomy' = ISPEC M' nchotomy
     val disjrl = map ((I##rhs) o strip_exists)	(strip_disj (concl nchotomy'))
     fun zot icase_thm (iimp,(vlist,disjrhs)) =
       let val lth = Rewrite.REWRITE_CONV[icase_thm, case_def] lconseqM'
           val rth = Rewrite.REWRITE_CONV[icase_thm, case_def] rconseq
           val theta = Term.match_term disjrhs
                     ((rhs o #ant o dest_imp o #2 o strip_forall o concl) iimp)
           val th = MATCH_MP iimp icase_thm
           val th1 = TRANS lth th
       in (TRANS th1 (SYM rth), (vlist, #1 theta))
       end
     val thm_substs = map2 zot (Lib.trye tl case_assms)
                               (zip (Lib.trye tl imps) disjrl)
     val aag = map (TRANS lconseq_thm o EQ_EXISTS_LINTRO) thm_substs
 in
   GEN_ALL (DISCH_ALL (DISJ_CASESL nchotomy' aag))
 end
 handle HOL_ERR _ => raise ERR "case_cong_thm" "construction failed";


end; (* Prim_rec *)
