(*---------------------------------------------------------------------------*)
(* Defines a type of equivalence classes, and transfers a list of            *)
(* functions and theorems about the representatives over to the new type.    *)
(* It returns a list of the transferred theorems.                            *)
(*                                                                           *)
(* name   - desired name of new type                                         *)
(*                                                                           *)
(* equiv    - Theorem that R is an equivalence relation; in the form:        *)
(*               |- !x y. x R y = (R x = R y)                                *)
(*                                                                           *)
(* fnlist   - list of {fname,func,fixity} where fname is the new function    *)
(*            name, func is the old term, and fixity gives the parsing       *)
(*            status.                                                        *)
(*                                                                           *)
(* welldefs - theorems asserting that the old functions are welldefined;     *)
(*            of the form |- (x1 R y1) /\ .. /\ (xn R yn) ==>                *)
(*                             (f x1 .. xn) R (f y1 .. yn)                   *)
(*            where "R" becomes "=" for types other than the                 *)
(*            representing type.                                             *)
(*                                                                           *)
(* thlist   - List of theorems about the old functions                       *)
(*                                                                           *)
(* Restrictions:                                                             *)
(*                                                                           *)
(*  * R must be an equivalence relation over the whole type, no subsets.     *)
(*                                                                           *)
(*  * All original functions must be curried (as are the new ones).          *)
(*                                                                           *)
(*  * The theorems must have all variables bound by existential or           *)
(*    universal quantifiers.                                                 *)
(*                                                                           *)
(*  * The theorems must be obviously `well-defined', i.e. invariant under    *)
(*    substitution [t/u] whenever |- t R u. Essentially "R" becomes "=" and  *)
(*    old functions become the new ones.                                     *)
(*                                                                           *)
(*  * All arguments/results of the representing type will be transferred     *)
(*    to the new type.                                                       *)
(*                                                                           *)
(* Author: John Harrison                                                     *)
(*---------------------------------------------------------------------------*)

structure EquivType :> EquivType =
struct

(* The Standard Header *)
open HolKernel Parse boolLib liteLib;

(* Fix the grammar used by this file *)
val ambient_grammars = Parse.current_grammars();
val _ = Parse.temp_set_grammars boolTheory.bool_grammars

val LAND_CONV = RATOR_CONV o RAND_CONV;
val PROVE = Tactical.default_prover

fun MK_COMB_TAC (asl,w) =
  let val (l,r) = dest_eq w
      val (l1,l2) = dest_comb l
      val (r1,r2) = dest_comb r in
  ([(asl,mk_eq(l1,r1)), (asl,mk_eq(l2,r2))],end_itlist (curry MK_COMB)) end;


(*---------------------------------------------------------------------------*)
(* Define this as hol90 dislikes genvars in constant definitions             *)
(* N.B. This is hopelessly crude.                                            *)
(*---------------------------------------------------------------------------*)

fun upto from to =
  if from>to then []
  else from::upto (from+1) to;

fun wargs tylist =
  let val nums = upto 1 (length tylist)
(*  val nms = map (fn n => implode ("T"::(explode(chr(n + ord"0"))))) nums in*)
      val nms = map (fn n => "T"^Lib.int_to_string n) nums
  in
      map mk_var (zip nms tylist)
  end;

(*---------------------------------------------------------------------------*)
(* Now the main function.                                                    *)
(*---------------------------------------------------------------------------*)


fun define_equivalence_type{name=tyname, equiv, defs = fnlist,
                            welldefs, old_thms = thlist} =
  let
  val absname = "mk_"^tyname and repname = "dest_"^tyname
  val eqv = (rator o rhs o rhs o snd o strip_forall o concl) equiv
  val repty = (hd o snd o dest_type o type_of) eqv
  val tydef =
    let val rtm = (--`\c. ?x. c = ^eqv x`--) in
    new_type_definition(tyname,
      PROVE((--`?c. ^rtm c`--),
            BETA_TAC THEN
            MAP_EVERY EXISTS_TAC [(--`^eqv x`--), (--`x:^(ty_antiq(repty))`--)]
            THEN REFL_TAC)) end
  val tybij = BETA_RULE
    (define_new_type_bijections {name = tyname^"_tybij",
                                 ABS = absname,
                                 REP = repname,
                                 tyax = tydef})
  val absty = mk_type(tyname,[])
  val (abs,rep) = ((I ## rator) o dest_comb o lhs o snd o dest_forall
                                o fst o dest_conj o concl) tybij

  val refl = PROVE
    ((--`!h. ^eqv h h`--),
     GEN_TAC THEN REWRITE_TAC[equiv] THEN REFL_TAC)
  val sym = PROVE
   ((--`!h i. ^eqv h i = ^eqv i h`--),
    REWRITE_TAC[equiv] THEN MATCH_ACCEPT_TAC EQ_SYM_EQ)
  val trans = PROVE
   ((--`!h i j. ^eqv h i /\ ^eqv i j ==> ^eqv h j`--),
    REPEAT GEN_TAC THEN REWRITE_TAC[equiv] THEN
    MATCH_ACCEPT_TAC EQ_TRANS)

  val EQ_AP = PROVE
   ((--`!p q. (p = q) ==> ^eqv p q`--),
    REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_ACCEPT_TAC refl)

  val EQ_WELLDEF = PROVE
   ((--`!x1 x2 y1 y2. (^eqv x1 x2) /\ (^eqv y1 y2) ==>
       ((^eqv x1 y1) = (^eqv x2 y2))`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THENL
   [RULE_ASSUM_TAC(ONCE_REWRITE_RULE[sym]), ALL_TAC] THEN
  POP_ASSUM(CONJUNCTS_THEN2 (fn th => DISCH_THEN(MP_TAC o CONJ th)) ASSUME_TAC)
  THEN DISCH_THEN(MP_TAC o MATCH_MP trans) THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[sym]) THEN
  POP_ASSUM(fn th => DISCH_THEN(MP_TAC o C CONJ th)) THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP trans))

  val DEST_MK_EQCLASS = PROVE
   ((--`!v. ^rep (^abs (^eqv v)) = ^eqv v`--),
    GEN_TAC THEN REWRITE_TAC[GSYM tybij] THEN
    EXISTS_TAC (--`v:^(ty_antiq(repty))`--) THEN REFL_TAC)

  val SAME_REP = PROVE
   ((--`!h i. ^eqv h i ==> ^eqv h ($@ (^eqv i))`--),
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC trans THEN
    EXISTS_TAC (--`i:^(ty_antiq(repty))`--) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SELECT_AX THEN
    EXISTS_TAC (--`i:^(ty_antiq(repty))`--) THEN MATCH_ACCEPT_TAC refl)

  val SAME_RCR = PROVE
    ((--`!h i. (^eqv($@(^rep h)) = ^eqv($@(^rep i))) = (h = i)`--),
     let val th = SYM(REWRITE_RULE[equiv]
                                  (SPECL [(--`h:^(ty_antiq(repty))`--),
                                          (--`h:^(ty_antiq(repty))`--)]
                                         SAME_REP))
         val th2 = REWRITE_RULE[CONJUNCT1 tybij]
                               (SPEC (--`^rep h`--)(CONJUNCT2 tybij))
         val th3 = SPEC (--`i:^(ty_antiq(absty))`--)
                        (GEN (--`h:^(ty_antiq(absty))`--) th2) in
     REPEAT GEN_TAC THEN MAP_EVERY CHOOSE_TAC [th2, th3] THEN
     ASM_REWRITE_TAC[th] THEN EVERY_ASSUM(SUBST1_TAC o SYM) THEN EQ_TAC THENL
      [DISCH_THEN(MP_TAC o AP_TERM abs), DISCH_THEN SUBST1_TAC] THEN
     REWRITE_TAC[tybij] end)

  val R_MK_COMB_TAC = FIRST
    [W(C (curry op THEN) (GEN_TAC THEN CONV_TAC
          (RAND_CONV BETA_CONV THENC LAND_CONV BETA_CONV)) o
       CONV_TAC o X_FUN_EQ_CONV o fst o dest_abs o lhs o snd),
     FIRST(map MATCH_MP_TAC (EQ_WELLDEF::welldefs)) THEN REPEAT CONJ_TAC,
     MK_COMB_TAC,
     MATCH_MP_TAC SAME_REP,
     MATCH_MP_TAC EQ_AP,
     FIRST (map MATCH_ACCEPT_TAC [refl, EQ_REFL])]

  fun EQC_FORALL_CONV tm =
    let val v = fst(dest_forall tm)
        val v' = (mk_var o(I##(K absty o assert(curry op = repty))) o dest_var)
                 v
        val th1 = GEN v' (SPEC (--`$@(^rep ^v')`--) (ASSUME tm))
        val tm' = concl th1
        val th2 = ASSUME tm'
        val th3 = GEN v (SPEC (--`^abs (^eqv ^v)`--) th2)
        val th4 = Rewrite.GEN_REWRITE_RULE ONCE_DEPTH_CONV
                       Rewrite.empty_rewrites [DEST_MK_EQCLASS] th3
        val tm'' = concl th4
        val peq = mk_eq(tm,tm'')
        val th5 = PROVE(peq,REPEAT R_MK_COMB_TAC)
        val th6 = EQ_MP(SYM th5) th4 in
    IMP_ANTISYM_RULE (DISCH_ALL th1) (DISCH_ALL th6) end

  val EQC_EXISTS_CONV =
    let val neg2 = SPEC (--`x:bool`--) (CONJUNCT1 NOT_CLAUSES) in
    REWR_CONV(SYM neg2) THENC
    RAND_CONV(NOT_EXISTS_CONV THENC EQC_FORALL_CONV) THENC
    NOT_FORALL_CONV THENC RAND_CONV(ABS_CONV(REWR_CONV neg2)) end


  fun transconv tm =
    if is_abs tm then (mk_abs o (I ## transconv) o dest_abs) tm
    else
      let val (opp,tms) = (I ## map transconv) (strip_comb tm) in
      if (mem opp (map #func fnlist) andalso (type_of tm = repty)) then
        (--`$@(^rep(^abs(^eqv ^(list_mk_comb(opp,tms)))))`--)
      else if tms = [] then opp
      else list_mk_comb(transconv opp,tms) end

  fun TRANSFORM_CONV tm =
    let val th1 =
            QCONV (DEPTH_CONV(EQC_FORALL_CONV ORELSEC EQC_EXISTS_CONV)) tm
        val tm1 = rhs(concl th1)
        val th2 = PROVE
         (mk_eq(tm1,transconv tm1),
          REWRITE_TAC[DEST_MK_EQCLASS] THEN
          REPEAT R_MK_COMB_TAC) in
    TRANS th1 th2
    end

   fun dest_funtype ty =
      if ty=repty then [ty]
      else let val (l,r) = dom_rng ty
           in [l]@dest_funtype r
           end handle HOL_ERR _ => [ty]

  fun define_fun {def_name,fname,func=tm,fixity} =
     let val tyl = dest_funtype(type_of tm)
         val ntyl = map (fn ty => if ty = repty then absty else ty) tyl
         val rty = end_itlist (fn t1 => fn t2 => mk_type("fun",[t1,t2])) ntyl
         val args = wargs (butlast ntyl)
         val rargs = map (fn tm => if (type_of tm = absty)
                                   then(--`$@ (^rep ^tm)`--)
                                   else tm)
                         args
          val l = list_mk_comb(mk_var(fname,rty),args)
          val r = let val r0 = list_mk_comb(tm,rargs)
                  in if type_of r0 = repty
                        then (--`^abs (^eqv ^r0)`--)
                        else r0
                  end
      in
        if fixity <> Prefix then
          Parse.add_rule (Parse.standard_spacing fname fixity)
        else ();
        new_definition(def_name, mk_eq(l,r))
     end

  val newdefs = map define_fun fnlist

  val newthms = map (REWRITE_RULE(map GSYM newdefs) o
                     REWRITE_RULE[equiv, SAME_RCR] o
                     CONV_RULE TRANSFORM_CONV) thlist
  in
  newthms
end;

val _ = Parse.temp_set_grammars ambient_grammars

end (* EquivType *)
