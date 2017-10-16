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
(*                                                                       *)
(* REVISED       : December 1999                                         *)
(* BY            : Michael Norrish                                       *)
(* REVISION      : Re-implemented new_prim_rec_defn using John           *)
(*                 Harrison's HOL Light code, in conjunction with the    *)
(*                 wide-ranging revisions to the datatype package.       *)
(*                                                                       *)
(* ===================================================================== *)


structure Prim_rec :> Prim_rec =
struct

open HolKernel Parse boolTheory boolSyntax
     Drule Tactical Tactic Conv Thm_cont Rewrite Abbrev;

val ERR = mk_HOL_ERR "Prim_rec";

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars boolTheory.bool_grammars
end
open Parse


(*---------------------------------------------------------------------------
     stuff from various jrh HOL-Light code
 ---------------------------------------------------------------------------*)

val lhand = rand o rator
val conjuncts = strip_conj

fun strip_vars tm =
  let fun pull_off_var tm acc =
        let val (Rator, Rand) = dest_comb tm
        in if is_var Rand then pull_off_var Rator (Rand::acc) else (tm, acc)
        end handle HOL_ERR _ => (tm, acc)
  in pull_off_var tm []
  end;

fun REPEATNC n c = if n < 1 then REFL else c THENC REPEATNC (n - 1) c

fun HEAD_BETA_CONV tm =
  let fun gotoheadpair c tm =
         if is_comb tm andalso is_comb (rator tm)
            then RATOR_CONV (gotoheadpair c) tm
            else c tm
  in
    REPEATC (gotoheadpair BETA_CONV) tm
  end;

fun CONJS_CONV c tm =
  if is_conj tm then BINOP_CONV (CONJS_CONV c) tm else c tm;

fun mymatch_and_instantiate axth pattern instance = let
  val (patvars, patbody) = strip_exists pattern
  val (instvars, instbody) = strip_exists instance
  fun tmlist_type (tm,ty) = type_of tm --> ty
  val pat_type = List.foldr tmlist_type Type.bool patvars
  val inst_type = List.foldr tmlist_type Type.bool instvars
  val tyinst = Type.match_type pat_type inst_type
  val new_patbody0 = Term.inst tyinst patbody
  val new_patvars = map (Term.inst tyinst) patvars
  val initial_env = ListPair.map op|-> (new_patvars, instvars)
  val new_patbody = Term.subst initial_env new_patbody0
  fun match_eqn cnum pat inst = let
    (* both terms of the form: !v1 .. vn. f (C1 ..) = rhs *)
    val (patvars, pateqn0) = strip_forall pat
    val (instvars, insteqn) = strip_forall inst
    val forall_env = ListPair.map op|-> (patvars, instvars)
    val pateqn = Term.subst forall_env pateqn0
    val _ = aconv (lhs pateqn) (lhs insteqn) orelse
      raise HOL_ERR {origin_function =
                "prove_raw_recursive_functions_exist.mymatch_and_instantiate",
              origin_structure = "Prim_rec",
              message = ("Failed to match LHSes in clause "^Int.toString cnum)}
    val instrhs = rhs insteqn and patrhs = rhs pateqn
    (* last arguments in the pattern will be instances of a function symbol
       being applied to recursive arguments *)
    val (pathd, patargs) = strip_comb patrhs
    val (vars, others) = partition is_var patargs
    val gvars_for_others = map (genvar o type_of) others
    val others_away =
      Term.subst (ListPair.map op|-> (others, gvars_for_others)) instrhs
    (* here we rely on the assumption that the combs we split off were the
       back half of the list of arguments *)
    val answer = list_mk_abs(vars @ gvars_for_others, others_away)
  in
    (pathd |-> answer)
    (* substitution to perform and number of beta conversions that will be
       required as well *)
  end
  fun match_eqns acc n patconjs instconjs =
    case (patconjs, instconjs) of
      ([], []) => List.rev acc
    | (p::ps, i::is) => match_eqns ((match_eqn n p i)::acc) (n + 1) ps is
    | _ => raise
        HOL_ERR {origin_function = "prove_raw_recursive_functions_exist",
                 origin_structure = "recursion",
                 message = "Number of conjuncts not even the same"}
  val tmsubst = match_eqns [] 1 (strip_conj new_patbody) (strip_conj instbody)
  val axth1 = Thm.INST_TYPE tyinst axth
  val axth2 = Thm.INST tmsubst axth1
in
  CONV_RULE (STRIP_QUANT_CONV
             (CONJS_CONV (STRIP_QUANT_CONV (RHS_CONV HEAD_BETA_CONV))))
  axth2
end

fun findax c ((p,ax)::rst) =
      ((match_term p c; (ax,rst))
        handle HOL_ERR _ => let val (a,l) = findax c rst in (a,(p,ax)::l) end)
  | findax c [] = raise ERR "prove_raw_recursive_functions_exist" "findax";

fun prove_raw_recursive_functions_exist ax tm = let
  val rawcls = conjuncts tm
  val spcls = map (snd o strip_forall) rawcls
  val lpats = map (strip_comb o lhand) spcls
  val ufns = itlist (op_insert aconv o fst) lpats []
  val axth = SPEC_ALL ax
  val (exvs,axbody) = strip_exists (concl axth)
  val axcls = conjuncts axbody
  val f = repeat rator o rand o lhand o snd o strip_forall
  val table = map (fn t => (f t,t)) axcls
  fun gax c (axs,tabl) =
       let val (axcl,tabl') = findax c tabl
       in (axcl::axs, tabl')
       end
  val raxs0 = rev_itlist gax (map (repeat rator o hd o snd) lpats) ([],table)
  val raxs = List.rev (fst raxs0)
  val axfns = map (repeat rator o lhand o snd o strip_forall) raxs
  val dict = ListPair.foldl (fn (a,(b,_),d) => Binarymap.insert(d,a,b))
                            (Binarymap.mkDict Term.compare)
                            (axfns, lpats)
  val urfns =
      map (fn v => Binarymap.find(dict,v) handle Binarymap.NotFound => v) exvs
  val axtm = list_mk_exists(exvs,list_mk_conj raxs)
  and urtm = list_mk_exists(urfns,tm)
  val ixth = mymatch_and_instantiate axth axtm urtm
  val (ixvs,ixbody) = strip_exists (concl ixth)
  val ixtm = Term.subst (map2 (curry op|->) ixvs urfns) ixbody
  val ixths = CONJUNCTS (ASSUME ixtm)
  val rixths = map (fn t => valOf (List.find (aconv t o concl) ixths)) rawcls
  val rixth = itlist SIMPLE_EXISTS ufns (end_itlist CONJ rixths)
in
  PROVE_HYP ixth (itlist SIMPLE_CHOOSE urfns rixth)
end

(* ------------------------------------------------------------------------ *)
(* Prove existence when PR argument always comes first in argument lists.   *)
(* ------------------------------------------------------------------------ *)

val prove_canon_recursive_functions_exist = let
  val RIGHT_BETAS =
      rev_itlist (fn a => CONV_RULE (RAND_CONV BETA_CONV) o C AP_THM a)
  fun canonize t = let
    val (avs,bod) = strip_forall t
    val (l,r) = dest_eq bod
    val (fnn,args) = strip_comb l
    val rarg = hd args
    and vargs = tl args
    val l' = mk_comb(fnn,rarg)
    and r' = list_mk_abs(vargs,r)
    val fvs = #2 (strip_comb rarg)
    val def = ASSUME(list_mk_forall(fvs,mk_eq(l', r')))
  in
    GENL avs (RIGHT_BETAS vargs (SPECL fvs def))
  end
in
  fn ax => fn tm => let
    val ths = map canonize (conjuncts tm)
    val atm = list_mk_conj (map (hd o hyp) ths)
    val eth = prove_raw_recursive_functions_exist ax atm
    val aths = CONJUNCTS(ASSUME atm)
    val rth = end_itlist CONJ (map2 PROVE_HYP aths ths)
    val evs = fst(strip_exists(concl eth))
  in
    PROVE_HYP eth (itlist SIMPLE_CHOOSE evs (itlist SIMPLE_EXISTS evs rth))
  end
end

(* ------------------------------------------------------------------------ *)
(* General version to prove existence.                                      *)
(* ------------------------------------------------------------------------ *)

fun universalise_clauses tm =
 let val rawcls = conjuncts tm
     val spcls = map (snd o strip_forall) rawcls
     val lpats = map (strip_comb o lhand) spcls
     val ufns = itlist (op_insert aconv o fst) lpats []
     val fvs = map (fn t => op_set_diff aconv (free_vars_lr t) ufns) rawcls
     val gcls = map2 (curry list_mk_forall) fvs rawcls
 in
   list_mk_conj gcls
 end

val prove_recursive_functions_exist =
 let fun reshuffle fnn args acc =
      let val args' = uncurry (C (curry op@)) (Lib.partition is_var args)
      in if ListPair.allEq (uncurry aconv) (args, args') then acc
         else
          let val gvs = map (genvar o type_of) args
              val gvs' = map (C (op_assoc aconv) (zip args gvs)) args'
              val lty = itlist (curry (op -->) o type_of) gvs'
                         (funpow (length gvs)
                                 (hd o tl o snd o dest_type) (type_of fnn))
              val fn' = genvar lty
              val def = mk_eq(fnn,list_mk_abs(gvs,list_mk_comb(fn',gvs')))
          in
            (ASSUME def)::acc
          end
      end
     fun scrub_def t th =
      let val (lhs, rhs) = dest_eq t
      in MP (Thm.INST [lhs |-> rhs] (DISCH t th)) (REFL rhs)
      end
     fun prove_once_universalised ax tm =
      let val rawcls = conjuncts tm
          val spcls = map (snd o strip_forall) rawcls
          val lpats = map (strip_comb o lhand) spcls
          val ufns = itlist (op_insert aconv o fst) lpats []
          val uxargs = map (C (op_assoc aconv) lpats) ufns
          val oxargs = map (uncurry (C (curry op@)) o Lib.partition is_var) uxargs
          val trths = itlist2 reshuffle ufns uxargs []
          val tth = QCONV
                      (REPEATC (CHANGED_CONV
                                  (PURE_REWRITE_CONV trths THENC
                                   DEPTH_CONV BETA_CONV))) tm
          val eth = prove_canon_recursive_functions_exist ax (rand(concl tth))
          val (evs,ebod) = strip_exists(concl eth)
          val fth = itlist SIMPLE_EXISTS ufns (EQ_MP (SYM tth) (ASSUME ebod))
          val gth = itlist scrub_def (map concl trths) fth
      in
        PROVE_HYP eth (itlist SIMPLE_CHOOSE evs gth)
      end
in
  fn ax => fn tm => prove_once_universalised ax (universalise_clauses tm)
end

val prove_rec_fn_exists = prove_recursive_functions_exist

(* ------------------------------------------------------------------------ *)
(* Version that defines function(s).                                        *)
(* ------------------------------------------------------------------------ *)

fun new_recursive_definition0 ax name tm =
 let val eth = prove_recursive_functions_exist ax tm
     val (evs,bod) = strip_exists(concl eth)
 in
  Rsyntax.new_specification
    {sat_thm=eth, name=name,
     consts = map (fn t => {const_name = fst(dest_var t),
                            fixity = NONE}) evs }
 end;

(* test with:
     load "listTheory";
     val ax =
       mk_thm([], ``!n c. ?f. (f [] = n) /\
                              (!x xs. f (CONS x xs) = c x xs (f xs))``);

     hide "map";
     val tm =
       ``(map f [] = []) /\ (map f (CONS x xs) = CONS (f x) (map f xs))``;
     prove_recursive_functions_exist ax tm;
     new_recursive_definition0 ax "map" tm;


     also
       new_type 0 "foo";
       new_type 0 "bar";
       load "arithmeticTheory";
       new_constant ("C1", ``:num -> foo``);
       new_constant ("C2", ``:bar -> foo``);
       new_constant ("D1", ``:bar``);
       new_constant ("D2", ``:foo -> num -> bar``);
       val ax = mk_thm([],
                       ``!C1' C2' D1' D2'.
                            ?fn0 fn1.
                               (!n. fn0 (C1 n) = C1' n) /\
                               (!b. fn0 (C2 b) = C2' b (fn1 b)) /\
                               (fn1 D1 = D1') /\
                               (!f n. fn1 (D2 f n) = D2' n f (fn0 f))``);
       app hide ["FF1", "FF2"];
       val tm1 = ``(FF1 f (C1 n) = f n) /\ (FF1 f (C2 b) = FF2 f b) /\
                   (FF2 f D1 = f 0) /\ (FF2 f (D2 fo n) = f n + FF1 f fo)``;


       prove_recursive_functions_exist ax tm1;
       new_recursive_definition0 ax "FF1" tm1;

       hide "FF3";
       val tm2 = ``(FF3 (C1 n) = T) /\ (FF3 (C2 b) = F)``;
       prove_recursive_functions_exist ax tm2;
       new_recursive_definition0 ax "FF3" tm2;

       hide "FF4";
       val tm3 = ``(FF4 D1 = 0) /\ (FF4 (D2 f n) = n)``;
       prove_recursive_functions_exist ax tm3;
       new_recursive_definition0 ax "FF4" tm3;

       hide "FF5";
       val tm4 = ``(FF5 D1 = 0)``;
       prove_recursive_functions_exist ax tm4;
       new_recursive_definition0 ax "FF5" tm4;

       hide "FF6";
       val tm5 = ``(FF6 (D2 fo n) = n) /\ (FF7 (C1 n) = n)``;
       prove_recursive_functions_exist ax tm5;
       new_recursive_definition0 ax "FF6" tm5;

       (* HOL Light equivalent *)
       new_type("foo", 0);;
       new_type("bar", 0);;
       new_constant("C1", `:num -> foo`);;
       new_constant("C2", `:bar -> foo`);;
       new_constant("D1", `:bar`);;
       new_constant("D2", `:foo -> num -> bar`);;
       let ax = mk_thm([], `!C1' C2' D1' D2'.
                            ?fn0 fn1.
                               (!n. fn0 (C1 n) = C1' n) /\
                               (!b. fn0 (C2 b) = C2' b (fn1 b)) /\
                               (fn1 D1 = D1') /\
                               (!f n. fn1 (D2 f n) = D2' n f (fn0 f))`);;

       let tm2 = `(FF3 (C1 n) = T) /\ (FF3 (C2 b) = F)`;;
       let fns = prove_recursive_functions_exist ax tm2;;

*)

(*---------------------------------------------------------------------------
     Make a new recursive function definition.
 ---------------------------------------------------------------------------*)

fun new_recursive_definition {name,rec_axiom,def} =
  new_recursive_definition0 rec_axiom name def;

(*---------------------------------------------------------------------------
   Given axiom and the name of the type, return a list of terms
   corresponding to that type's constructors with their arguments.
 ---------------------------------------------------------------------------*)

fun type_constructors_with_args ax name =
  let val (_, body) = strip_exists (#2 (strip_forall (concl ax)))
      fun extract_constructor tm =
         let val (_, eqn) = strip_forall tm
             val (lhs,_) = dest_eq eqn
             val arg = rand lhs
         in
            if fst (dest_type (type_of arg)) = name then SOME arg
            else NONE
         end
  in
    List.mapPartial extract_constructor (strip_conj body)
  end

(* as above but without arguments *)
fun type_constructors ax name =
  map (#1 o strip_comb) (type_constructors_with_args ax name)


local
  fun only_variable_args ty = List.all (not o is_type) (snd (dest_type ty))
  fun only_new types = List.filter only_variable_args types
in
  (* return all of the types defined by an axiom, formerly "new_types". *)
  fun doms_of_tyaxiom ax =
   let val (evs, _) = strip_exists (#2 (strip_forall (concl ax)))
       val candidate_types = map (#1 o dom_rng o type_of) evs
   in
      only_new candidate_types
   end

  (*---------------------------------------------------------------------------
      similarly for an induction theorem, which will be of the form

        !P1 .. PN.
           c1 /\ ... /\ cn ==> (!x. P1 x) /\ (!x. P2 x) ... /\ (!x. PN x)

     Formerly "new_types_from_ind"
   ---------------------------------------------------------------------------*)

  fun doms_of_ind_thm ind =
   let val conclusions = strip_conj(#2(strip_imp(#2(strip_forall(concl ind)))))
       val candidate_types = map (type_of o fst o dest_forall) conclusions
   in
     only_new candidate_types
   end
end

(*---------------------------------------------------------------------------*
 * Define a case constant for a datatype. This is used by TFL's              *
 * pattern-matching translation and are generally useful as replacements     *
 * for "destructor" operations.                                              *
 *---------------------------------------------------------------------------*)

fun num_variant vlist v =
  let val counter = ref 0
      val (Name,Ty) = dest_var v
      val slist = ref (map (fst o dest_var) vlist)
      fun pass str =
         if (mem str (!slist))
         then ( counter := !counter + 1;
                pass (Lib.strcat Name (Lib.int_to_string(!counter))))
         else (slist := str :: !slist; str)
  in
  mk_var(pass Name, Ty)
  end;

fun case_constant_name {type_name} = type_name ^ "_CASE"
fun case_constant_defn_name {type_name} = type_name ^ "_case_def"

fun generate_case_constant_eqns ty clist =
 let val (dty,rty) = Type.dom_rng ty
     val (Tyop,Args) = dest_type dty
     fun mk_cfun ctm (nv,away) =
       let val (c,args) = strip_comb ctm
           val fty = itlist (curry (op -->)) (map type_of args) rty
           val vname = if (length args = 0) then "v" else "f"
           val v = num_variant away (mk_var(vname, fty))
       in (v::nv, v::away)
       end
     val arg_list = rev(fst(rev_itlist mk_cfun clist ([],free_varsl clist)))
     val v = mk_var(case_constant_name{type_name = Tyop},
                    list_mk_fun(dty :: map type_of arg_list, rty))
     fun clause (a,c) = mk_eq(list_mk_comb(v,c::arg_list),
                              list_mk_comb(a, #2 (strip_comb c)))
 in
   list_mk_conj (ListPair.map clause (arg_list, clist))
 end

fun define_case_constant ax =
 let val oktypes = doms_of_tyaxiom ax
     val conjs = strip_conj (#2 (strip_exists (#2 (strip_forall (concl ax)))))
     val newfns = map (rator o lhs o #2 o strip_forall) conjs
     val newtypes = map type_of newfns
     val usethese = mk_set
           (List.filter (fn ty => Lib.mem (#1 (dom_rng ty)) oktypes) newtypes)
     fun mk_defn ty =
      let val (dty,rty) = dom_rng ty
          val name = fst (dest_type dty)
          val cs = type_constructors_with_args ax name
          val eqns = generate_case_constant_eqns ty cs
      in new_recursive_definition
             {name=case_constant_defn_name {type_name = name},
              rec_axiom=ax,
              def=eqns}
      end
 in
  map mk_defn usethese
end

(*---------------------------------------------------------------------------*)
(*       INDUCT_THEN                                                         *)
(*---------------------------------------------------------------------------*)


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
 if is_var body orelse is_const body then REFL else
 if is_abs body then ABS_CONV (BETAS fnn (#2(dest_abs body)))
 else let val (Rator,Rand) = dest_comb body
      in if aconv Rator fnn then BETA_CONV
         else let val cnv1 = BETAS fnn Rator
                  and cnv2 = BETAS fnn Rand
                  fun f (Rator,Rand) = (cnv1 Rator, cnv2 Rand)
              in MK_COMB o (f o dest_comb)
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
   let val (Bvar,Body) = dest_forall g
       and y' = Term.variant (free_varsl (g::A)) y
   in ([(A, subst[Bvar |-> y'] Body)],
       fn [th] => GEN Bvar (INST [y' |-> Bvar] th) | _ => raise Match)
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

local fun ctacs tm =
       if is_conj tm
       then let val tac2 = ctacs (snd(dest_conj tm))
            in fn ttac => CONJUNCTS_THEN2 ttac (tac2 ttac)
            end
       else I
in
fun TACF tm =
 let val (vs,body) = strip_forall tm
 in if is_imp body
    then let val TTAC = ctacs (fst(dest_imp body))
         in fn x => fn ttac =>
              MAP_EVERY (GTAC o Lib.K x) vs THEN DISCH_THEN (TTAC ttac)
         end
    else fn x => fn ttac => Tactical.ALL_TAC
 end
end;

(* ---------------------------------------------------------------------*)
(* Internal function: TACS						*)
(*									*)
(* TACS uses TACF to generate a parameterized list of tactics, one for  *)
(* each conjunct in the hypothesis of an induction theorem.		*)
(*									*)
(* For example, if tm is the hypothesis of the induction theorem for the*)
(* natural numbers---i.e. if:						*)
(*									*)
(*   tm = "P 0 /\ (!n. P n ==> P(SUC n))"				*)
(*									*)
(* then TACS tm yields the parameterized list of tactics:		*)
(*									*)
(*   \x ttac. [TACF "P 0" x ttac; TACF "!n. P n ==> P(SUC n)" x ttac]   *)
(*									*)
(* TACS is a strictly local function, used only in INDUCT_THEN.		*)
(* ---------------------------------------------------------------------*)

fun f (conj1,conj2) = (TACF conj1, TACS conj2)
and TACS tm =
  let val (cf,csf) = f(dest_conj tm) handle HOL_ERR _ => (TACF tm, K(K[]))
  in fn x => fn ttac => cf x ttac::csf x ttac
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
  | GOALS A [t] tm = let val (sg,pf) = t (A,tm) in ([sg],[pf]) end
  | GOALS A (h::t) tm =
      let val (conj1,conj2) = dest_conj tm
          val (sgs,pfs) = GOALS A t conj2
          val (sg,pf) = h (A,conj1)
      in (sg::sgs, pf::pfs)
      end;

(* --------------------------------------------------------------------- *)
(* Internal function: GALPH						*)
(* 									*)
(* GALPH "!x1 ... xn. A ==> B":   alpha-converts the x's to genvars.	*)
(* --------------------------------------------------------------------- *)

local fun rule v =
       let val gv = genvar(type_of v)
       in fn eq => let val th = FORALL_EQ v eq
                   in TRANS th (GEN_ALPHA_CONV gv (rhs(concl th)))
                   end
       end
in
fun GALPH tm =
   let val (vs,hy) = strip_forall tm
   in if (is_imp hy) then Lib.itlist rule vs (REFL hy) else REFL tm
   end
end;

(* ---------------------------------------------------------------------*)
(* Internal function: GALPHA						*)
(* 									*)
(* Applies the conversion GALPH to each conjunct in a sequence.		*)
(* ---------------------------------------------------------------------*)

fun f (conj1,conj2) = (GALPH conj1, GALPHA conj2)
and GALPHA tm =
   let val (c,cs) = f(dest_conj tm)
   in MK_COMB(AP_TERM boolSyntax.conjunction c, cs)
   end handle HOL_ERR _ => GALPH tm

(* --------------------------------------------------------------------- *)
(* INDUCT_THEN : general induction tactic for concrete recursive types.	 *)
(* --------------------------------------------------------------------- *)

local val boolvar = genvar Type.bool
in
fun INDUCT_THEN th =
 let val (Bvar,Body) = dest_forall(concl th)
     val (hy,_) = dest_imp Body
     val bconv = BETAS Bvar hy
     val tacsf = TACS hy
     val v = genvar (type_of Bvar)
     val eta_th = CONV_RULE (RAND_CONV ETA_CONV) (UNDISCH(SPEC v th))
     val (asm,con) = case dest_thm eta_th
                     of ([asm],con) => (asm,con)
                      | _ => raise Match
     val ind = GEN v (SUBST [boolvar |-> GALPHA asm]
                            (mk_imp(boolvar, con))
                            (DISCH asm eta_th))
 in fn ttac => fn (A,t) =>
     let val lam = snd(dest_comb t)
         val spec = SPEC lam (INST_TYPE (Lib.snd(Term.match_term v lam)) ind)
         val (ant,conseq) = dest_imp(concl spec)
         val beta = SUBST [boolvar |-> bconv ant]
                          (mk_imp(boolvar, conseq)) spec
         val tacs = tacsf (fst(dest_abs lam)) ttac
         val (gll,pl) = GOALS A tacs (fst(dest_imp(concl beta)))
         val pf = ((MP beta) o LIST_CONJ) o mapshape(map length gll)pl
     in
       (Lib.flatten gll, pf)
     end
     handle e => raise wrap_exn "Prim_rec" "INDUCT_THEN" e
 end
 handle e => raise wrap_exn "Prim_rec" "INDUCT_THEN" e
end;

(*--------------------------------------------------------------------------
 * Now prove_induction_thm and prove_cases_thm.
 *--------------------------------------------------------------------------*)

infixr 3 ==;
infixr 4 ==>;
infixr 5 \/;
infixr 6 /\;
infixr 3 -->;
infixr 3 THENC;
infixr 3 ORELSEC;

fun (x == y)  = mk_eq(x,y);
fun (x ==> y) = mk_imp(x, y)
fun (x /\ y)  = mk_conj(x,y);
fun (x \/ y)  = mk_disj(x,y);


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

val AP_AND = AP_TERM boolSyntax.conjunction

local val P = mk_var("P", alpha --> bool)
      val v = genvar Type.bool
      and v1 = genvar alpha
      and v2 = genvar alpha
      val ex1P = mk_comb(boolSyntax.exists1,P)
      val th1 = SPEC P (CONV_RULE (X_FUN_EQ_CONV P) EXISTS_UNIQUE_DEF)
      val th2 = CONJUNCT2(UNDISCH(fst(EQ_IMP_RULE(RIGHT_BETA th1))))
      val imp = GEN P (DISCH ex1P (SPECL [v1, v2] th2))
      fun AND (e1,e2) = MK_COMB(AP_AND e1, e2)
      fun beta_conj(conj1,conj2) = (BETA_CONV conj1, BETA_CONV conj2)
      fun conv tm = AND (beta_conj (dest_conj tm))
in
fun UNIQUENESS th =
  let val _ = assert boolSyntax.is_exists1 (concl th)
      val (Rator,Rand) = dest_comb(concl th)
      val theta = [alpha |-> type_of (bvar Rand)]
      val uniq = MP (SPEC Rand (INST_TYPE theta imp)) th
      val red = conv (fst(dest_imp(concl uniq)))
      val (V1,V2) = let val i = Term.inst theta in (i v1,i v2) end
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
   let val (conj1,conj2) = dest_conj tm
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

local val T_AND_T = CONJUNCT1 (SPEC boolSyntax.T AND_CLAUSES)
in
val CONJS_SIMP  =
   let fun simp conv tm =
          let val (conj1,conj2) = dest_conj tm
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
fun T_AND_CONV tm = SPEC (snd(dest_conj tm)) T_AND
end;

(* ---------------------------------------------------------------------*)
(* Internal function: GENL_T						*)
(*									*)
(* GENL_T [x1;...;xn] returns |- (!x1...xn.T) = T			*)
(*									*)
(* ---------------------------------------------------------------------*)

local val t_eq_t = REFL T
in
fun GENL_T [] = t_eq_t
  | GENL_T l =
      let val gen = list_mk_forall(l,T)
          val imp1 = DISCH gen (SPECL l (ASSUME gen))
          val imp2 = DISCH T (GENL l (ASSUME T))
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
      val eq = inst [alpha |-> bool] boolSyntax.equality
      val T_EQ_T = EQT_INTRO(REFL T)
      val T_OR = GEN v (CONJUNCT1 (SPEC v OR_CLAUSES))
      fun DISJ_SIMP tm =
         let val (disj1,disj2) = dest_disj tm
             val eqn = SYM(CONJS_SIMP BETA_CONV disj1)
         in SUBST[v |-> eqn] ((v \/ disj2) == T) (SPEC disj2 T_OR)
         end

in
fun SIMP_CONV tm =
   let val (vs,(lhs,rhs)) = (I ## dest_eq) (strip_forall tm)
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
      val eq = inst [alpha |-> bool] boolSyntax.equality
      val EQ_T = GEN v (CONJUNCT1 (CONJUNCT2 (SPEC v EQ_CLAUSES)))
      fun R_SIMP tm =
         let val (lhs,rhs) = dest_eq tm
         in if aconv rhs T
            then SPEC lhs EQ_T
            else SPECL [lhs, fst(dest_disj rhs)] OR_IMP_THM
         end
in
fun HYP_SIMP tm =
   let val (vs,(lhs,rhs)) = (I##dest_eq) (strip_forall tm)
       val eqsimp = AP_TERM (mk_comb(eq,lhs)) (LIST_BETA_CONV rhs)
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
   let val (vs,(ant,_)) = (I ## dest_imp) (strip_forall tm)
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
       val (Bvar,Body) = dest_forall(rhs(concl eq))
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
      fun gen 0 = []
        | gen n = genvar B::gen (n-1)
      fun mk_fn P ty tm =
         let val (lhs,rhs) = dest_eq(snd(strip_forall tm))
             val c = rand lhs
             val args = snd(strip_comb rhs)
             val vars = filter is_var args
             val n = length(filter (fn t => type_of t = ty) vars)
         in if (n=0) then list_mk_abs (vars, T)
            else let val bools = gen n
                     val term = list_mk_conj bools \/ mk_comb(P,c)
                 in list_mk_abs((bools@vars),term)
                 end
         end
      val LCONV = RATOR_CONV o RAND_CONV
      val conv1 = LCONV(CONJS_SIMP SIMP_CONV) THENC T_AND_CONV
      and conv2 = CONJS_CONV (HYP_SIMP THENC TRY_CONV ANTE_ALL_CONV)
in
fun prove_induction_thm th =
   let val (Bvar,Body) = dest_abs(rand(snd(strip_forall(concl th))))
       val (ty,rty) = case dest_type (type_of Bvar)
                      of (_,[ty, rty]) => (ty,rty)
                       | _ => raise Match
       val inst = INST_TYPE [rty |-> B] th
       val P = mk_primed_var("P", ty --> B)
       and v = genvar ty
       and cases = strip_conj Body
       val uniq = let val (vs,tm) = strip_forall(concl inst)
                      val thm = UNIQUENESS(SPECL vs inst)
                  in GENL vs (SPECL [mk_abs(v,T), P] thm)
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
      and neg = boolSyntax.negation
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
   let val (ant,conseq) = dest_imp(dest_neg tm)
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

local val A = mk_var("A",Type.bool)
      val B = mk_var("B",Type.bool)
      val DE_MORG = GENL [A,B] (CONJUNCT1(SPEC_ALL DE_MORGAN_THM))
      and cnv = BASE_CONV ORELSEC STEP_CONV
      and v1 = genvar Type.bool
      and v2 = genvar Type.bool
in
fun NOT_IN_CONV tm =
   let val (conj1,conj2) = dest_conj(dest_neg tm)
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

local fun EX tm th = EXISTS (mk_exists(tm,concl th),tm) th
      fun CH tm th = CHOOSE (tm,ASSUME(mk_exists(tm,hd(hyp th)))) th
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
   in let val (disj1,disj2) = dest_disj concl_th
          val i1 = rule disj1
          and i2 = DISJS_CHAIN rule (ASSUME disj2)
      in DISJ_CASES th (DISJ1 i1 (concl i2)) (DISJ2 (concl i1) i2)
      end
      handle HOL_ERR _ => MP (DISCH concl_th (rule concl_th)) th
   end


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

fun EXISTS_EQUATION tm th = let
  val (l,r) = boolSyntax.dest_eq tm
  val P = mk_abs(l, concl th)
  val th1 = BETA_CONV(mk_comb(P,l))
  val th2 = ISPECL [P, r] JRH_INDUCT_UTIL
  val th3 = EQ_MP (SYM th1) th
  val th4 = GEN l (DISCH tm th3)
in
  MP th2 th4
end


local
  fun margs n s avoid [] = []
    | margs n s avoid (h::t) =
      let val v = variant avoid
                          (mk_var(s^(Int.toString n),h))
      in
        v::margs (n + 1) s (v::avoid) t
      end
  fun make_args s avoid tys =
      if length tys = 1 then
        [variant avoid (mk_var(s, hd tys))]
        handle _ => raise ERR "make_args" ""
      else margs 0 s avoid tys


  fun mk_exclauses x rpats = let
    (* order of existentially quantified variables is same order
       as they appear as arguments to the constructor *)
    val xts = map (fn t =>
                      list_mk_exists(#2 (strip_comb t), mk_eq(x,t))) rpats
  in
    mk_abs(x,list_mk_disj xts)
  end
  fun prove_triv tm = let
    val (evs,bod) = strip_exists tm
    val (l,r) = dest_eq bod
    val (lf,largs) = strip_comb l
    val (rf,rargs) = strip_comb r
    val _ = (aconv lf rf) orelse raise ERR "prove_triv" ""
    val ths = map (ASSUME o mk_eq) (zip rargs largs)
    val th1 = rev_itlist (C (curry MK_COMB)) ths (REFL lf)
  in
    itlist EXISTS_EQUATION (map concl ths) (SYM th1)
  end
  fun prove_disj tm =
      if is_disj tm then let
          val (l,r) = dest_disj tm
        in
          DISJ1 (prove_triv l) r
          handle HOL_ERR _ => DISJ2 l (prove_disj r)
        end
      else prove_triv tm
  fun prove_eclause tm = let
    val (avs,bod) = strip_forall tm
    val ctm = if is_imp bod then rand bod else bod
    val cth = prove_disj ctm
    val dth = if is_imp bod then DISCH (lhand bod) cth else cth
  in
    GENL avs dth
  end
  fun CONJUNCTS_CONV c tm =
      if is_conj tm then BINOP_CONV (CONJUNCTS_CONV c) tm else c tm
  fun prove_cases_thm0 th = let
    val (_,bod) = strip_forall(concl th)
    val cls = map (snd o strip_forall) (conjuncts(lhand bod))
    val pats = map (fn t => if is_imp t then rand t else t) cls
    val spats = map dest_comb pats
    val preds = itlist (op_insert aconv o fst) spats []
    val rpatlist = map
                     (fn pr => map snd (filter (fn (p,x) => aconv p pr) spats))
                     preds
    val xs = make_args "x" (free_varsl pats) (map (type_of o hd) rpatlist)
    val xpreds = map2 mk_exclauses xs rpatlist
    fun double_name th = let
      fun rename t = let
        val (v, _) = dest_forall t
        val (vnm,ty) = dest_var v
      in
        RAND_CONV (ALPHA_CONV (mk_var(vnm^vnm, ty))) t
      end
    in
      DISCH_ALL (CONV_RULE (CONJUNCTS_CONV rename) (UNDISCH th))
    end
    val ith = BETA_RULE
                (Thm.INST (ListPair.map (fn (x,p) => p |-> x) (xpreds, preds))
                          (double_name (SPEC_ALL th)))
    val eclauses = conjuncts(fst(dest_imp(concl ith)))
  in
    MP ith (end_itlist CONJ (map prove_eclause eclauses))
  end
in
fun prove_cases_thm ind0 = let
  val ind = CONV_RULE
              (STRIP_QUANT_CONV (RATOR_CONV (RAND_CONV
                (CONJUNCTS_CONV (REDEPTH_CONV RIGHT_IMP_FORALL_CONV))))) ind0
  val basic_thm = prove_cases_thm0 ind
  val oktypes = doms_of_ind_thm ind
in
  List.filter
    (fn th => Lib.mem (type_of (fst(dest_forall (concl th)))) oktypes)
    (CONJUNCTS basic_thm)
end

end; (* prove_cases_thm *)

(*---------------------------------------------------------------------------
    Proving case congruence:

     |- (M = M') /\
        (!x1,...,xk. (M' = C1 x1..xk) ==> (f1 x1..xk = f1' x1..xk))
         /\ ... /\
        (!x1,...,xj. (M' = Cn x1..xj) ==> (fn x1..xj = fn' x1..xj))
        ==>
       (ty_case f1..fn M = ty_case f1'..fn' M')

 ---------------------------------------------------------------------------*)

fun case_cong_term case_def =
 let val clauses = (strip_conj o concl) case_def
     val clause1 = Lib.trye hd clauses
     val left = (#1 o dest_eq o #2 o strip_forall) clause1
     val (c, allargs) = strip_comb left
     val (tyarg, nonty_args) =
         case allargs of h::t => (h,t)
                       | _ => raise Fail "case_cong_term: should never happen"
     val ty = type_of tyarg
     val allvars = all_varsl clauses
     val M = variant allvars (mk_var("M", ty))
     val M' = variant (M::allvars) (mk_var("M",ty))
     val lhsM = list_mk_comb(c, M::nonty_args)
     fun mk_clause clause =
       let val (lhs,rhs) = (dest_eq o #2 o strip_forall) clause
           val func = (#1 o strip_comb) rhs
           val (Name,Ty) = dest_var func
           val func' = variant allvars (mk_var(Name^"'", Ty))
           val capp = hd (#2 (strip_comb lhs))
           val (constr,xbar) = strip_vars capp
       in (func',
           list_mk_forall
           (xbar, mk_imp(mk_eq(M',capp),
                         mk_eq(list_mk_comb(func,xbar),
                               list_mk_comb(func',xbar)))))
       end
     val (funcs',clauses') = unzip (map mk_clause clauses)
 in
 mk_imp(list_mk_conj(mk_eq(M, M')::clauses'),
        mk_eq(lhsM, list_mk_comb(c,M'::funcs')))
 end;

(*---------------------------------------------------------------------------*
 *                                                                           *
 *        A, v = M[x1,...,xn] |- N                                           *
 *  ------------------------------------------                               *
 *     A, ?x1...xn. v = M[x1,...,xn] |- N                                    *
 *                                                                           *
 *---------------------------------------------------------------------------*)

fun EQ_EXISTS_LINTRO (thm,(vlist,theta)) =
  let val veq = case filter (can dest_eq) (hyp thm)
                of [veq] => veq
                 | _ => raise Match
      fun CHOOSER v (tm,thm) =
        let val w = (case (subst_assoc (aconv v) theta)
                      of SOME w => w
                       | NONE => v)
            val ex_tm = mk_exists(w,tm)
        in (ex_tm, CHOOSE(w, ASSUME ex_tm) thm)
        end
  in snd(itlist CHOOSER vlist (veq,thm))
  end;


fun OKform case_def =
  let val clauses = (strip_conj o concl) case_def
      val left = (fst o dest_eq o #2 o strip_forall) (Lib.trye hd clauses)
      val opvars = tl (#2 (strip_comb left))
      fun rhs_head c = fst(strip_comb(rhs(snd(strip_forall c))))
      val rhs_heads = map rhs_head clauses
      fun check [] = true
        | check ((x,y)::rst) = aconv x y andalso check rst
  in
     check (zip opvars rhs_heads)
  end

fun case_cong_thm nchotomy case_def =
 let open Psyntax
     val _ = assert OKform case_def
     val clause1 =
       let val c = concl case_def in fst(dest_conj c) handle HOL_ERR _ => c end
     val V = tl (snd (strip_comb (lhs (#2 (strip_forall clause1)))))
     val gl = case_cong_term case_def
     val (ant,conseq) = dest_imp gl
     val imps = CONJUNCTS (ASSUME ant)
     val M_eq_M' = hd imps
     val (M, M') = dest_eq (concl M_eq_M')
     fun get_asm tm = (fst o dest_imp o #2 o strip_forall) tm handle _ => tm
     val case_assms = map (ASSUME o get_asm o concl) imps
     val (lconseq, rconseq) = dest_eq conseq
     val lconseq_thm = SUBST_CONV [M |-> M_eq_M'] lconseq lconseq
     val lconseqM' = rhs(concl lconseq_thm)
     val nchotomy' = ISPEC M' nchotomy
     val disjrl = map ((I##rhs) o strip_exists)	(strip_disj (concl nchotomy'))
     val V' = tl(snd(strip_comb rconseq))
     val theta = map2 (fn v => fn v' => {redex=v,residue=v'}) V V'
     fun zot (p as (icase_thm, case_def_clause)) (iimp,(vlist,disjrhs)) =
         let
           val c = case_def_clause |> concl |> lhs |> strip_comb |> #1
           fun AP_THMl tl th = List.foldl (fn (v,th) => AP_THM th v) th tl
           val lth =
                 icase_thm |> AP_TERM c |> AP_THMl V |> C TRANS case_def_clause
           val rth = TRANS (icase_thm |> AP_TERM c |> AP_THMl V')
                           (INST theta case_def_clause)
           val theta = Term.match_term disjrhs
                     ((rhs o fst o dest_imp o #2 o strip_forall o concl) iimp)
           val th = MATCH_MP iimp icase_thm
           val th1 = TRANS lth th
         in
           (TRANS th1 (SYM rth), (vlist, #1 theta))
         end
     val thm_substs = map2 zot
                       (zip (Lib.trye tl case_assms)
                            (map SPEC_ALL (CONJUNCTS case_def)))
                       (zip (Lib.trye tl imps) disjrl)
     val aag = map (TRANS lconseq_thm o EQ_EXISTS_LINTRO) thm_substs
 in
   GENL (M::M'::V) (DISCH_ALL (DISJ_CASESL nchotomy' aag))
 end
 handle HOL_ERR _ => raise ERR "case_cong_thm" "construction failed";



(* The standard versions of these (in Conv) check that the term being
   manipulated is actually an equality.  I want a slightly more efficient
   version *)
val LHS_CONV = RATOR_CONV o RAND_CONV
val RHS_CONV = RAND_CONV


(* =====================================================================*)
(* PROOF THAT CONSTRUCTORS OF RECURSIVE TYPES ARE ONE-TO-ONE		*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* Internal function: list_variant					*)
(*									*)
(* makes variants of the variables in l2 such that they are all not in	*)
(* l1 and are all different.						*)
(* ---------------------------------------------------------------------*)

fun list_variant l1 [] = []
  | list_variant l1 (h::t) =
       let val v = variant l1 h
       in v::(list_variant (v::l1) t)
       end;

fun mk_subst2 [] [] = []
  | mk_subst2 (a::L1) (b::L2) = (b |-> a)::mk_subst2 L1 L2
  | mk_subst2 _ _ = raise Match;


(* ----------------------------------------------------------------------*)
(* Internal function: prove_const_one_one.				 *)
(*									 *)
(* This function proves that a single constructor of a recursive type is *)
(* one-to-one (it is called once for each appropriate constructor). The  *)
(* theorem input, th, is the characterizing theorem for the recursive 	 *)
(* type in question.  The term, tm, is the defining equation for the 	 *)
(* constructor in question, taken from the body of the theorem th.	 *)
(*									 *)
(* For example, if:							 *)
(*									 *)
(*  th = |- !x f. ?! fn. (fn[] = x) /\ (!h t. fn(CONS h t) = f(fn t)h t) *)
(*									 *)
(* and									 *)
(*									 *)
(*  tm = "!h t. fn(CONS h t) = f(fn t)h t"				 *)
(*									 *)
(* then prove_const_one_one th tm yields:				 *)
(*								 	 *)
(*  |- !h t h' t'. (CONS h t = CONS h' t') = (h = h') /\ (t = t')	 *)
(*									 *)
(* ----------------------------------------------------------------------*)

(* Basic strategy is to use a function
      f h' t' (C h t) = (h = h') /\ (t = t')
   Then, if we assume
               C h t = C h' t'
       f h t (C h t) = f h t (C h' t')
  (h = h) /\ (t = t) = (h = h') /\ (t = t')
                   T = (h = h') /\ (t = t')
  so
        (C h t = C h' t') ==> (h = h') /\ (t = t')
  in the other direction, we just rewrite (C h t) with the equalities and
  get the desired equation.
*)

fun prove_const_one_one th tm = let
  val (vs,(lhs,_)) = (I ## dest_eq)(strip_forall tm)
  val C = rand lhs
  val funtype =
    List.foldr (fn (tm, ty) => Type.-->(type_of tm, ty))
    (Type.-->(type_of C, Type.bool)) vs
  val f = genvar funtype
  val vvs = list_variant vs vs
  val fn_body = list_mk_conj(ListPair.map op== (vs, vvs))
  val f_ap_vs = list_mk_comb(f, vs)
  val C' = subst (mk_subst2 vvs vs) C
  val eqn =
    list_mk_forall(vs @ vvs, mk_comb(f_ap_vs, C') == fn_body)
  val fn_exists_thm = prove_recursive_functions_exist th eqn
  val eqn_thm = ASSUME (snd (dest_exists (concl fn_exists_thm)))
  val C_eq_C'_t = C == C'
  val C_eq_C' = ASSUME C_eq_C'_t
  val fC_eq_fC' = AP_TERM f_ap_vs C_eq_C'
  val expandedfs = CONV_RULE (LHS_CONV (REWR_CONV eqn_thm) THENC
                              RHS_CONV (REWR_CONV eqn_thm)) fC_eq_fC'
  val imp1 =
    CHOOSE(f, fn_exists_thm) (DISCH C_eq_C'_t (REWRITE_RULE [] expandedfs))

  val eqns = CONJUNCTS (ASSUME fn_body)
  val rewritten = REWRITE_CONV eqns C
  val imp2 = DISCH fn_body rewritten
in
  GENL vs (GENL vvs (IMP_ANTISYM_RULE imp1 imp2))
end

(* ----------------------------------------------------------------------*)
(* prove_constructors_one_one : prove that the constructors of a given	 *)
(* concrete recursive type are one-to-one. The input is a theorem of the *)
(* form returned by define_type.					 *)
(*									 *)
(* EXAMPLE: 								 *)
(*									 *)
(* Input: 								 *)
(* 									 *)
(*    |- !x f. ?! fn. (fn[] = x) /\ (!h t. fn(CONS h t) = f(fn t)h t) 	 *)
(*									 *)
(* Output:								 *)
(*									 *)
(*    |- !h t h' t'. (CONS h t = CONS h' t') = (h = h') /\ (t = t')	 *)
(* ----------------------------------------------------------------------*)

local
  (* given an equivalence relation R, partition a list into a list of lists
     such that everything in each list is related to each other *)
  (* preserves the order of the elements within each partition with
     respect to the order they were given in the original list *)
  fun partition R l = let
    fun partition0 parts [] = parts
      | partition0 parts (x::xs) = let
          fun srch_parts [] = [[x]]
            | srch_parts (p::ps) = if R x (hd p) then (x::p)::ps
                                   else p::(srch_parts ps)
        in
          partition0 (srch_parts parts) xs
        end
  in
    map List.rev (partition0 [] l)
  end
in

  fun prove_constructors_one_one th = let
    val all_eqns =
      strip_conj (snd (strip_exists(snd(strip_forall(concl th)))))
    val axtypes = doms_of_tyaxiom th
    fun eqn_type eq = type_of (rand (lhs (#2 (strip_forall eq))))
    fun same_domain eq1 eq2 = eqn_type eq1 = eqn_type eq2
    fun prove_c11_for_type eqns = let
      val funs =
        List.filter (fn tm => is_comb(rand(lhs(snd(strip_forall tm)))))
        eqns
    in
      if null funs then NONE
      else
        SOME (LIST_CONJ (map (prove_const_one_one th) funs))
        handle HOL_ERR _ =>
          raise ERR "prove_constructors_one_one" ""
    end
    fun maybe_prove eqns =
      if Lib.mem (eqn_type (hd eqns)) axtypes then
        SOME (prove_c11_for_type eqns)
      else NONE
  in
    List.mapPartial maybe_prove (partition same_domain all_eqns)
  end


(* =====================================================================*)
(* DISTINCTNESS OF VALUES FOR EACH CONSTRUCTOR				*)
(* =====================================================================*)

(* ---------------------------------------------------------------------*)
(* prove_constructors_distinct : prove that the constructors of a given	*)
(* recursive type yield distinct (non-equal) values.			*)
(*									*)
(* EXAMPLE: 								*)
(*									*)
(* Input: 								*)
(* 									*)
(*    |- !x f. ?! fn. (fn[] = x) /\ (!h t. fn(CONS h t) = f(fn t)h t) 	*)
(* 									*)
(* Output:								*)
(* 									*)
(*    |- !h t. ~([] = CONS h t)						*)
(* ---------------------------------------------------------------------*)

(* Basic strategy is to define a function over the type such that
      f (C1 ...) = 0
      f (C2 ...) = 1
      f (C3 ...) = 2
      ...
      f (Cn ...) = n
   However, we want to do this by avoiding the use of numbers.  So, we
   encode the numbers on the RHS above as functions over booleans.  In
   particular, the type of the function will be
      bool ^ log n -> bool
   The encoding of the function will be such that it is true iff the
   arguments form the encoding of the number it is supposed to represent.
   If we have 10 constructors, log n will be 4, and the encoding of 5 will
   be
       \b4 b3 b2 b1. b4 /\ ~b3 /\ b2 /\ ~b1
   The encoding is MSB to the left.

   When function f is defined, it is then easy to distinguish any
   two constructors Ci and Cj.
       Assume           (Ci xn) = (Cj yn)
       then           f (Ci xn) = f (Cj yn)            (Leibnitz)
       so     f (Ci xn) [| i |] = f (Cj yn) [| i |]      (ditto)
   But f is constructed in such a way that the term on the left will be
   true, while that on the right will be false.  We derive a contradiction
   and conclude that the original assumption was false.
*)

local
  val bn0 = mk_var("b0", Type.bool)
  val bn1 = mk_var("b1", Type.bool)
  val bn2 = mk_var("b2", Type.bool)
  val bn3 = mk_var("b3", Type.bool)
  val bn4 = mk_var("b4", Type.bool)
  val bn5 = mk_var("b5", Type.bool)
  val bn6 = mk_var("b6", Type.bool)
  val bn7 = mk_var("b7", Type.bool)
  val bn8 = mk_var("b8", Type.bool)
  val bn9 = mk_var("b9", Type.bool)
in
  fun bn n =
    case n of
      0 => bn0
    | 1 => bn1
    | 2 => bn2
    | 3 => bn3
    | 4 => bn4
    | 5 => bn5
    | 6 => bn6
    | 7 => bn7
    | 8 => bn8
    | 9 => bn9
    | x => mk_var("b"^Int.toString x, Type.bool)
end


(* encode bv nb n
     returns a list of terms encoding the number n in nb bits.  If bv is
     true, then the terms are successive boolean variables.  If bv is false
     then the terms are all either T or ~T.
   encode true nb n
     is used to produce the body of the functions encoding for n
   encode false nb n
     is used to produce the arguments that the functions are applied to.
*)
fun encode bv numbits n =
  if numbits <= 0 then []
  else let
    val bn0 = if bv then bn numbits else T
    val bn = if n mod 2 = 0 then mk_neg bn0 else bn0
  in
    bn::encode bv (numbits - 1) (n div 2)
  end

(*
  mk_num generates the function corresponding to number n.  The abstraction
  will have numbits bound variables.
*)
fun mk_num numbits n = let
  val vars = List.tabulate(numbits, (fn n => bn (n + 1)))
in
  list_mk_abs(List.rev vars, list_mk_conj(encode true numbits n))
end

(* calculates how many bits are required to represent a number *)
fun rounded_log n = if n <= 1 then 0 else 1 + rounded_log ((n + 1) div 2)

fun RATORn_CONV n c t = if n <= 0 then c t
                        else RATOR_CONV (RATORn_CONV (n - 1) c) t

fun nBETA_CONV dpth n =
  if n <= 0 then REFL
  else
    RATORn_CONV (dpth - 1) BETA_CONV THENC nBETA_CONV (dpth - 1) (n - 1)

(* !x. ~T /\ x = ~T *)
val notT_and = prove(gen_all ((mk_neg T /\ bn 1) == mk_neg T),
                              REWRITE_TAC []);
(* !x. ~~T /\ x = x *)
val notnotT_and = prove(gen_all (((mk_neg (mk_neg T)) /\ bn 1) == bn 1),
                        REWRITE_TAC []);
(* !x. T /\ x = x *)
val T_and = prove(gen_all (T /\ bn 1 == bn 1), REWRITE_TAC []);
(* (T = ~T) = F *)
val T_eqF = prove((T == mk_neg T) == F, REWRITE_TAC []);
(* ~~T = T *)
val notnotT = prove(mk_neg (mk_neg T) == T, REWRITE_TAC []);
(* ~T = F *)
val notT = prove(mk_neg T == F, REWRITE_TAC []);

(* A special purpose conv to move along a conjunction of T's, ~T's and ~~T's,
   simplifying it to a single atom as quickly as possible.
   Might be possible to improve it by looking for an instance of ~T, and
   then doing the two rewrites required to push this to the top. *)
fun simp_conjs t =
  if is_conj t then let
    val (conj1, conj2) = dest_conj t
  in
    if is_neg conj1 then
      if is_neg (dest_neg conj1) then
        (REWR_CONV notnotT_and THENC simp_conjs) t
      else
        REWR_CONV notT_and t
    else
      (REWR_CONV T_and THENC simp_conjs) t
  end
  else REFL t

fun to_true t = if is_neg t then REWR_CONV notnotT t else REFL t

fun prove_ineq nb f fc1 fc2 c1 c20 c1n = let
  val c1_vars = #2 (strip_comb c1)
  val (c2_t, c20_vars) = strip_comb c20
  val c2_vars = list_variant c1_vars c20_vars
  val c2 = list_mk_comb (c2_t, c2_vars)
  val c1c2_eqt = c1 == c2
  val c1_eq_c2 = ASSUME c1c2_eqt
  val fc1_eq_fc2 = AP_TERM f c1_eq_c2
  fun fold (arg, thm) = AP_THM thm arg
  val fc1_args_eq_fc2_args = List.foldl fold fc1_eq_fc2 c1n
  val expand_left =
    CONV_RULE (LHS_CONV (RATORn_CONV nb (REWR_CONV fc1))) fc1_args_eq_fc2_args
  val expand_right =
    CONV_RULE (RHS_CONV (RATORn_CONV nb (REWR_CONV fc2))) expand_left
  val beta_left = CONV_RULE (LHS_CONV (nBETA_CONV nb nb)) expand_right
  val beta_right = CONV_RULE (RHS_CONV (nBETA_CONV nb nb)) beta_left
  val result0 =
    CONV_RULE (LHS_CONV (simp_conjs THENC to_true) THENC RHS_CONV simp_conjs)
    beta_right
  val result1 = DISCH c1c2_eqt (EQ_MP T_eqF result0)
  val result = GEN_ALL (MATCH_MP IMP_F result1)
in
  result
end

(* The type of numbers represented using nb many bits *)

fun numtype nb = if nb <= 1 then bool --> bool else bool --> numtype (nb - 1)

fun generate_fn_term nb ty = genvar (ty --> numtype nb)

fun generate_eqns nb ctrs f =
 let fun recurse n [] = []
       | recurse n (x::xs) =
         (mk_comb(f, x) == mk_num nb n):: recurse (n + 1) xs
 in recurse 0 ctrs
 end

fun number nb lst =
let fun number0 _ [] = []
      | number0 n (x::xs) = (encode false nb n,x)::number0 (n+1) xs
in
  number0 0 lst
end

fun app_triangle f [] = []
  | app_triangle f [x] = []
  | app_triangle f (x::xs) = map (fn y => f (x, y)) xs @ app_triangle f xs

fun ctrs_with_args clauses =
 let fun get_ctr tm = rand (lhs (#2 (strip_forall tm)))
 in map get_ctr clauses
 end

fun prove_constructors_distinct thm = let
  val all_eqns = strip_conj(snd(strip_exists(snd(strip_forall(concl thm)))))
  val axtypes = doms_of_tyaxiom thm
  fun eqn_type eq = type_of (rand (lhs (#2 (strip_forall eq))))
  fun same_domain eq1 eq2 = eqn_type eq1 = eqn_type eq2
  fun prove_cd_for_type eqns = let
    val ctrs = ctrs_with_args eqns
    val nb = rounded_log (length ctrs)
  in
    if nb = 0 then NONE
    else let
      val f = generate_fn_term nb (type_of (hd ctrs))
      val eqns = generate_eqns nb ctrs f
      val fn_defn = list_mk_conj eqns
      val fn_exists = prove_recursive_functions_exist thm fn_defn
      val fn_thm = ASSUME (snd (dest_exists (concl fn_exists)))
      val eqn_thms = CONJUNCTS fn_thm
      val ctrs_with_eqns_and_numbers =
        number nb (ListPair.zip (ctrs, eqn_thms))
      fun prove_result ((c1n, (c1, fc1)), (c2n, (c2, fc2))) =
        prove_ineq nb f fc1 fc2 c1 c2 c1n
      val thms = app_triangle prove_result ctrs_with_eqns_and_numbers
      val thm = LIST_CONJ thms
    in
      SOME (CHOOSE (f, fn_exists) thm)
    end
  end
  fun maybe_prove_cd_for_type eqns =
    let val ctrs = ctrs_with_args eqns
    in if Lib.mem (type_of (hd ctrs)) axtypes
          then SOME (prove_cd_for_type eqns)
          else NONE
    end
in
  List.mapPartial maybe_prove_cd_for_type (partition same_domain all_eqns)
end

end (* local where partition is defined *)

(*---------------------------------------------------------------------------

          Test routines for distinctness proofs.

  load "Define_type";
  fun gen_type n = let
    val name = "foo"^Int.toString n
    val fixities = List.tabulate(n, fn _ => Prefix)
    fun clause n = let
      val C = "C"^Int.toString n
    in
      if n = 0 then  "C0 of bool => 'a"
      else C ^ " of bool => 'a => " ^name
    end
    fun sepby sep [] = []
      | sepby sep [x]= [x]
      | sepby sep (x::xs) = x::sep::sepby sep xs
    val clauses = sepby " | " (List.tabulate(n, clause))
    val spec = String.concat (name::" = "::clauses)
  in
    Define_type.define_type { fixities = fixities,
                              type_spec = [QUOTE spec],
                              name = name }
  end;
  val foo5 = gen_type 5;
  val foo10 = gen_type 10;
  val foo20 = gen_type 20;
  Lib.time prove_constructors_distinct foo5;
  Lib.time prove_constructors_distinct foo10;
  Lib.time prove_constructors_distinct foo20;
  (* tests seem to indicate that the code above is roughly 1.5 times
     slower than the original code by Tom Melham.  This is probably
     acceptable given that it is now independent of the theory of
     numbers *)

 ---------------------------------------------------------------------------*)

fun usefuls cs = let
  fun cfvs c = FVL (#1 (strip_forall c)) empty_tmset
  val vs = foldl (fn (c,s) => HOLset.intersection(cfvs c, s))
                 (cfvs (hd cs))
                 (tl cs)
  val vs_l = HOLset.listItems vs
  val (_, eqn1) = strip_forall (hd cs)
  val (const,args) = strip_comb (lhs eqn1)
  val (arg1_ty, casefs) = case args of
                              h::t => (type_of h,t)
                            | _ => raise mk_HOL_ERR "Prim_rec" "prove_case_rand_thm"
                                         "Case constant theorem has too few arguments"
  val v = variant vs_l (mk_var("x", arg1_ty))
in
  (const, list_mk_comb(const, v::tl args), casefs, vs_l, v)
end

fun prove_case_rand_thm {nchotomy, case_def} = let
  val cs = strip_conj (concl case_def)
  val (const,t,casefs,vs_l,v) = usefuls cs
  val tyvs = foldl (fn (v,s) => HOLset.addList(s, type_vars_in_term v))
                   (HOLset.empty Type.compare)
                   vs_l
  fun foldthis (sv, acc) = if acc = sv then mk_vartype(dest_vartype acc ^ "1")
                           else acc
  val fresh_tyvar = HOLset.foldl foldthis alpha tyvs
  val f = variant vs_l (mk_var("f", type_of t --> fresh_tyvar))
  val ctor_args = map (fn c => c |> strip_forall |> #2 |> lhs |> strip_comb
                                 |> #2 |> hd |> strip_comb |> #2)
                      cs
  val new_lhs = mk_comb(f, t)
  val cfs' =
      ListPair.map
        (fn (cf, args) => list_mk_abs(args, mk_comb(f, list_mk_comb(cf, args))))
        (casefs, ctor_args)
  val const' = inst [#2 (strip_fun (type_of const)) |-> fresh_tyvar] const
  val rhs' = list_mk_comb(const', v::cfs')
in
  prove(mk_eq(mk_comb(f,t),rhs'),
        STRUCT_CASES_TAC (ISPEC v nchotomy) THEN
        PURE_REWRITE_TAC [case_def] THEN BETA_TAC THEN
        PURE_REWRITE_TAC [EQT_INTRO (SPEC_ALL EQ_REFL)])
end

(* prove a theorem of the form
     ty_CASE x f1 .. fn :bool <=>
       (?a1 .. ai. x = ctor1 a1 .. ai /\ f1 a1 .. ai) \/
       (?b1 .. bj. x = ctor2 b1 .. bj /\ f2 b1 .. bj) \/
       ...
*)
fun prove_case_elim_thm {case_def,nchotomy} = let
  val cs = strip_conj (concl case_def)
  val (const,t0,casefs0,vs_l,v) = usefuls cs
  val casefs = map (inst [type_of t0 |-> bool]) casefs0
  val t = inst [type_of t0 |-> bool] t0
  val t_thm = ASSUME t
  val nch = SPEC v nchotomy
  val disjs0 = strip_disj (concl nch)
  fun mapthis (ex_eqn, cf) = let
    val (vs, eqn) = strip_exists ex_eqn
  in
    list_mk_exists(vs, mk_conj(eqn, list_mk_comb(cf,vs)))
  end
  val _ = length casefs = length disjs0 orelse
          raise mk_HOL_ERR "Prim_rec" "prove_case_elim_thm"
                "case_def and nchotomy theorem don't match up"
  val disjs = ListPair.map mapthis (disjs0,casefs)
  fun prove_case_from_eqn ext = let
    (* ext is of the form ``?a1 .. ai. x = ctor1 a1 .. ai /\ f1 a1 .. ai`` *)
    val (vs,body) = strip_exists ext
    val body_th = ASSUME body
    val res0 = EQT_ELIM (PURE_REWRITE_CONV [body_th,case_def] t)
    fun foldthis (v,(ext,th)) = let
      val ex' = mk_exists(v,ext)
    in
      (ex', CHOOSE (v,ASSUME ex') th)
    end
  in
    List.foldr foldthis (body,res0) vs
  end
  val ths = map (#2 o prove_case_from_eqn) disjs
  val (ds, d) = front_last disjs
  fun disj_recurse ds ths =
      case (ds, ths) of
          ([d], [th]) => (d, th)
        | (d::ds, th::ths) =>
          let
            val (d2, th2) = disj_recurse ds ths
            val t = mk_disj(d,d2)
          in
            (t, DISJ_CASES (ASSUME t) th th2)
          end
        | _ => raise Fail "prove_case_elim_thm: can't happen"
  val (_, case1) = disj_recurse disjs ths

  fun prove_exists d = let
    val (vs, body) = strip_exists d
    val (c1, c2) = dest_conj body
    val body_th = CONJ (ASSUME c1) (ASSUME c2)
    val ex_thm =
        List.foldr (fn (v, th) => EXISTS(mk_exists(v,concl th),v) th)
                   body_th vs
    val elim =
        EQ_MP (PURE_REWRITE_CONV [ASSUME c1, case_def] t) t_thm
  in
    PROVE_HYP elim ex_thm
  end
  val exists_thms = map prove_exists disjs
  fun mkholes ds =
      case ds of
          [] => []
        | d::t => (NONE::map SOME t) ::
                  (map (cons (SOME d)) (mkholes t))
  val holes = mkholes (map concl exists_thms)
  fun holemerge (th, holedlist) =
      case holedlist of
          [NONE] => th
        | NONE::rest => DISJ1 th (list_mk_disj (map valOf rest))
        | SOME t::rest =>
          DISJ2 t (holemerge (th, rest))
        | [] => raise Fail "Can't happen"
  val eqconcls =
      ListPair.map (DISCH t o holemerge) (exists_thms, holes)
  fun existentialify_asm th = let
    val eq = hd (hyp th)
    val (_, vs) = eq |> rhs |> strip_comb
    fun foldthis (v, (ext, th)) = let
      val ext' = mk_exists(v,ext)
    in
      (ext', CHOOSE(v, ASSUME ext') th)
    end
  in
    #2 (List.foldr foldthis (eq, th) vs)
  end
  val existentialified_asms = map existentialify_asm eqconcls
in
  IMP_ANTISYM_RULE
    (PROVE_HYP nch (#2 (disj_recurse disjs0 existentialified_asms)))
    (DISCH_ALL case1)
end

fun prove_case_eq_thm (rcd as {case_def, nchotomy}) = let
  val elim = prove_case_elim_thm rcd
  val rand_thm = prove_case_rand_thm rcd
  val fvar = rator (lhs (concl rand_thm))
  val (dom, rng) = dom_rng (type_of fvar)
  val fvs = free_vars (concl rand_thm)
  val v = variant fvs (mk_var("v", dom))
  val v' = variant (v::fvs) v
  val rand_thm' = rand_thm |> INST_TYPE [rng |-> bool]
                           |> INST [inst [rng |-> bool] fvar |->
                                    mk_abs(v', mk_eq(v', v))]
                           |> BETA_RULE
in
  rand_thm' |> CONV_RULE (RAND_CONV (REWR_CONV elim))
            |> BETA_RULE
end




end; (* Prim_rec *)
