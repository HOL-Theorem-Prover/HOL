structure Defn :> Defn =
struct

open HolKernel Parse boolLib;
open pairLib Rules wfrecUtils Pmatch Induction DefnBase;

type thry   = TypeBasePure.typeBase
type proofs = Manager.proofs
type absyn  = Absyn.absyn;

val ERR = mk_HOL_ERR "Defn";
val ERRloc = mk_HOL_ERRloc "Defn";

val monitoring = ref false;

(* Interactively:
  val const_eq_ref = ref (!Defn.const_eq_ref);
*)
val const_eq_ref = ref Conv.NO_CONV;

(*---------------------------------------------------------------------------
      Miscellaneous support
 ---------------------------------------------------------------------------*)

fun enumerate l = map (fn (x,y) => (y,x)) (Lib.enumerate 0 l);

fun drop [] x = x
  | drop (_::t) (_::rst) = drop t rst
  | drop _ _ = raise ERR "drop" "";

fun variants FV vlist =
  fst
    (rev_itlist
       (fn v => fn (V,W) =>
           let val v' = variant W v in (v'::V, v'::W) end) vlist ([],FV));

fun make_definition thry s tm = (new_definition(s,tm), thry)

fun head tm = head (rator tm) handle HOL_ERR _ => tm;

fun all_fns eqns =
  op_mk_set aconv (map (head o lhs o #2 o strip_forall) (strip_conj eqns));

fun dest_hd_eqn eqs =
  let val hd_eqn = if is_conj eqs then fst(dest_conj eqs) else eqs
      val (lhs,rhs) = dest_eq (snd(strip_forall hd_eqn))
  in (strip_comb lhs, rhs)
  end;

fun dest_hd_eqnl (hd_eqn::_) =
  let val (lhs,rhs) = dest_eq (snd (strip_forall (concl hd_eqn)))
  in (strip_comb lhs, rhs)
  end
  | dest_hd_eqnl _ = raise Match

fun extract_info constset db =
    let open TypeBasePure
        fun foldthis (tyinfo, (R, C)) =
            if List.exists
                (fn x => same_const (case_const_of tyinfo) x
                         handle HOL_ERR _ => false) constset then
              (case_def_of tyinfo::R, case_cong_of tyinfo::C)
            else (R, C)
      val (rws,congs) = foldl foldthis ([], []) (listItems db)
    in {case_congs=congs, case_rewrites=rws}
    end;

(*---------------------------------------------------------------------------
    Support for automatically building names to store definitions
    (and the consequences thereof) with in the current theory. Somewhat
    ad hoc, but I don't know a better way!
 ---------------------------------------------------------------------------*)

val ind_suffix = ref "_ind";
val def_suffix = boolLib.def_suffix

fun indSuffix s     = (s ^ !ind_suffix);
fun defSuffix s     = (s ^ !def_suffix);
fun defPrim s       = defSuffix(s^"_primitive");
fun defExtract(s,n) = defSuffix(s^"_extract"^Lib.int_to_string n);
fun argMunge s      = defSuffix(s^"_curried");
fun auxStem stem    = stem^"_AUX";
fun unionStem stem  = stem^"_UNION";

val imp_elim =
 let val P = mk_var("P",bool)
     val Q = mk_var("Q",bool)
     val R = mk_var("R",bool)
     val PimpQ = mk_imp(P,Q)
     val PimpR = mk_imp(P,R)
     val tm = mk_eq(PimpQ,PimpR)
     val tm1 = mk_imp(P,tm)
     val th1 = DISCH tm (DISCH P (ASSUME tm))
     val th2 = ASSUME tm1
     val th2a = ASSUME P
     val th3 = MP th2 th2a
     val th3a = EQ_MP (SPECL[PimpQ, PimpR] boolTheory.EQ_IMP_THM) th3
     val (th4,th5) = (CONJUNCT1 th3a,CONJUNCT2 th3a)
     fun pmap f (x,y) = (f x, f y)
     val (th4a,th5a) = pmap (DISCH P o funpow 2 UNDISCH) (th4,th5)
     val th4b = DISCH PimpQ th4a
     val th5b = DISCH PimpR th5a
     val th6 = DISCH tm1 (IMP_ANTISYM_RULE th4b th5b)
     val th7 = DISCH tm (DISCH P (ASSUME tm))
 in GENL [P,Q,R]
         (IMP_ANTISYM_RULE th6 th7)
 end;

fun inject ty [v] = [v]
  | inject ty (v::vs) =
     let val (lty,rty) = case dest_type ty of
                           (_, [x,y]) => (x,y)
                         | _ => raise Bind
         val res = mk_comb(mk_const("INL", lty-->ty),v)
         val inr = curry mk_comb (mk_const("INR", rty-->ty))
     in
       res::map inr (inject rty vs)
     end
  | inject ty [] = raise Match


fun project [] _ _ = raise ERR "project" "catastrophic invariant failure (eqns was empty!?)"
  | project [_] ty M = [M]
  | project (_::ls) ty M = let
      val (lty,rty) = sumSyntax.dest_sum ty
      in mk_comb(mk_const("OUTL", type_of M-->lty),M)
         :: project ls rty (mk_comb(mk_const("OUTR", type_of M-->rty),M))
      end

(*---------------------------------------------------------------------------*
 * We need a "smart" MP. th1 can be less quantified than th2, so th2 has     *
 * to be specialized appropriately. We assume that all the "local"           *
 * variables are quantified first.                                           *
 *---------------------------------------------------------------------------*)

fun ModusPonens th1 th2 =
  let val V1 = #1(strip_forall(fst(dest_imp(concl th1))))
      val V2 = #1(strip_forall(concl th2))
      val diff = Lib.op_set_diff Term.aconv V2 V1
      fun loop th =
        if is_forall(concl th)
        then let val (Bvar,Body) = dest_forall (concl th)
             in if Lib.op_mem Term.aconv Bvar diff
                then loop (SPEC Bvar th) else th
             end
        else th
  in
    MP th1 (loop th2)
  end
  handle _ => raise ERR "ModusPonens" "failed";


(*---------------------------------------------------------------------------*)
(* Version of PROVE_HYP that works modulo permuting outer universal quants.  *)
(*---------------------------------------------------------------------------*)

fun ALPHA_PROVE_HYP th1 th2 =
 let val c1 = concl th1
     val asl = hyp th2
     val tm = snd(strip_forall c1)
     val a = Lib.first (fn t => aconv tm (snd(strip_forall t))) asl
     val V = fst(strip_forall a)
     val th1' = GENL V (SPEC_ALL th1)
 in
   PROVE_HYP th1' th2
 end;

fun name_of (ABBREV {bind, ...})           = bind
  | name_of (PRIMREC{bind, ...})           = bind
  | name_of (NONREC {eqs, ind, stem, ...}) = stem
  | name_of (STDREC {eqs, ind, stem, ...}) = stem
  | name_of (MUTREC {eqs,ind,stem,...})    = stem
  | name_of (NESTREC{eqs,ind,stem, ...})   = stem
  | name_of (TAILREC{eqs,ind,stem, ...})   = stem

fun eqns_of (ABBREV  {eqn, ...}) = [eqn]
  | eqns_of (NONREC  {eqs, ...}) = [eqs]
  | eqns_of (PRIMREC {eqs, ...}) = [eqs]
  | eqns_of (STDREC  {eqs, ...}) = eqs
  | eqns_of (NESTREC {eqs, ...}) = eqs
  | eqns_of (MUTREC  {eqs, ...}) = eqs
  | eqns_of (TAILREC {eqs, ...}) = eqs;


fun aux_defn (NESTREC {aux, ...}) = SOME aux
  | aux_defn     _  = NONE;

fun union_defn (MUTREC {union, ...}) = SOME union
  | union_defn     _  = NONE;

fun ind_of (ABBREV _)           = NONE
  | ind_of (NONREC  {ind, ...}) = SOME ind
  | ind_of (PRIMREC {ind, ...}) = SOME ind
  | ind_of (STDREC  {ind, ...}) = SOME ind
  | ind_of (NESTREC {ind, ...}) = SOME ind
  | ind_of (MUTREC  {ind, ...}) = SOME ind
  | ind_of (TAILREC {ind, ...}) = SOME ind;


fun params_of (ABBREV _)  = []
  | params_of (PRIMREC _) = []
  | params_of (NONREC {SV, ...}) = SV
  | params_of (STDREC {SV, ...}) = SV
  | params_of (NESTREC{SV, ...}) = SV
  | params_of (MUTREC {SV, ...}) = SV
  | params_of (TAILREC {SV, ...}) = SV

fun schematic defn = not(List.null (params_of defn));

fun tcs_of (ABBREV _)  = []
  | tcs_of (NONREC _)  = []
  | tcs_of (PRIMREC _) = []
  | tcs_of (STDREC  {eqs,...}) = op_U aconv (map hyp eqs)
  | tcs_of (NESTREC {eqs,...}) = op_U aconv (map hyp eqs)
  | tcs_of (MUTREC  {eqs,...}) = op_U aconv (map hyp eqs)
  | tcs_of (TAILREC {eqs,...}) = raise ERR "tcs_of" "Tail recursive definition"


fun reln_of (ABBREV _)  = NONE
  | reln_of (NONREC _)  = NONE
  | reln_of (PRIMREC _) = NONE
  | reln_of (STDREC  {R, ...}) = SOME R
  | reln_of (NESTREC {R, ...}) = SOME R
  | reln_of (MUTREC  {R, ...}) = SOME R
  | reln_of (TAILREC {R, ...}) = SOME R;


fun nUNDISCH n th = if n<1 then th else nUNDISCH (n-1) (UNDISCH th)

fun INST_THM theta th =
  let val asl = hyp th
      val th1 = rev_itlist DISCH asl th
      val th2 = INST_TY_TERM theta th1
  in
   nUNDISCH (length asl) th2
  end;

fun isubst (tmtheta,tytheta) tm = subst tmtheta (inst tytheta tm);

fun inst_defn (STDREC{eqs,ind,R,SV,stem}) theta =
      STDREC {eqs=map (INST_THM theta) eqs,
              ind=INST_THM theta ind,
              R=isubst theta R,
              SV=map (isubst theta) SV, stem=stem}
  | inst_defn (NESTREC{eqs,ind,R,SV,aux,stem}) theta =
      NESTREC {eqs=map (INST_THM theta) eqs,
               ind=INST_THM theta ind,
               R=isubst theta R,
               SV=map (isubst theta) SV,
               aux=inst_defn aux theta, stem=stem}
  | inst_defn (MUTREC{eqs,ind,R,SV,union,stem}) theta =
      MUTREC {eqs=map (INST_THM theta) eqs,
              ind=INST_THM theta ind,
              R=isubst theta R,
              SV=map (isubst theta) SV,
              union=inst_defn union theta, stem=stem}
  | inst_defn (PRIMREC{eqs,ind,bind}) theta =
      PRIMREC{eqs=INST_THM theta eqs,
              ind=INST_THM theta ind, bind=bind}
  | inst_defn (NONREC {eqs,ind,SV,stem}) theta =
      NONREC {eqs=INST_THM theta eqs,
              ind=INST_THM theta ind,
              SV=map (isubst theta) SV,stem=stem}
  | inst_defn (ABBREV {eqn,bind}) theta = ABBREV {eqn=INST_THM theta eqn,bind=bind}
  | inst_defn (TAILREC{eqs,ind,R,SV,stem}) theta =
      TAILREC {eqs=map (INST_THM theta) eqs,
              ind=INST_THM theta ind,
              R=isubst theta R,
              SV=map (isubst theta) SV, stem=stem};


fun set_reln def R =
   case reln_of def
    of NONE => def
     | SOME Rpat => inst_defn def (Term.match_term Rpat R)
                    handle e => (HOL_MESG"set_reln: unable"; raise e);

fun PROVE_HYPL thl th = itlist PROVE_HYP thl th

fun MATCH_HYPL thms th =
  let val aslthms = mapfilter (EQT_ELIM o REWRITE_CONV thms) (hyp th)
  in itlist PROVE_HYP aslthms th
  end;


(* We use PROVE_HYPL on induction theorems, since their tcs are fully
   quantified. We use MATCH_HYPL on equations, since their tcs are
   bare.
*)

fun elim_tcs (STDREC {eqs, ind, R, SV,stem}) thms =
     STDREC{R=R, SV=SV, stem=stem,
            eqs=map (MATCH_HYPL thms) eqs,
            ind=PROVE_HYPL thms ind}
  | elim_tcs (NESTREC {eqs, ind, R,  SV, aux, stem}) thms =
     NESTREC{R=R, SV=SV, stem=stem,
            eqs=map (MATCH_HYPL thms) eqs,
            ind=PROVE_HYPL thms ind,
            aux=elim_tcs aux thms}
  | elim_tcs (MUTREC {eqs, ind, R, SV, union, stem}) thms =
     MUTREC{R=R, SV=SV, stem=stem,
            eqs=map (MATCH_HYPL thms) eqs,
            ind=PROVE_HYPL thms ind,
            union=elim_tcs union thms}
  | elim_tcs (TAILREC {eqs, ind, R, SV,stem}) thms =
     TAILREC{R=R, SV=SV, stem=stem,
            eqs=map (MATCH_HYPL thms) eqs,
            ind=PROVE_HYPL thms ind}
  | elim_tcs x _ = x;


local
 val lem =
   let val M  = mk_var("M",bool)
       val P  = mk_var("P",bool)
       val M1 = mk_var("M1",bool)
       val tm1 = mk_eq(M,M1)
       val tm2 = mk_imp(M,P)
   in DISCH tm1 (DISCH tm2 (SUBS [ASSUME tm1] (ASSUME tm2)))
   end
in
fun simp_assum conv tm th =
  let val th' = DISCH tm th
      val tmeq = conv tm
      val tm' = rhs(concl tmeq)
  in
    if aconv tm' T then MP th' (EQT_ELIM tmeq)
    else UNDISCH(MATCH_MP (MATCH_MP lem tmeq) th')
  end
end;

fun SIMP_HYPL conv th = itlist (simp_assum conv) (hyp th) th;

fun simp_tcs (STDREC {eqs, ind, R, SV, stem}) conv =
     STDREC{R=rhs(concl(conv R)), SV=SV, stem=stem,
            eqs=map (SIMP_HYPL conv) eqs,
            ind=SIMP_HYPL conv ind}
  | simp_tcs (NESTREC {eqs, ind, R,  SV, aux, stem}) conv =
     NESTREC{R=rhs(concl(conv R)), SV=SV, stem=stem,
            eqs=map (SIMP_HYPL conv) eqs,
            ind=SIMP_HYPL conv ind,
            aux=simp_tcs aux conv}
  | simp_tcs (MUTREC {eqs, ind, R, SV, union, stem}) conv =
     MUTREC{R=rhs(concl(conv R)), SV=SV, stem=stem,
            eqs=map (SIMP_HYPL conv) eqs,
            ind=SIMP_HYPL conv ind,
            union=simp_tcs union conv}
  | simp_tcs x _ = x;


fun TAC_HYPL tac th =
  PROVE_HYPL (mapfilter (C (curry Tactical.prove) tac) (hyp th)) th;

fun prove_tcs (STDREC {eqs, ind, R, SV, stem}) tac =
     STDREC{R=R, SV=SV, stem=stem,
            eqs=map (TAC_HYPL tac) eqs,
            ind=TAC_HYPL tac ind}
  | prove_tcs (NESTREC {eqs, ind, R,  SV, aux, stem}) tac =
     NESTREC{R=R, SV=SV, stem=stem,
            eqs=map (TAC_HYPL tac) eqs,
            ind=TAC_HYPL tac ind,
            aux=prove_tcs aux tac}
  | prove_tcs (MUTREC {eqs, ind, R, SV, union, stem}) tac =
     MUTREC{R=R, SV=SV, stem=stem,
            eqs=map (TAC_HYPL tac) eqs,
            ind=TAC_HYPL tac ind,
            union=prove_tcs union tac}
  | prove_tcs x _ = x;


(*---------------------------------------------------------------------------*)
(* Deal with basic definitions.                                              *)
(*---------------------------------------------------------------------------*)

fun triv_defn (ABBREV _) = true
  | triv_defn (PRIMREC _) = true
  | triv_defn otherwise = false

fun fetch_eqns (ABBREV{eqn,...})  = eqn
  | fetch_eqns (PRIMREC{eqs,...}) = eqs
  | fetch_eqns otherwise = raise ERR "fetch_eqns" "shouldn't happen"

(*---------------------------------------------------------------------------
   Store definition information to disk. Currently, just writes out the
   eqns and induction theorem. A more advanced implementation would
   write things out so that, when the exported theory is reloaded, the
   defn datastructure is rebuilt. This would give a seamless view of
   things.

   Note that we would need to save union and aux info only when
   termination has not been proved for a nested recursion.

   Another (easier) way to look at it would be to require termination
   and suchlike to be taken care of in the current theory. That is
   what is assumed at present.
 ---------------------------------------------------------------------------*)

local fun is_suc tm =
       case total dest_thy_const tm
        of NONE => false
         | SOME{Name,Thy,...} => Name="SUC" andalso Thy="num"
in
val SUC_TO_NUMERAL_DEFN_CONV_hook =
      ref (fn _ => raise ERR "SUC_TO_NUMERAL_DEFN_CONV_hook" "not initialized")
fun add_persistent_funs l =
  if not (!computeLib.auto_import_definitions) then () else
    let val has_lhs_SUC = List.exists
              (can (find_term is_suc) o lhs o #2 o strip_forall)
                                      o strip_conj o concl
      fun f (s, th) =
        [s] @
        (if has_lhs_SUC th then let
            val name = s^"_compute"
            val name = let
              val used = Lib.C Lib.mem (#1 (Lib.unzip (current_theorems())))
              fun loop n = let val x = (name^(Int.toString n)) in if used x then loop (n+1) else x end
              in if used name then loop 0 else name end
            val th_compute = CONV_RULE (!SUC_TO_NUMERAL_DEFN_CONV_hook) th
            val _ = save_thm(name,th_compute)
            in [name] end
         else [])
    in
      computeLib.add_persistent_funs (List.concat (map f l))
    end
end;

val mesg = with_flag(MESG_to_string, Lib.I) HOL_MESG

local
  val chatting = ref true
  val _ = Feedback.register_btrace("Define.storage_message", chatting)
in
fun been_stored (s,thm) =
  (add_persistent_funs [(s,thm)];
   if !chatting then
     mesg ((if !Globals.interactive then
              "Definition has been stored under "
            else
              "Saved definition __ ") ^Lib.quote s^"\n")
   else ()
   )

fun store(stem,eqs,ind) =
  let val eqs_bind = defSuffix stem
      val ind_bind = indSuffix stem
      fun save x = Feedback.trace ("Theory.save_thm_reporting", 0) save_thm x
      val   _  = save (ind_bind, ind)
      val eqns = save (eqs_bind, eqs)
      val _ = add_persistent_funs [(eqs_bind,eqs)]
         handle e => HOL_MESG ("Unable to add "^eqs_bind^" to global compset")
  in
    if !chatting then
       mesg (String.concat
               (if !Globals.interactive then
                  [   "Equations stored under ", Lib.quote eqs_bind,
                   ".\nInduction stored under ", Lib.quote ind_bind, ".\n"]
                else
                  [  "Saved definition __ ", Lib.quote eqs_bind,
                   "\nSaved induction ___ ", Lib.quote ind_bind, "\n"]))
    else ()
  end
end

local
  val LIST_CONJ_GEN = LIST_CONJ o map GEN_ALL
in
  fun save_defn (ABBREV {bind,eqn, ...})     = been_stored (bind,eqn)
  | save_defn (PRIMREC{bind,eqs, ...})       = been_stored (bind,eqs)
  | save_defn (NONREC {eqs, ind, stem, ...}) = store(stem,eqs,ind)
  | save_defn (STDREC {eqs, ind, stem, ...}) = store(stem,LIST_CONJ_GEN eqs,ind)
  | save_defn (TAILREC{eqs, ind, stem, ...}) = store(stem,LIST_CONJ_GEN eqs,ind)
  | save_defn (MUTREC {eqs,ind,stem,...})    = store(stem,LIST_CONJ_GEN eqs,ind)
  | save_defn (NESTREC{eqs,ind,stem, ...})   = store(stem,LIST_CONJ_GEN eqs,ind)
end


(*---------------------------------------------------------------------------
        Termination condition extraction
 ---------------------------------------------------------------------------*)

fun extraction_thms constset thy =
 let val {case_rewrites,case_congs} = extract_info constset thy
 in (case_rewrites, case_congs@read_congs())
 end;

(*---------------------------------------------------------------------------
         Capturing termination conditions.
 ----------------------------------------------------------------------------*)


local fun !!v M = mk_forall(v, M)
      val mem = Lib.op_mem aconv
      fun set_diff a b = Lib.filter (fn x => not (mem x b)) a
in
fun solver (restrf,f,G,nref) _ context tm =
  let val globals = f::G  (* not to be generalized *)
      fun genl tm = itlist !! (set_diff (rev(free_vars tm)) globals) tm
      val rcontext = rev context
      val antl = case rcontext of [] => []
                               | _   => [list_mk_conj(map concl rcontext)]
      val TC = genl(list_mk_imp(antl, tm))
      val (R,arg,pat) = wfrecUtils.dest_relation tm
  in
     if can(find_term (aconv restrf)) arg
     then (nref := true; raise ERR "solver" "nested function")
     else let val _ = if can(find_term (aconv f)) TC
                      then nref := true else ()
          in case rcontext
              of [] => SPEC_ALL(ASSUME TC)
               | _  => MATCH_MP (SPEC_ALL (ASSUME TC)) (LIST_CONJ rcontext)
          end
  end
end;

fun extract FV congs f (proto_def,WFR) =
 let val R = rand WFR
     val CUT_LEM = ISPECL [f,R] relationTheory.RESTRICT_LEMMA
     val restr_fR = rator(rator(lhs(snd(dest_imp (concl (SPEC_ALL CUT_LEM))))))
     fun mk_restr p = mk_comb(restr_fR, p)
 in fn (p,th) =>
    let val nested_ref = ref false
        val FV' = FV@free_vars(concl th)
        val rwArgs = (RW.Pure [CUT_LEM],
                      RW.Context ([],RW.DONT_ADD),
                      RW.Congs congs,
                      RW.Solver (solver (mk_restr p, f, FV', nested_ref)))
        val th' = CONV_RULE (RW.Rewrite RW.Fully rwArgs) th
    in
      (th', Lib.op_set_diff aconv (hyp th') [proto_def,WFR], !nested_ref)
    end
end;


(*---------------------------------------------------------------------------*
 * Perform TC extraction without making a definition.                        *
 *---------------------------------------------------------------------------*)

type wfrec_eqns_result = {WFR : term,
                          SV : term list,
                          proto_def : term,
                          extracta  : (thm * term list * bool) list,
                          pats  : pattern list}

fun protect_rhs eqn = mk_eq(lhs eqn,combinSyntax.mk_I(rhs eqn))
fun protect eqns = list_mk_conj (map protect_rhs (strip_conj eqns));

val unprotect_term = rhs o concl o PURE_REWRITE_CONV [combinTheory.I_THM];
val unprotect_thm  = PURE_REWRITE_RULE [combinTheory.I_THM];

(*---------------------------------------------------------------------------*)
(* Once patterns are instantiated and the clauses are simplified, there can  *)
(* still remain right-hand sides with occurrences of fully concrete tests on *)
(* literals. Here we simplify those away.                                    *)
(*                                                                           *)
(* const_eq_ref is a reference cell that decides equality of literals such   *)
(* as 23, "foo", #"G", 6w, 0b1000w. It gets updated in reduceLib, stringLib  *)
(* and wordsLib.                                                             *)
(*---------------------------------------------------------------------------*)

fun elim_triv_literal_CONV tm =
   let
      val const_eq_conv = !const_eq_ref
      val cnv = TRY_CONV (REWR_CONV literal_case_THM THENC BETA_CONV) THENC
                RATOR_CONV (RATOR_CONV (RAND_CONV const_eq_conv)) THENC
                PURE_ONCE_REWRITE_CONV [COND_CLAUSES]
   in
       cnv tm
   end

fun checkSV pats SV =
 let fun get_pat (GIVEN(p,_)) = p
       | get_pat (OMITTED(p,_)) = p
     fun strings_of vlist =
         Lib.commafy (List.map (Lib.quote o #1 o dest_var)
                               (Listsort.sort Term.compare vlist))
 in
   if null SV then ()
   else HOL_MESG (String.concat
     ["Definition is schematic in the following variables:\n    ",
      String.concat (strings_of SV)])
   ;
   case op_intersect aconv (free_varsl (map get_pat pats)) SV
    of [] => ()
     | probs =>
       raise ERR "wfrec_eqns"
         (String.concat
             (["the following variables occur both free (schematic) ",
               "and bound in the definition: \n   "] @ strings_of probs))
 end

(*---------------------------------------------------------------------------*)
(* Instantiate the recursion theorem and extract termination conditions,     *)
(* but do not define the constant yet.                                       *)
(*---------------------------------------------------------------------------*)

fun wfrec_eqns facts tup_eqs =
 let val {functional,pats} =
        mk_functional (TypeBasePure.toPmatchThry facts) (protect tup_eqs)
     val SV = free_vars functional    (* schematic variables *)
     val _ = checkSV pats SV
     val (f, Body) = dest_abs functional
     val (x,_) = dest_abs Body
     val (Name, fty) = dest_var f
     val (f_dty, f_rty) = Type.dom_rng fty
     val WFREC_THM0 = ISPEC functional relationTheory.WFREC_COROLLARY
     val R = variant (free_vars tup_eqs) (fst(dest_forall(concl WFREC_THM0)))
     val WFREC_THM = ISPECL [R, f] WFREC_THM0
     val tmp = fst(wfrecUtils.strip_imp(concl WFREC_THM))
     val proto_def = Lib.trye hd tmp
     val WFR = Lib.trye (hd o tl) tmp
     val R1 = rand WFR
     val corollary' = funpow 2 UNDISCH WFREC_THM
     val given_pats = givens pats
     val corollaries = map (C SPEC corollary') given_pats
     val eqns_consts = op_mk_set aconv (find_terms is_const functional)
     val (case_rewrites,congs) = extraction_thms eqns_consts facts
     val RWcnv = REWRITES_CONV (add_rewrites empty_rewrites
                                (literal_case_THM::case_rewrites))
     val rule = unprotect_thm o
                RIGHT_CONV_RULE
                   (LIST_BETA_CONV
                    THENC REPEATC ((RWcnv THENC LIST_BETA_CONV) ORELSEC
                                   elim_triv_literal_CONV))
     val corollaries' = map rule corollaries
  in
     {proto_def=proto_def,
      SV=Listsort.sort Term.compare SV,
      WFR=WFR,
      pats=pats,
      extracta = map (extract [R1] congs f (proto_def,WFR))
                     (zip given_pats corollaries')}
  end

(*---------------------------------------------------------------------------
 * Pair patterns with termination conditions. The full list of patterns for
 * a definition is merged with the TCs arising from the user-given clauses.
 * There can be fewer clauses than the full list, if the user omitted some
 * cases. This routine is used to prepare input for mk_induction.
 *---------------------------------------------------------------------------*)

fun merge full_pats TCs =
let fun insert (p,TCs) =
      let fun insrt ((x as (h,[]))::rst) =
                 if (aconv p h) then (p,TCs)::rst else x::insrt rst
            | insrt (x::rst) = x::insrt rst
            | insrt[] = raise ERR"merge.insert" "pat not found"
      in insrt end
    fun pass ([],ptcl_final) = ptcl_final
      | pass (ptcs::tcl, ptcl) = pass(tcl, insert ptcs ptcl)
in
  pass (TCs, map (fn p => (p,[])) full_pats)
end;

(*---------------------------------------------------------------------------*
 * Define the constant after extracting the termination conditions. The      *
 * wellfounded relation used in the definition is computed by using the      *
 * choice operator on the extracted conditions (plus the condition that      *
 * such a relation must be wellfounded).                                     *
 *                                                                           *
 * There are three flavours of recursion: standard, nested, and mutual.      *
 *                                                                           *
 * A "standard" recursion is one that is not mutual or nested.               *
 *---------------------------------------------------------------------------*)

fun stdrec thy bindstem {proto_def,SV,WFR,pats,extracta} =
 let val R1 = rand WFR
     val f = lhs proto_def
     val (extractants,TCl_0,_) = unzip3 extracta
     fun gen_all away tm =
        let val FV = free_vars tm
        in itlist (fn v => fn tm =>
              if op_mem aconv v away then tm else mk_forall(v,tm)) FV tm
        end
     val TCs_0 = op_U aconv TCl_0
     val TCl = map (map (gen_all (R1::SV))) TCl_0
     val TCs = op_U aconv TCl
     val full_rqt = WFR::TCs
     val R2 = mk_select(R1, list_mk_conj full_rqt)
     val R2abs = rand R2
     val fvar = mk_var(fst(dest_var f),
                       itlist (curry op-->) (map type_of SV) (type_of f))
     val fvar_app = list_mk_comb(fvar,SV)
     val (def,theory) = make_definition thy (defPrim bindstem)
                          (subst [f |-> fvar_app, R1 |-> R2] proto_def)
     val fconst = fst(strip_comb(lhs(snd(strip_forall(concl def)))))
     val disch'd = itlist DISCH (proto_def::WFR::TCs_0) (LIST_CONJ extractants)
     val inst'd = SPEC (list_mk_comb(fconst,SV))
                       (SPEC R2 (GENL [R1, f] disch'd))
     val def' = MP inst'd (SPEC_ALL def)
     val var_wits = LIST_CONJ (map ASSUME full_rqt)
     val TC_choice_thm =
           MP (CONV_RULE(BINOP_CONV BETA_CONV)(ISPECL[R2abs, R1] boolTheory.SELECT_AX)) var_wits
 in
    {theory = theory, R=R1, SV=SV,
     rules = CONJUNCTS
              (rev_itlist (C ModusPonens) (CONJUNCTS TC_choice_thm) def'),
     full_pats_TCs = merge (map pat_of pats) (zip (givens pats) TCl),
     patterns = pats}
 end


(*---------------------------------------------------------------------------
      Nested recursion.
 ---------------------------------------------------------------------------*)

fun nestrec thy bindstem {proto_def,SV,WFR,pats,extracta} =
 let val R1 = rand WFR
     val (f,rhs_proto_def) = dest_eq proto_def
     (* make parameterized definition *)
     val (Name,Ty) = Lib.trye dest_var f
     val aux_name = Name^"_aux"
     val faux = mk_var(aux_name,itlist(curry(op-->)) (map type_of (R1::SV)) Ty)
     val aux_bindstem = auxStem bindstem
     val (def,theory) =
           make_definition thy (defSuffix aux_bindstem)
               (mk_eq(list_mk_comb(faux,R1::SV), rhs_proto_def))
     val def' = SPEC_ALL def
     val faux_capp = lhs(concl def')
     val faux_const = #1(strip_comb faux_capp)
     val (extractants,TCl_0,_) = unzip3 extracta
     val TCs_0 = op_U aconv TCl_0
     val disch'd = itlist DISCH (proto_def::WFR::TCs_0) (LIST_CONJ extractants)
     val inst'd = GEN R1 (MP (SPEC faux_capp (GEN f disch'd)) def')
     fun kdisch keep th =
       itlist (fn h => fn th => if op_mem aconv h keep then th else DISCH h th)
              (hyp th) th
     val disch'dl_0 = map (DISCH proto_def o
                           DISCH WFR o kdisch [proto_def,WFR])
                        extractants
     val disch'dl_1 = map (fn d => MP (SPEC faux_capp (GEN f d)) def')
                          disch'dl_0
     fun gen_all away tm =
        let val FV = free_vars tm
        in itlist (fn v => fn tm =>
              if op_mem aconv v away then tm else mk_forall(v,tm)) FV tm
        end
     val TCl = map (map (gen_all (R1::f::SV) o subst[f |-> faux_capp])) TCl_0
     val TCs = op_U aconv TCl
     val full_rqt = WFR::TCs
     val R2 = mk_select(R1, list_mk_conj full_rqt)
     val R2abs = rand R2
     val R2inst'd = SPEC R2 inst'd
     val fvar = mk_var(fst(dest_var f),
                       itlist (curry op-->) (map type_of SV) (type_of f))
     val fvar_app = list_mk_comb(fvar,SV)
     val (def1,theory1) = make_definition thy (defPrim bindstem)
               (mk_eq(fvar_app, list_mk_comb(faux_const,R2::SV)))
     val var_wits = LIST_CONJ (map ASSUME full_rqt)
     val TC_choice_thm =
         MP (CONV_RULE(BINOP_CONV BETA_CONV)(ISPECL[R2abs, R1] boolTheory.SELECT_AX)) var_wits
     val elim_chosenTCs =
           rev_itlist (C ModusPonens) (CONJUNCTS TC_choice_thm) R2inst'd
     val rules = simplify [GSYM def1] elim_chosenTCs
     val pat_TCs_list = merge (map pat_of pats) (zip (givens pats) TCl)

     (* and now induction *)

     val aux_ind = Induction.mk_induction theory1
                       {fconst=faux_const, R=R1, SV=SV,
                        pat_TCs_list=pat_TCs_list}
     val ics = strip_conj(fst(dest_imp(snd(dest_forall(concl aux_ind)))))
     fun dest_ic tm = if is_imp tm then strip_conj (fst(dest_imp tm)) else []
     val ihs = Lib.flatten (map (dest_ic o snd o strip_forall) ics)
     val nested_ihs = filter (can (find_term (aconv faux_const))) ihs
     (* a nested ih is of the form

           !(c1/\.../\ck ==> R a pat ==> P a)

        where "aux R N" occurs in "c1/\.../\ck" or "a". In the latter case,
        we have a nested recursion; in the former, there's just a call
        to aux in the context. In both cases, we want to eliminate "R a pat"
        by assuming "c1/\.../\ck ==> R a pat" and doing some work. Really,
        what we prove is something of the form

          !(c1/\.../\ck ==> R a pat) |-
             (!(c1/\.../\ck ==> R a pat ==> P a))
               =
             (!(c1/\.../\ck ==> P a))

        where the c1/\.../\ck might not be there (when there is no
        context for the recursive call), and where !( ... ) denotes
        a universal prefix.
     *)
     fun fSPEC_ALL th =
       case Lib.total dest_forall (concl th) of
           SOME (v,_) => fSPEC_ALL (SPEC v th)
         | NONE => th
     fun simp_nested_ih nih =
      let val (lvs,tm) = strip_forall nih
          val (ants,Pa) = strip_imp_only tm
          val P = rator Pa  (* keep R, P, and SV unquantified *)
          val vs = op_set_diff aconv (free_varsl ants) (R1::P::SV)
          val V = op_union aconv lvs vs
          val has_context = (length ants = 2)
          val ng = list_mk_forall(V,list_mk_imp (front_last ants))
          val th1 = fSPEC_ALL (ASSUME ng)
          val th1a = if has_context then UNDISCH th1 else th1
          val th2 = fSPEC_ALL (ASSUME nih)
          val th2a = if has_context then UNDISCH th2 else th2
          val Rab = fst(dest_imp(concl th2a))
          val th3 = MP th2a th1a
          val th4 = if has_context
                    then DISCH (fst(dest_imp(concl th1))) th3
                    else th3
          val th5 = GENL lvs th4
          val th6 = DISCH nih th5
          val tha = fSPEC_ALL(ASSUME (concl th5))
          val thb = if has_context then UNDISCH tha else tha
          val thc = DISCH Rab thb
          val thd = if has_context
                     then DISCH (fst(dest_imp(snd(strip_forall ng)))) thc
                     else thc
          val the = GENL lvs thd
          val thf = DISCH_ALL the
      in
        MATCH_MP (MATCH_MP IMP_ANTISYM_AX th6) thf
      end handle e => raise wrap_exn "nestrec.simp_nested_ih"
                       "failed while trying to generated nested ind. hyp." e
     val nested_ih_simps = map simp_nested_ih nested_ihs
     val ind0 = simplify nested_ih_simps aux_ind
     val ind1 = UNDISCH_ALL (SPEC R2 (GEN R1 (DISCH_ALL ind0)))
     val ind2 = simplify [GSYM def1] ind1
     val ind3 = itlist ALPHA_PROVE_HYP (CONJUNCTS TC_choice_thm) ind2
 in
    {rules = CONJUNCTS rules,
     ind = ind3,
     SV = SV,
     R = R1,
     theory = theory1, aux_def = def, def = def1,
     aux_rules = map UNDISCH_ALL disch'dl_1,
     aux_ind = aux_ind
    }
 end;


(*---------------------------------------------------------------------------
      Performs tupling and also eta-expansion.
 ---------------------------------------------------------------------------*)

fun tuple_args alist =
 let
   val find = Lib.C (op_assoc1 aconv) alist
   fun tupelo tm =
     case dest_term tm of
        LAMB (Bvar, Body) => mk_abs (Bvar, tupelo Body)
      | _ =>
         let
           val (g, args) = strip_comb tm
           val args' = map tupelo args
         in
           case find g of
              NONE => list_mk_comb (g, args')
            | SOME (stem', argtys) =>
               if length args < length argtys  (* partial application *)
                 then
                   let
                     val nvs = map (curry mk_var "a") (drop args argtys)
                     val nvs' = variants (free_varsl args') nvs
                     val comb' = mk_comb(stem', list_mk_pair(args' @nvs'))
                   in
                     list_mk_abs(nvs', comb')
                   end
               else mk_comb(stem', list_mk_pair args')
         end
 in
   tupelo
 end;

(*---------------------------------------------------------------------------
     Mutual recursion. This is reduced to an ordinary definition by
     use of sum types. The n mutually recursive functions are mapped
     to a single function "mut" having domain and range be sums of
     the domains and ranges of the given functions. The domain sum
     has n components. The range sum has k <= n components, built from
     the set of range types. The arguments of the left hand side of
     the function are uniformly injected into the domain sum. On the
     right hand side, every occurrence of a function "f a" is translated
     to "OUT(mut (IN a))", where IN is the compound injection function,
     and OUT brings the result back to the original type of "f a".
     Finally, each rhs is injected into the range sum.

     After that translation, "mut" is defined. And then the individual
     functions are defined. Rewriting then brings them out.

     After that, induction is easy to recover from the induction theorem
     for mut.
 ---------------------------------------------------------------------------*)

fun ndom_rng ty 0 = ([],ty)
  | ndom_rng ty n =
      let val (dom,rng) = dom_rng ty
          val (L,last) = ndom_rng rng (n-1)
      in (dom::L, last)
      end;

fun tmi_eq (tm1,i1:int) (tm2,i2) = i1 = i2 andalso aconv tm1 tm2
fun mutrec thy bindstem eqns =
  let val dom_rng = Type.dom_rng
      val genvar = Term.genvar
      val DEPTH_CONV = Conv.DEPTH_CONV
      val BETA_CONV = Thm.BETA_CONV
      val OUTL = sumTheory.OUTL
      val OUTR = sumTheory.OUTR
      val sum_case_def = sumTheory.sum_case_def
      val CONJ = Thm.CONJ
      fun dest_atom tm = (dest_var tm handle HOL_ERR _ => dest_const tm)
      val eqnl = strip_conj eqns
      val lhs_info =
          op_mk_set tmi_eq (map ((I##length) o strip_comb o lhs) eqnl)
      val div_tys = map (fn (tm,i) => ndom_rng (type_of tm) i) lhs_info
      val lhs_info1 = zip (map fst lhs_info) div_tys
      val dom_tyl = map (list_mk_prod_type o fst) div_tys
      val rng_tyl = mk_set (map snd div_tys)
      val mut_dom = end_itlist mk_sum_type dom_tyl
      val mut_rng = end_itlist mk_sum_type rng_tyl
      val mut_name = unionStem bindstem
      val mut = mk_var(mut_name, mut_dom --> mut_rng)
      fun inform (f,(doml,rng)) =
        let val s = fst(dest_atom f)
        in if 1<length doml
            then (f, (mk_var(s^"_TUPLED",list_mk_prod_type doml --> rng),doml))
            else (f, (f,doml))
         end
      val eqns' = tuple_args (map inform lhs_info1) eqns
      val eqnl' = strip_conj eqns'
      val (L,R) = unzip (map dest_eq eqnl')
      val fnl' = op_mk_set aconv (map (fst o strip_comb o lhs) eqnl')
      val fnvar_map = zip lhs_info1 fnl'
      val gvl = map genvar dom_tyl
      val gvr = map genvar rng_tyl
      val injmap = zip fnl' (map2 (C (curry mk_abs)) (inject mut_dom gvl) gvl)
      fun mk_lhs_mut_app (f,arg) =
          mk_comb(mut,beta_conv (mk_comb(op_assoc aconv f injmap,arg)))
      val L1 = map (mk_lhs_mut_app o dest_comb) L
      val gv_mut_rng = genvar mut_rng
      val outfns = map (curry mk_abs gv_mut_rng) (project rng_tyl mut_rng gv_mut_rng)
      val ty_outs = zip rng_tyl outfns
      (* now replace each f by \x. outbar(mut(inbar x)) *)
      fun fout f = (f,assoc (#2(dom_rng(type_of f))) ty_outs)
      val RNG_OUTS = map fout fnl'
      fun mk_rhs_mut f v =
          (f |-> mk_abs(v,beta_conv (mk_comb(op_assoc aconv f RNG_OUTS,
                                             mk_lhs_mut_app (f,v)))))
      val R1 = map (Term.subst (map2 mk_rhs_mut fnl' gvl)) R
      val eqnl1 = zip L1 R1
      val rng_injmap =
            zip rng_tyl (map2 (C (curry mk_abs)) (inject mut_rng gvr) gvr)
      fun f_rng_in f = (f,assoc (#2(dom_rng(type_of f))) rng_injmap)
      val RNG_INS = map f_rng_in fnl'
      val tmp = zip (map (#1 o dest_comb) L) R1
      val R2 = map (fn (f,r) => beta_conv(mk_comb(op_assoc aconv f RNG_INS, r)))
                   tmp
      val R3 = map (rhs o concl o QCONV (DEPTH_CONV BETA_CONV)) R2
      val mut_eqns = list_mk_conj(map mk_eq (zip L1 R3))
      val wfrec_res = wfrec_eqns thy mut_eqns
      val defn =
        if exists I (#3(unzip3 (#extracta wfrec_res)))   (* nested *)
        then let val {rules,ind,aux_rules, aux_ind, theory, def,aux_def,...}
                     = nestrec thy mut_name wfrec_res
             in {rules=rules, ind=ind, theory=theory,
                 aux=SOME{rules=aux_rules, ind=aux_ind}}
              end
        else let val {rules,R,SV,theory,full_pats_TCs,...}
                   = stdrec thy mut_name wfrec_res
             val f = #1(dest_comb(lhs (concl(Lib.trye hd rules))))
             val ind = Induction.mk_induction theory
                         {fconst=f, R=R, SV=SV, pat_TCs_list=full_pats_TCs}
             in {rules=rules, ind=ind, theory=theory, aux=NONE}
             end
      val theory1 = #theory defn
      val mut_rules = #rules defn
      val mut_constSV = #1(dest_comb(lhs(concl (hd mut_rules))))
      val (mut_const,params) = strip_comb mut_constSV
      fun define_subfn (n,((fvar,(argtys,rng)),ftupvar)) thy =
         let val inbar  = op_assoc aconv ftupvar injmap
             val outbar = op_assoc aconv ftupvar RNG_OUTS
             val (fvarname,_) = dest_atom fvar
             val defvars = rev
                  (Lib.with_flag (Globals.priming, SOME"") (variants [fvar])
                     (map (curry mk_var "x") argtys))
             val tup_defvars = list_mk_pair defvars
             val newty = itlist (curry (op-->)) (map type_of params@argtys) rng
             val fvar' = mk_var(fvarname,newty)
             val dlhs  = list_mk_comb(fvar',params@defvars)
             val Uapp  = mk_comb(mut_constSV,
                            beta_conv(mk_comb(inbar,list_mk_pair defvars)))
             val drhs  = beta_conv (mk_comb(outbar,Uapp))
             val thybind = defExtract(mut_name,n)
         in
           (make_definition thy thybind (mk_eq(dlhs,drhs)) , (Uapp,outbar))
         end
      fun mk_def triple (defl,thy,Uout_map) =
            let val ((d,thy'),Uout) = define_subfn triple thy
            in (d::defl, thy', Uout::Uout_map)
            end
      val (defns,theory2,Uout_map) =
            itlist mk_def (Lib.enumerate 0 fnvar_map) ([],theory1,[])
      fun apply_outmap th =
         let fun matches (pat,_) = Lib.can (Term.match_term pat)
                                           (lhs (concl th))
             val (_,outf) = Lib.first matches Uout_map
         in AP_TERM outf th
         end
      val mut_rules1 = map apply_outmap mut_rules
      val simp = Rules.simplify (OUTL::OUTR::map GSYM defns)
      (* finally *)
      val mut_rules2 = map simp mut_rules1

      (* induction *)
      val mut_ind0 = simp (#ind defn)
      val pindices = enumerate (map fst div_tys)
      val vary = Term.variant(Term.all_varsl
                    (concl (hd mut_rules2)::hyp (hd mut_rules2)))
      fun mkP (tyl,i) def =
          let val V0 = snd(strip_comb(lhs(snd(strip_forall(concl def)))))
              val V = drop (#SV wfrec_res) V0
              val P = vary (mk_var("P"^Lib.int_to_string i,
                                   list_mk_fun_type (tyl@[bool])))
           in (P, mk_pabs(list_mk_pair V,list_mk_comb(P, V)))
          end
      val (Plist,preds) = unzip (map2 mkP pindices defns)
      val Psum_case = end_itlist (fn P => fn tm =>
           let val Pty = type_of P
               val Pdom = #1(dom_rng Pty)
               val tmty = type_of tm
               val tmdom = #1(dom_rng tmty)
               val gv = genvar (sumSyntax.mk_sum(Pdom, tmdom))
           in
              mk_abs(gv, sumSyntax.mk_sum_case(P,tm,gv))
           end) preds
      val mut_ind1 = Rules.simplify [sum_case_def] (SPEC Psum_case mut_ind0)
      val (ant,_) = dest_imp (concl mut_ind1)
      fun mkv (i,ty) = mk_var("v"^Lib.int_to_string i,ty)
      val V = map (map mkv)
                  (map (Lib.enumerate 0 o fst) pindices)
      val Vinj = map2 (fn f => fn vlist =>
                        beta_conv(mk_comb(#2 f, list_mk_pair vlist))) injmap V
      val und_mut_ind1 = UNDISCH mut_ind1
      val tmpl = map (fn (vlist,v) =>
                         GENL vlist (Rules.simplify [sum_case_def]
                                     (SPEC v und_mut_ind1)))   (zip V Vinj)
      val mut_ind2 = GENL Plist (DISCH ant (LIST_CONJ tmpl))
  in
    { rules = mut_rules2,
      ind =  mut_ind2,
      SV = #SV wfrec_res,
      R = rand (#WFR wfrec_res),
      union = defn,
      theory = theory2
    }
  end;


(*---------------------------------------------------------------------------
       The purpose of pairf is to translate a prospective definition
       into a completely tupled format. On entry to pairf, we know that
       f is curried, i.e., of type

              f : ty1 -> ... -> tyn -> rangety

       We build a tupled version of f

              f_tupled : ty1 * ... * tyn -> rangety

       and then make a definition

              f x1 ... xn = f_tupled (x1,...,xn)

       We also need to remember how to revert an induction theorem
       into the original domain type. This function is not used for
       mutual recursion, since things are more complicated there.

 ----------------------------------------------------------------------------*)

fun move_arg tm =
  Option.map
    (fn (f, (v, b)) => boolSyntax.mk_eq (Term.mk_comb (f, v), b))
    (Lib.total ((Lib.I ## Term.dest_abs) o boolSyntax.dest_eq) tm)

fun pairf (stem, eqs0) =
 let
   val ((f, args), rhs) = dest_hd_eqn eqs0
   val argslen = length args
 in
   if argslen = 1   (* not curried ... do eta-expansion *)
     then (tuple_args [(f, (f, map type_of args))] eqs0, stem, I)
   else
     let
       val stem'name = stem ^ "_tupled"
       val argtys = map type_of args
       val rng_ty = type_of rhs
       val tuple_dom = list_mk_prod_type argtys
       val stem' = mk_var (stem'name, tuple_dom --> rng_ty)
       fun untuple_args (rules, induction) =
         let
           val eq1 = concl (hd rules)
           val (lhs, rhs) = dest_eq (snd (strip_forall eq1))
           val (tuplec, args) = strip_comb lhs
           val (SV, p) = front_last args
           val defvars = rev (Lib.with_flag (Globals.priming, SOME "")
                                 (variants (f :: SV))
                                 (map (curry mk_var "x") argtys))
           val tuplecSV = list_mk_comb (tuplec, SV)
           val def_args = SV @ defvars
           val fvar =
             mk_var (atom_name f,
                     list_mk_fun_type (map type_of def_args @ [rng_ty]))
           val def  = new_definition (argMunge stem,
                        mk_eq (list_mk_comb (fvar, def_args),
                               list_mk_comb (tuplecSV, [list_mk_pair defvars])))
           val rules' = map (Rewrite.PURE_REWRITE_RULE [GSYM def]) rules
           val induction' =
             let
               val P = fst (dest_var (fst (dest_forall (concl induction))))
               val Qty = itlist (curry Type.-->) argtys Type.bool
               val Q = mk_primed_var (P, Qty)
               val tm =
                 mk_pabs (list_mk_pair defvars, list_mk_comb (Q, defvars))
             in
               GEN Q (PairedLambda.GEN_BETA_RULE
                   (SPEC tm (Rewrite.PURE_REWRITE_RULE [GSYM def] induction)))
             end
         in
           (rules', induction') before Theory.delete_const stem'name
         end
     in
       (tuple_args [(f, (stem', argtys))] eqs0, stem'name, untuple_args)
     end
 end
 handle e as HOL_ERR {message = "incompatible types", ...} =>
   case move_arg eqs0 of SOME tm => pairf (stem, tm) | NONE => raise e

(*---------------------------------------------------------------------------*)
(* Abbreviation or prim. rec. definitions.                                   *)
(*---------------------------------------------------------------------------*)

local fun is_constructor tm = not (is_var tm orelse is_pair tm)
in
fun non_wfrec_defn (facts,bind,eqns) =
 let val ((_,args),_) = dest_hd_eqn eqns
 in if Lib.exists is_constructor args
    then let
      val {Thy=cthy,Tyop=cty,...} =
            dest_thy_type (type_of(first is_constructor args))
      in
        case TypeBasePure.prim_get facts (cthy,cty)
        of NONE => raise ERR "non_wfrec_defn" "unexpected lhs in definition"
         | SOME tyinfo =>
           let val def = Prim_rec.new_recursive_definition
                          {name=bind,def = eqns,
                           rec_axiom = TypeBasePure.axiom_of tyinfo}
               val ind = TypeBasePure.induction_of tyinfo
           in PRIMREC{eqs = def, ind = ind, bind=bind}
           end
      end
    else ABBREV {eqn=new_definition (bind, eqns), bind=bind}
 end
end;

fun mutrec_defn (facts,stem,eqns) =
 let val {rules, ind, SV, R,
          union as {rules=r,ind=i,aux,...},...} = mutrec facts stem eqns
     val union' = case aux
      of NONE => STDREC{eqs = r,
                        ind = i,
                        R = R,
                        SV=SV, stem=unionStem stem}
      | SOME{rules=raux,ind=iaux} =>
         NESTREC{eqs = r,
                 ind = i,
                 R = R,
                 SV=SV, stem=unionStem stem,
                 aux=STDREC{eqs = raux,
                            ind = iaux,
                            R = R,
                            SV=SV,stem=auxStem stem}}
 in MUTREC{eqs = rules,
           ind = ind,
           R = R, SV=SV, stem=stem, union=union'}
 end
 handle e => raise wrap_exn "Defn" "mutrec_defn" e;

fun nestrec_defn (thy,(stem,stem'),wfrec_res,untuple) =
  let val {rules,ind,SV,R,aux_rules,aux_ind,...}
         = nestrec thy stem' wfrec_res
      val (rules', ind') = untuple (rules, ind)
  in NESTREC {eqs = rules',
              ind = ind',
              R = R, SV=SV, stem=stem,
              aux=STDREC{eqs = aux_rules,
                         ind = aux_ind,
                         R = R, SV=SV, stem=auxStem stem'}}
  end;

fun stdrec_defn (facts,(stem,stem'),wfrec_res,untuple) =
 let val {rules,R,SV,full_pats_TCs,...} = stdrec facts stem' wfrec_res
     val ((f,_),_) = dest_hd_eqnl rules
     val ind = Induction.mk_induction facts
                  {fconst=f, R=R, SV=SV, pat_TCs_list=full_pats_TCs}
 in
 case hyp (LIST_CONJ rules)
 of []     => raise ERR "stdrec_defn" "Empty hypotheses"
  | [WF_R] =>   (* non-recursive defn via complex patterns *)
       (let val (WF,R)    = dest_comb WF_R
            val theta     = [Type.alpha |-> hd(snd(dest_type (type_of R)))]
            val Empty_thm = INST_TYPE theta relationTheory.WF_EMPTY_REL
            val (r1, i1)  = untuple(rules, ind)
            val r2        = MATCH_MP (DISCH_ALL (LIST_CONJ r1)) Empty_thm
            val i2        = MATCH_MP (DISCH_ALL i1) Empty_thm
        in
           NONREC {eqs = r2,
                   ind = i2, SV=SV, stem=stem}
        end handle HOL_ERR _ => raise ERR "stdrec_defn" "")
  | otherwise =>
        let val (rules', ind') = untuple (rules, ind)
        in STDREC {eqs = rules',
                   ind = ind',
                   R = R, SV=SV, stem=stem}
        end
 end
 handle e => raise wrap_exn "Defn" "stdrec_defn" e

(*---------------------------------------------------------------------------
    A general, basic, interface to function definitions. First try to
    use standard existing machinery to make a prim. rec. definition, or
    an abbreviation. If those attempts fail, try to use a wellfounded
    definition (with pattern matching, wildcard expansion, etc.). Note
    that induction is derived for all wellfounded definitions, but
    a termination proof is not attempted. For that, use the entrypoints
    in TotalDefn.
 ---------------------------------------------------------------------------*)

fun prim_mk_defn stem eqns =
 let
   val _ = Lexis.ok_identifier stem orelse
           raise ERR "prim_mk_defn"
                 (String.concat [Lib.quote stem, " is not alphanumeric"])
   val facts = TypeBase.theTypeBase ()
 in
  non_wfrec_defn (facts, defSuffix stem, eqns)
  handle HOL_ERR _ =>
    case all_fns eqns of
       [] => raise ERR "prim_mk_defn" "no eqns"
     | [_] => (* one defn being made *)
        let
          val ((f, args), rhs) = dest_hd_eqn eqns
          fun err s = raise ERR "prim_mk_defn" s
        in
          if List.length args > 0 then
             let
                val (tup_eqs, stem', untuple) =
                  pairf (stem, eqns)
                  handle HOL_ERR _ =>
                    err "failure in internal translation to tupled format"
                val wfrec_res = wfrec_eqns facts tup_eqs
              in
                if exists I (#3 (unzip3 (#extracta wfrec_res)))   (* nested *)
                  then nestrec_defn (facts, (stem, stem'), wfrec_res, untuple)
                else stdrec_defn  (facts, (stem, stem'), wfrec_res, untuple)
              end
          else if free_in f rhs then
            case move_arg eqns of
               SOME tm => prim_mk_defn stem tm
             | NONE => err "Simple nullary definition recurses"
          else
            case free_vars rhs of
               [] => err "Nullary definition failed - giving up"
             | fvs =>
                err ("Free variables (" ^
                     String.concat (Lib.commafy (map (#1 o dest_var) fvs)) ^
                     ") on RHS of nullary definition")
        end
     | (_::_::_) => (* mutrec defns being made *)
        mutrec_defn (facts, stem, eqns)
 end
 handle e as HOL_ERR {origin_structure = "Defn", message = message, ...} =>
       if not (String.isPrefix "at Induction.mk_induction" message) orelse
          PmatchHeuristics.is_classic ()
          then raise wrap_exn "Defn" "prim_mk_defn" e
       else ( Feedback.HOL_MESG "Trying classic cases heuristic..."
            ; PmatchHeuristics.with_classic_heuristic (prim_mk_defn stem) eqns)
      | e => raise wrap_exn "Defn" "prim_mk_defn" e

(*---------------------------------------------------------------------------*)
(* Version of mk_defn that restores the term signature and grammar if it     *)
(* fails.                                                                    *)
(*---------------------------------------------------------------------------*)

fun mk_defn stem eqns =
  Parse.try_grammar_extension
    (Theory.try_theory_extension (uncurry prim_mk_defn)) (stem, eqns)

fun mk_Rdefn stem R eqs =
  let val defn = mk_defn stem eqs
  in case reln_of defn
      of NONE => defn
       | SOME Rvar => inst_defn defn (Term.match_term Rvar R)
  end;

(*===========================================================================*)
(* Calculating dependencies among a unordered collection of definitions      *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(* Transitive closure of relation rel given as list of pairs. The TC         *)
(* function operates on a list of elements [...,(x,(Y,fringe)),...] where    *)
(* Y is the set of "seen" fringe elements, and fringe is those elements of   *)
(* Y that we just "arrived at" (thinking of the relation as a directed       *)
(* graph) and which are not already in Y. Steps in the graph are made from   *)
(* the fringe, in a breadth-first manner.                                    *)
(*---------------------------------------------------------------------------*)

fun TC rels_0 =
 let fun step a = op_assoc aconv a rels_0 handle HOL_ERR _ => []
     fun relstep rels (x,(Y,fringe)) =
       let val fringe' = op_U aconv (map step fringe)
           val Y' = op_union aconv Y fringe'
           val fringe'' = op_set_diff aconv fringe' Y
       in (x,(Y',fringe''))
       end
     fun steps rels =
       case Lib.partition (null o (snd o snd)) rels
        of (_,[]) => map (fn (x,(Y,_)) => (x,Y)) rels
         | (nullrels,nnullrels) => steps (map (relstep rels) nnullrels @ nullrels)
 in
   steps (map (fn (x,Y) => (x,(Y,Y))) rels_0)
 end;

(*---------------------------------------------------------------------------*)
(* Transitive closure of a list of pairs.                                    *)
(*---------------------------------------------------------------------------*)

fun trancl rel =
 let val field = op_U aconv (map (fn (x,y) => [x,y]) rel)
     fun init x =
       let val Y = rev_itlist (fn (a,b) => fn acc =>
                      if aconv a x then op_insert aconv b acc else acc) rel []
       in (x,Y)
       end
 in
   TC (map init field)
 end;

(*---------------------------------------------------------------------------*)
(* partial order on the relation.                                            *)
(*---------------------------------------------------------------------------*)

fun depends_on (a,adeps) (b,bdeps) =
  op_mem aconv b adeps andalso not (op_mem aconv a bdeps);

(*---------------------------------------------------------------------------*)
(* Given a transitively closed relation, topsort it into dependency order,   *)
(* then build the mutually dependent chunks (cliques).                       *)
(*---------------------------------------------------------------------------*)

fun cliques_of tcrel =
 let fun chunk [] acc = acc
       | chunk ((a,adeps)::t) acc =
         let val (bideps,rst) =
                 Lib.partition (fn (b,bdeps) => op_mem aconv a bdeps) t
         in chunk rst (((a,adeps)::bideps)::acc)
         end
     val sorted = Lib.topsort depends_on tcrel
 in chunk sorted []
 end;

(*---------------------------------------------------------------------------
 Examples.
val ex1 =
 [("a","b"), ("b","c"), ("b","d"),("d","c"),
  ("a","e"), ("e","f"), ("f","e"), ("d","a"),
  ("f","g"), ("g","g"), ("g","i"), ("g","h"),
  ("i","h"), ("i","k"), ("h","j")];

val ex2 =  ("a","z")::ex1;
val ex3 =  ("z","a")::ex1;
val ex4 =  ("z","c")::ex3;
val ex5 =  ("c","z")::ex3;
val ex6 =  ("c","i")::ex3;

cliques_of (trancl ex1);
cliques_of (trancl ex2);
cliques_of (trancl ex3);
cliques_of (trancl ex4);
cliques_of (trancl ex5);
cliques_of (trancl ex6);
  --------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* Find the variables free in the rhs of an equation, that don't also occur  *)
(* on the lhs. This helps locate calls to other functions also being defined,*)
(* so that the dependencies can be calculated.                               *)
(*---------------------------------------------------------------------------*)

fun free_calls tm =
 let val (l,r) = dest_eq tm
     val (f,pats) = strip_comb l
     val lhs_vars = free_varsl pats
     val rhs_vars = free_vars r
 in
    (f, op_set_diff aconv rhs_vars lhs_vars)
 end;

(*---------------------------------------------------------------------------*)
(* Find all the dependencies between a collection of equations. Mutually     *)
(* dependent equations end up in the same clique.                            *)
(*---------------------------------------------------------------------------*)

fun dependencies eqns =
  let val basic = map free_calls (strip_conj eqns)
      fun agglom ((f,l1)::(g,l2)::t) =
             if aconv f g then agglom ((f,op_union aconv l1 l2)::t)
              else (f,l1)::agglom ((g,l2)::t)
        | agglom other = other
 in
   cliques_of (TC (agglom basic))
 end;

(*---------------------------------------------------------------------------
 Examples.

val eqns = ``(f x = 0) /\ (g y = 1) /\ (h a = h (a-1) + g a)``;
dependencies eqns;

val eqns = ``(f [] = 0) /\ (f (h1::t1) = g(h1) + f t1) /\
             (g y = 1) /\ (h a = h (a-1) + g a)``;
dependencies eqns;

load"stringTheory";
Hol_datatype `term = Var of string | App of string => term list`;
Hol_datatype `pterm = pVar of string | pApp of string # pterm list`;

val eqns = ``(f (pVar s) = sing s) /\
             (f (pApp (a,ptl)) = onion (sing a) (g ptl)) /\
             (g [] = {}) /\
             (g (t::tlist) = onion (f t) (g tlist)) /\
             (sing a = {a}) /\ (onion s1 s2 = s1 UNION s2)``;
dependencies eqns;
  ---------------------------------------------------------------------------*)

val eqn_head = head o lhs;

(*---------------------------------------------------------------------------*)
(* Take a collection of equations for a set of different functions, and      *)
(* untangle the dependencies so that functions are defined before use.       *)
(* Handles (mutually) recursive dependencies.                                *)
(*---------------------------------------------------------------------------*)

fun sort_eqns eqns =
 let val eql = strip_conj eqns
     val cliques = dependencies eqns
     val cliques' = map (map fst) cliques
     fun clique_eqns clique =
          filter (fn eqn => op_mem aconv (eqn_head eqn) clique) eql
 in
   map (list_mk_conj o clique_eqns) cliques'
 end;

(*---------------------------------------------------------------------------
 Example (adapted from ex1 above).

val eqns =
 ``(f1 x = f2 (x-1) + f5 (x-1)) /\
   (f2 x = f3 (x-1) + f4 (x-1)) /\
   (f3 x = x + 2) /\
   (f4 x = f3 (x-1) + f1(x-2)) /\
   (f5 x = f6 (x-1)) /\
   (f6 x = f5(x-1) + f7(x-2)) /\
   (f7 0 = f8 3 + f9 4) /\
   (f7 (SUC n) = SUC n * f7 n + f9 n) /\
   (f8 x = f10 (x + x)) /\
   (f9 x = f8 x + f11 (x-4)) /\
   (f10 x = x MOD 2) /\
   (f11 x = x DIV 2)``;

sort_eqns eqns;
sort_eqns (list_mk_conj (rev(strip_conj eqns)));
 ---------------------------------------------------------------------------*)

fun mk_defns stems eqnsl =
 let fun lhs_atoms eqns = op_mk_set aconv (map (head o lhs) (strip_conj eqns))
     fun mk_defn_theta stem eqns =
       let val Vs = lhs_atoms eqns
           val def = mk_defn stem eqns
           val Cs = op_mk_set aconv
                              (map (head o lhs o snd o strip_forall)
                                   (flatten
                                      (map (strip_conj o concl) (eqns_of def))))
           val theta = map2 (curry (op |->)) Vs Cs
       in (def, theta)
       end
    (*----------------------------------------------------------------------*)
    (* Once a definition is made, substitute the introduced constant for    *)
    (* the corresponding variables in the rest of the equations waiting to  *)
    (* be defined.                                                          *)
    (*----------------------------------------------------------------------*)
    fun mapdefn [] = []
      | mapdefn ((s,e)::t) =
         let val (defn,theta) = mk_defn_theta s e
             val t' = map (fn (s,e) => (s,subst theta e)) t
         in defn :: mapdefn t'
         end
 in
   mapdefn (zip stems eqnsl)
 end
 handle e => raise wrap_exn "Defn" "mk_defns" e;

(*---------------------------------------------------------------------------
     Quotation interface to definition. This includes a pass for
     expansion of wildcards in patterns.
 ---------------------------------------------------------------------------*)

fun vary s S =
 let fun V n =
      let val s' = s^Lib.int_to_string n
      in if mem s' S then V (n+1) else (s',s'::S)
      end
 in V 0 end;

(*---------------------------------------------------------------------------
    A wildcard is a contiguous sequence of underscores. This is
    somewhat cranky, we realize, but restricting to only one
    is not great for readability at times.
 ---------------------------------------------------------------------------*)

fun wildcard s =
    s <> "" andalso CharVector.all (fn #"_" => true | _ => false) s

local open Absyn
in
fun vnames_of (VAQ(_,tm)) S = union (map (fst o Term.dest_var) (all_vars tm)) S
  | vnames_of (VIDENT(_,s)) S = union [s] S
  | vnames_of (VPAIR(_,v1,v2)) S = vnames_of v1 (vnames_of v2 S)
  | vnames_of (VTYPED(_,v,_)) S = vnames_of v S

fun names_of (AQ(_,tm)) S = union (map (fst o Term.dest_var) (all_vars tm)) S
  | names_of (IDENT(_,s)) S = union [s] S
  | names_of (APP(_,IDENT(_,"case_arrow__magic"), _)) S = S
  | names_of (APP(_,M,N)) S = names_of M (names_of N S)
  | names_of (LAM(_,v,M)) S = names_of M (vnames_of v S)
  | names_of (TYPED(_,M,_)) S = names_of M S
  | names_of (QIDENT(_,_,_)) S = S
end;

local
  val v_vary = vary "v"
  fun tm_exp tm S =
    case dest_term tm
    of VAR(s,Ty) =>
         if wildcard s then
           let val (s',S') = v_vary S in (Term.mk_var(s',Ty),S') end
         else (tm,S)
     | CONST _  => (tm,S)
     | COMB(Rator,Rand) =>
        let val (Rator',S')  = tm_exp Rator S
            val (Rand', S'') = tm_exp Rand S'
        in (mk_comb(Rator', Rand'), S'')
        end
     | LAMB _ => raise ERR "tm_exp" "abstraction in pattern"
  open Absyn
in
fun exp (AQ(locn,tm)) S =
      let val (tm',S') = tm_exp tm S in (AQ(locn,tm'),S') end
  | exp (IDENT (p as (locn,s))) S =
      if wildcard s
        then let val (s',S') = v_vary S in (IDENT(locn,s'), S') end
        else (IDENT p, S)
  | exp (QIDENT (p as (locn,s,_))) S =
      if wildcard s
       then raise ERRloc "exp" locn "wildcard in long id. in pattern"
       else (QIDENT p, S)
  | exp (APP(locn,M,N)) S =
      let val (M',S')   = exp M S
          val (N', S'') = exp N S'
      in (APP (locn,M',N'), S'')
      end
  | exp (TYPED(locn,M,pty)) S =
      let val (M',S') = exp M S in (TYPED(locn,M',pty),S') end
  | exp (LAM(locn,_,_)) _ = raise ERRloc "exp" locn "abstraction in pattern"

fun expand_wildcards asy (asyl,S) =
   let val (asy',S') = exp asy S in (asy'::asyl, S') end
end;

fun multi_dest_eq t =
    Absyn.dest_eq t
      handle HOL_ERR _ => Absyn.dest_binop "<=>" t
      handle HOL_ERR _ => raise ERRloc "multi_dest_eq"
                                       (Absyn.locn_of_absyn t)
                                       "Expected an equality"

local
  fun dest_pvar (Absyn.VIDENT(_,s)) = s
    | dest_pvar other = raise ERRloc "munge" (Absyn.locn_of_vstruct other)
                                     "dest_pvar"
  fun dest_atom tm = (dest_const tm handle HOL_ERR _ => dest_var tm);
  fun dest_head (Absyn.AQ(_,tm)) = fst(dest_atom tm)
    | dest_head (Absyn.IDENT(_,s)) = s
    | dest_head (Absyn.TYPED(_,a,_)) = dest_head a
    | dest_head (Absyn.QIDENT(locn,_,_)) =
            raise ERRloc "dest_head" locn "qual. ident."
    | dest_head (Absyn.APP(locn,_,_)) =
            raise ERRloc "dest_head" locn "app. node"
    | dest_head (Absyn.LAM(locn,_,_)) =
            raise ERRloc "dest_head" locn "lam. node"
  fun strip_tyannote0 acc absyn =
      case absyn of
        Absyn.TYPED(locn, a, ty) => strip_tyannote0 ((ty,locn)::acc) a
      | x => (List.rev acc, x)
  val strip_tyannote = strip_tyannote0 []
  fun list_mk_tyannote(tyl,a) =
      List.foldl (fn ((ty,locn),t) => Absyn.TYPED(locn,t,ty)) a tyl
in
fun munge eq (eqs,fset,V) =
 let val (vlist,body) = Absyn.strip_forall eq
     val (lhs0,rhs)   = multi_dest_eq body
(*     val   _          = if exists wildcard (names_of rhs []) then
                         raise ERRloc "munge" (Absyn.locn_of_absyn rhs)
                                      "wildcards on rhs" else () *)
     val (tys, lhs)   = strip_tyannote lhs0
     val (f,pats)     = Absyn.strip_app lhs
     val (pats',V')   = rev_itlist expand_wildcards pats
                            ([],Lib.union V (map dest_pvar vlist))
     val new_lhs0     = Absyn.list_mk_app(f,rev pats')
     val new_lhs      = list_mk_tyannote(tys, new_lhs0)
     val new_eq       = Absyn.list_mk_forall(vlist, Absyn.mk_eq(new_lhs, rhs))
     val fstr         = dest_head f
 in
    (new_eq::eqs, insert fstr fset, V')
 end
end;

fun elim_wildcards eqs =
 let val names = names_of eqs []
     val (eql,fset,_) = rev_itlist munge (Absyn.strip_conj eqs) ([],[],names)
 in
   (Absyn.list_mk_conj (rev eql), rev fset)
 end;

(*---------------------------------------------------------------------------*)
(* To parse a purported definition, we have to convince the parser that the  *)
(* names to be defined aren't constants.  We can do this using "hide".       *)
(* After the parsing has been done, the grammar has to be put back the way   *)
(* it was.  If a definition is subsequently made, this will update the       *)
(* grammar further (ultimately using add_const).                             *)
(*---------------------------------------------------------------------------*)

fun non_head_idents acc alist =
    case alist of
      [] => acc
    | Absyn.IDENT(_, s)::rest => let
        val acc' =
            if Lexis.is_string_literal s orelse Lexis.is_char_literal s
            then acc
            else HOLset.add(acc,s)
      in
        non_head_idents acc' rest
      end
    | (a as Absyn.APP(_, _, x))::rest => let
        val (_, args) = Absyn.strip_app a
      in
        non_head_idents acc (args @ rest)
      end
    | Absyn.TYPED(_, a, _)::rest => non_head_idents acc (a::rest)
    | _ :: rest => non_head_idents acc rest

fun get_param_names eqs_a = let
  val eqs = Absyn.strip_conj eqs_a
  val heads = map (#1 o multi_dest_eq o #2 o Absyn.strip_forall) eqs
in
  non_head_idents (HOLset.empty String.compare) heads |> HOLset.listItems
end

fun is_constructor_name oinfo s = let
  val possible_ops =
      case Overload.info_for_name oinfo s of
        NONE => []
      | SOME {actual_ops, ...} => actual_ops
in
  List.exists TypeBase.is_constructor possible_ops
end

fun unify_error pv1 pv2 = let
  open Preterm
  val (nm,ty1,l1) = dest_ptvar pv1
  val (_,ty2,l2) = dest_ptvar pv2
in
  "Couldn't unify types of head symbol " ^
  Lib.quote nm ^ " at positions " ^ locn.toShortString l1 ^ " and " ^
  locn.toShortString l2 ^ " with types " ^
  type_to_string (Pretype.toType ty1) ^ " and " ^
  type_to_string (Pretype.toType ty2)
end

fun ptdefn_freevars pt = let
  open Preterm
  val (uvars, body) = strip_pforall pt
  val (l,r) = case strip_pcomb body of
                  (_, [l,r]) => (l,r)
                | _ => raise ERRloc "ptdefn_freevars" (locn body)
                             "Couldn't see preterm as equality"
  val (f0, args) = strip_pcomb l
  val f = head_var f0
  val lfs = op_U eq (map ptfvs args)
  val rfs = ptfvs r
  infix \\
  fun s1 \\ s2 = op_set_diff eq s1 s2
in
  op_union eq (rfs \\ lfs \\ uvars) [f]
end

fun defn_absyn_to_term a = let
  val alist = Absyn.strip_conj a
  open errormonad
  val tycheck = Preterm.typecheck_phase1 (SOME (term_to_string, type_to_string))
  val ptsM =
      mmap
        (fn a => absyn_to_preterm a >- (fn ptm => tycheck ptm >> return ptm))
        alist
  fun foldthis (pv as Preterm.Var{Name,Ty,Locn}, env) =
    if String.sub(Name,0) = #"_" then return env
    else
      (case Binarymap.peek(env,Name) of
           NONE => return (Binarymap.insert(env,Name,pv))
         | SOME pv' =>
             Preterm.ptype_of pv' >- (fn pty' => Pretype.unify Ty pty') >>
             return env)
    | foldthis (_, env) = raise Fail "defn_absyn_to_term: can't happen"
  open Preterm
  fun construct_final_term pts =
    let
      val ptm = plist_mk_rbinop
                  (Antiq {Tm=boolSyntax.conjunction,Locn=locn.Loc_None})
                  pts
    in
      overloading_resolution ptm >- (fn (pt,b) =>
      report_ovl_ambiguity b     >>
      to_term pt                 >- (fn t =>
      return (t |> remove_case_magic |> !post_process_term)))
    end
  val M =
    ptsM >-
    (fn pts =>
      let
        val all_frees = op_U Preterm.eq (map ptdefn_freevars pts)
      in
        foldlM foldthis (Binarymap.mkDict String.compare) all_frees >>
        construct_final_term pts
      end)
in
  smash M Pretype.Env.empty
end

fun parse_absyn absyn0 = let
  val (absyn,fn_names) = elim_wildcards absyn0
  val oldg = term_grammar()
  val oinfo = term_grammar.overload_info oldg
  val nonconstructor_parameter_names =
      List.filter (not o is_constructor_name oinfo) (get_param_names absyn)
  val _ =
      app (ignore o Parse.hide) (nonconstructor_parameter_names @ fn_names)
  fun restore() = temp_set_grammars(type_grammar(), oldg)
  val tm  = defn_absyn_to_term absyn handle e => (restore(); raise e)
in
  restore();
  (tm, fn_names)
end;

(*---------------------------------------------------------------------------*)
(* Parse a quotation. Fail if parsing or type inference or overload          *)
(* resolution (etc) fail. Returns a list of equations; each element in the   *)
(* list is a separate mutually recursive clique.                             *)
(*---------------------------------------------------------------------------*)

fun parse_quote q =
  sort_eqns (fst (parse_absyn (Parse.Absyn q)))
  handle e => raise wrap_exn "Defn" "parse_quote" e;

fun Hol_defn stem q =
 (case parse_quote q
   of [] => raise ERR "Hol_defn" "no definitions"
    | [eqns] => mk_defn stem eqns
    | otherwise => raise ERR "Hol_defn" "multiple definitions")
  handle e =>
  raise wrap_exn_loc "Defn" "Hol_defn"
           (Absyn.locn_of_absyn (Parse.Absyn q)) e;

fun Hol_defns stems q =
 (case parse_quote q
   of [] => raise ERR "Hol_defns" "no definition"
    | eqnl => mk_defns stems eqnl)
  handle e => raise wrap_exn_loc "Defn" "Hol_defns"
                 (Absyn.locn_of_absyn (Parse.Absyn q)) e;

local
  val stems =
    List.map (fst o dest_var o fst o strip_comb o lhs o snd o strip_forall o
              hd o strip_conj)
in
  fun Hol_multi_defns q =
    (case parse_quote q of
       [] => raise ERR "Hol_multi_defns" "no definition"
      | eqnsl => mk_defns (stems eqnsl) eqnsl)
    handle e => raise wrap_exn_loc "Defn" "Hol_multi_defns"
                   (Absyn.locn_of_absyn (Parse.Absyn q)) e
end

fun Hol_Rdefn stem Rquote eqs_quote =
  let val defn = Hol_defn stem eqs_quote
  in case reln_of defn
      of NONE => defn
       | SOME Rvar =>
          let val R = Parse.typedTerm Rquote (type_of Rvar)
          in inst_defn defn (Term.match_term Rvar R)
          end
  end;

(*---------------------------------------------------------------------------
        Goalstack-based interface to termination proof.
 ---------------------------------------------------------------------------*)

fun mangle th [] = th
  | mangle th [h] = DISCH h th
  | mangle th (h::rst) =
      Rewrite.PURE_ONCE_REWRITE_RULE [boolTheory.AND_IMP_INTRO]
         (DISCH h (mangle th rst));


(*---------------------------------------------------------------------------
    Have to take care with how the assumptions are discharged. Hence mangle.
 ---------------------------------------------------------------------------*)

val WF_tm = prim_mk_const{Name="WF",Thy="relation"};

fun get_WF tmlist =
 pluck (same_const WF_tm o rator) tmlist
 handle HOL_ERR _ => raise ERR "get_WF" "unexpected termination condition";

fun TC_TAC0 E I =
 let val th = CONJ E I
     val asl = hyp th
     val hyps' = let val (wfr,rest) = get_WF asl
                 in wfr::rest end handle HOL_ERR _ => asl
     val tac = MATCH_MP_TAC (GEN_ALL (mangle th hyps'))
     val goal = ([],concl th)
 in
   case tac goal
    of ([([],g)],validation) => (([],g), fn th => validation [th])
     | _  => raise ERR "TC_TAC" "unexpected output"
 end;

fun TC_TAC defn =
 let val E = LIST_CONJ (eqns_of defn)
     val I = Option.valOf (ind_of defn)
 in
   TC_TAC0 E I
 end;

fun tgoal_no_defn0 (def,ind) =
   if null (op_U aconv [(hyp def)])
   then raise ERR "tgoal" "no termination conditions"
   else let val (g,validation) = TC_TAC0 def ind
        in proofManagerLib.add (Manager.new_goalstack g validation)
        end handle HOL_ERR _ => raise ERR "tgoal" "";

fun tgoal_no_defn (def,ind) =
  Lib.with_flag (proofManagerLib.chatting,false) tgoal_no_defn0 (def,ind);

fun tgoal0 defn =
   if null (tcs_of defn)
   then raise ERR "tgoal" "no termination conditions"
   else let val (g,validation) = TC_TAC defn
        in proofManagerLib.add (Manager.new_goalstack g validation)
        end handle HOL_ERR _ => raise ERR "tgoal" "";

fun tgoal defn = Lib.with_flag (proofManagerLib.chatting,false) tgoal0 defn;

(*---------------------------------------------------------------------------
     The error handling here is pretty coarse.
 ---------------------------------------------------------------------------*)

fun tprove2 tgoal0 (defn,tactic) =
  let val _ = tgoal0 defn
      val _ = proofManagerLib.expand tactic  (* should finish proof off *)
      val th  = proofManagerLib.top_thm ()
      val _   = proofManagerLib.drop()
      val eqns = CONJUNCT1 th
      val ind  = CONJUNCT2 th
  in
     (eqns,ind)
  end
  handle e => (proofManagerLib.drop(); raise wrap_exn "Defn" "tprove" e)

fun tprove1 tgoal0 p =
  let
    val (eqns,ind) = Lib.with_flag (proofManagerLib.chatting,false) (tprove2 tgoal0) p
    val () = if not (!computeLib.auto_import_definitions) then ()
             else computeLib.add_funs
                    [eqns, CONV_RULE (!SUC_TO_NUMERAL_DEFN_CONV_hook) eqns]
  in
    (eqns, ind)
  end

fun tprove p = tprove1 tgoal0 p
fun tprove0 p = tprove2 tgoal0 p
fun tprove_no_defn p = tprove1 tgoal_no_defn0 p

fun tstore_defn (d,t) =
  let val (def,ind) = tprove0 (d,t)
  in store (name_of d,def,ind)
   ; (def,ind)
  end;

end (* Defn *)
