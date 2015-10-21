(* ========================================================================= *
 *                                                                           *
 *                        Coinductive Definitions                            *
 *                                                                           *
 * ========================================================================= *)

structure CoIndDefLib :> CoIndDefLib =
struct

open HolKernel boolLib liteLib InductiveDefinition IndDefLib


(* Prove definitions work for non-schematic relations with canonical rules.  *)

fun derive_canon_coinductive_relations pclauses =
    let val (vargs, bodies) = split(map strip_forall pclauses)
    	val swap_fn = fn (x, y) => (y, x)
    	val bodies = map mk_imp (map swap_fn (map dest_imp bodies))
    	val pclauses = map list_mk_forall (zip vargs bodies)
    	val closed = list_mk_conj pclauses
    	val (ants, concs) = split (map dest_imp bodies)
    	val rels = map (repeat rator) ants
    	val avoids = all_vars closed
    	val rels' = variants avoids rels
    	val prime_fn = subst (map2 (curry op |->) rels rels' )
    	val closed' = prime_fn closed

	(* definition theorems *)
	fun mk_def arg ant =
	    mk_eq(repeat rator ant,
		  list_mk_abs(arg,list_mk_exists(rels',
				 mk_conj(prime_fn ant, closed'))))
	val deftms = map2 mk_def vargs ants
	val defthms = map2 HALF_BETA_EXPAND vargs (map ASSUME deftms)

	(* coinductive theorems *)
	fun rm_exists_left th =
	    let val ant = fst (dest_imp (concl th))
		val (vars, conj) = strip_exists ant
		val ex_fn = fn (v, t) => EXISTS(mk_exists(v, concl t), v) t
		val ex = foldl ex_fn (ASSUME conj) (rev vars)
		val th1 = PROVE_HYP ex (UNDISCH th)
		val (c1, c2) = dest_conj conj
		val th2 = CONJ (ASSUME c1) (ASSUME c2)
	    in DISCH c1 (PROVE_HYP th2 th1)
	    end

	fun mk_coind args th =
	    let val th = snd(EQ_IMP_RULE(SPEC_ALL th))
	    in GENL args (rm_exists_left th)
	    end
	val coindthms = map2 mk_coind vargs defthms
	val coindthmr = end_itlist CONJ coindthms
	val coindthm = GENL rels'(DISCH closed' coindthmr)

	(* mono theorems *)
        val mants = map2 (fn a => fn t =>
          list_mk_forall(a,mk_imp(prime_fn t, t))) vargs concs
        val monotm = mk_imp(concl coindthmr, list_mk_conj mants)
        val monothm = ASSUME(list_mk_forall(rels,list_mk_forall(rels',monotm)))
	val closthm = ASSUME closed'
        val monothms = CONJUNCTS
            (MP (SPEC_ALL monothm) (MP (SPECL rels' coindthm) closthm))
        val closthms = CONJUNCTS closthm

	(* rules *)
	fun intro_exists_left th =
	    let val conj1 = fst (dest_imp (concl th))
		val conj = mk_conj(conj1, closed')
		val A = CONJUNCT1(ASSUME conj);
		val B = CONJUNCT2(ASSUME conj);
		val step1 = PROVE_HYP A (UNDISCH th);
		val step2 = PROVE_HYP B step1;
		val ex_fn = fn (v, (t1, t2)) =>
		    (mk_exists(v, t1), CHOOSE(v, ASSUME (mk_exists(v, t1))) t2)
	    in foldl ex_fn (conj, step2) (rev rels')
	    end

        fun prove_rule mth (cth,dth) =
            let val (avs, bod) = strip_forall(concl mth)
                val th1 = IMP_TRANS (SPECL avs cth) (SPECL avs mth)
		val (ex, th1') = intro_exists_left th1
                val th2 = DISCH ex th1'
                val th3 = IMP_TRANS (fst(EQ_IMP_RULE(SPECL avs dth))) th2
            in GENL avs th3
            end
        val ruvalhms = map2 prove_rule monothms (zip closthms defthms)
        val ruvalhm = end_itlist CONJ ruvalhms

	(* cases *)
        val dtms = map2 (curry list_mk_abs) vargs concs
        val double_fn = subst (map2 (curry op |->) rels dtms)
        fun mk_unbetas tm dtm =
            let val (avs,bod) = strip_forall tm
                val (il,r) = dest_comb bod
                val (i,l) = dest_comb il
                val bth = RIGHT_BETAS avs (REFL dtm)
                val munb = AP_THM (AP_TERM i bth) l
		val iunb = AP_THM (AP_TERM i bth) (double_fn r)
                val junb = AP_TERM (mk_comb(i,l)) bth
                val quantify = itlist MK_FORALL avs
            in (quantify junb,(quantify iunb,quantify munb))
            end
        val unths = map2 mk_unbetas pclauses dtms
        val irthm = EQ_MP (SYM(end_itlist MK_CONJ (map fst unths))) ruvalhm
        val mrthm = MP (SPECL rels (SPECL dtms monothm)) irthm
        val imrth = EQ_MP
          (SYM(end_itlist MK_CONJ (map (fst o snd) unths))) mrthm
        val ifthm = MP (SPECL dtms coindthm) imrth
        val fthm = EQ_MP (end_itlist MK_CONJ (map (snd o snd) unths)) ifthm
        fun mk_case th1 th2 =
            let val avs = fst(strip_forall(concl th1))
            in GENL avs (IMP_ANTISYM_RULE (SPEC_ALL th2) (SPEC_ALL th1))
            end
        val casethm = end_itlist CONJ
               (map2 mk_case (CONJUNCTS fthm) (CONJUNCTS ruvalhm))
    in CONJ fthm (CONJ coindthm casethm)
    end
    handle e => raise (wrap_exn "CoIndDefLib"
                         "derive_canon_coinductive_relations"e);



(* General case for nonschematic relations; monotonicity & defn hyps.        *)

fun derive_nonschematic_coinductive_relations tm =
  let val clauses   = strip_conj tm
      val canonthm  = canonicalize_clauses clauses
      val canonthm' = SYM canonthm
      val pclosed   = rand(concl canonthm)
      val pclauses  = strip_conj pclosed
      val rawthm    = derive_canon_coinductive_relations pclauses
      val (ruvalhm,otherthms) = CONJ_PAIR rawthm
      val (indthm,casethm)    = CONJ_PAIR otherthms
      val ruvalhm' = EQ_MP canonthm' ruvalhm
      and indthm'  = CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV canonthm')) indthm
  in CONJ ruvalhm' (CONJ indthm' casethm)
  end
  handle e => raise (wrap_exn "CoIndDefLib"
                       "derive_nonschematic_coinductive_relations" e);


fun new_coinductive_definition monoset stem (tm,clocs) =
 let val clauses = strip_conj tm
     val (clauses',fvs) = unschematize_clauses clauses
     val _ = check_definition fvs clocs (list_mk_conj clauses')
     val th0 = derive_nonschematic_coinductive_relations
                 (check_definition fvs clocs (list_mk_conj clauses'))
     val th1 = prove_monotonicity_hyps monoset th0
     val th2 = generalize_schematic_variables fvs th1
     val th3 = make_definitions stem th2
     val avs = fst(strip_forall(concl th3))
     val (r,ic) = CONJ_PAIR(SPECL avs th3)
     val (i,c)  = CONJ_PAIR ic
 in (GENL avs r, GENL avs i, GENL avs c)
 end
 handle e => raise wrap_exn "CoIndDefLib" "new_coinductive_definition" e;


(* ------------------------------------------------------------------------- *)

fun save_theorems name (rules, coind, strong_ind, cases) = let
in
  save_thm(name^"_rules", rules);
  save_thm(name^"_coind", coind);
  (* save_thm(name^"_strongind", strong_ind);*)
  save_thm(name^"_cases", cases);
  (* export_rule_induction (name ^ "_strongind") *)
  ()
end

fun derive_strong_coinduction (rules, coind) = ((* TODO *))

(* -------------------------------------------------------------------------  )
(  Entrypoints:                                                              *)

fun Hol_mono_coreln name monoset tm = let
  val _ = Lexis.ok_sml_identifier (name ^ !boolLib.def_suffix) orelse
          raise ERR "Hol_mono_coreln"
                    ("Bad name for definition: "^ Lib.mlquote name^
                     " (use xHol_coreln to specify a better)")
  val (rules, coind, cases) = new_coinductive_definition monoset name tm
  val strong_ind = derive_strong_coinduction (rules, coind)
in
  save_theorems name (rules, coind, strong_ind, cases);
  (rules, coind, cases)
end
handle e => raise (wrap_exn "CoIndDefLib" "Hol_mono_coreln" e);

fun xHol_coreln name q =
    Hol_mono_coreln name (!IndDefLib.the_monoset) (IndDefLib.term_of q)

fun Hol_coreln q = let
  val parse = IndDefLib.term_of
                      |> trace ("syntax_error", 0)
                      |> trace ("show_typecheck_errors", 0)
  val def as (def_t, _) = parse q
  val name = IndDefLib.name_from_def def_t
in
  Hol_mono_coreln name (!IndDefLib.the_monoset) def
end handle e => Raise (wrap_exn "CoIndDefLib" "Hol_coreln" e);


end (* CoIndDefLib *)
