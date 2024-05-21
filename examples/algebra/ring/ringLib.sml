(* ========================================================================= *)
(*  A decision procedure for the universal theory of rings                   *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)
(* Ported by Chun Tian. The Australian National University (ANU), May 2024   *)
(* ========================================================================= *)

structure ringLib :> ringLib =
struct

open HolKernel boolLib bossLib;

open pred_setTheory cardinalTheory ringTheory ringLibTheory Grobner Normalizer
     integerTheory intReduce intLib tautLib normalForms Canon Canon_Port
     pairSyntax intSyntax ringSyntax pred_setSyntax Ho_Rewrite liteLib;

(* ------------------------------------------------------------------------- *)
(* Establish the required grammar(s) for executing this file                 *)
(* ------------------------------------------------------------------------- *)

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars ringLib_grammars
end

open Parse;

val ERR = mk_HOL_ERR "ringLib";
fun failwith s = raise ERR "?" s

(* |- !P Q. P /\ (?x. Q x) <=> ?x. P /\ Q x *)
val RIGHT_AND_EXISTS_THM = GSYM RIGHT_EXISTS_AND_THM

(* |- !P Q. (?x. P x) /\ Q <=> ?x. P x /\ Q *)
val LEFT_AND_EXISTS_THM = GSYM LEFT_EXISTS_AND_THM

(* |- p ==> q ==> r <=> p /\ q ==> r *)
val IMP_IMP = Q.SPECL [‘p’, ‘q’, ‘r’] AND_IMP_INTRO;

val PRENEX_CONV = Canon.PRENEX_CONV;
val CNF_CONV    = Canon.CNF_CONV;

val ring_tyname = "Ring"; (* There are also other occurrences of it. *)

(* ------------------------------------------------------------------------- *)
(* Instantiate the normalizer and ring procedure for the case of a ring      *)
(* "r:A ring" with the whole type A as the carrier. Since all the machinery  *)
(* of the normalizer is designed for such "universal" rings, this is the     *)
(* best we can do, but below we use this to define a general procedure.      *)
(* The RING instantiation is called RING_INTEGRAL_DOMAIN_UNIVERSAL since     *)
(* it in general assumes "integral_domain r" and may also assume that        *)
(* "ring_char r = 0". Later we use the other cofactors function to give      *)
(* a better decision procedure for general rings, but the integral           *)
(* domain one may be independently useful for proofs involving cancellation  *)
(* in such domains.                                                          *)
(* ------------------------------------------------------------------------- *)

(* 1. RING_POLY_UNIVERSAL_CONV *)
local
  val pth = (UNDISCH o SPEC_ALL o prove)
   (“!r. ring_carrier r = univ(:'a)
          ==> (!x y z. ring_add r x (ring_add r y z) =
                       ring_add r (ring_add r x y) z) /\
              (!x y. ring_add r x y = ring_add r y x) /\
              (!x. ring_add r (ring_of_int r (&0)) x = x) /\
              (!x y z. ring_mul r x (ring_mul r y z) =
                       ring_mul r (ring_mul r x y) z) /\
              (!x y. ring_mul r x y = ring_mul r y x) /\
              (!x. ring_mul r (ring_of_int r (&1)) x = x) /\
              (!x. ring_mul r (ring_of_int r (&0)) x = ring_of_int r (&0)) /\
              (!x y z. ring_mul r x (ring_add r y z) =
                       ring_add r (ring_mul r x y) (ring_mul r x z)) /\
              (!x. ring_pow r x 0 = ring_of_int r (&1)) /\
              (!x n. ring_pow r x (SUC n) = ring_mul r x (ring_pow r x n))”,
    REWRITE_TAC[RING_OF_INT_OF_NUM, RING_OF_NUM_1, CONJUNCT1 ring_of_num] THEN
    SIMP_TAC std_ss[RING_ADD_LZERO, RING_MUL_LID, RING_MUL_LZERO, IN_UNIV] THEN
    SIMP_TAC std_ss[ring_pow, RING_ADD_LDISTRIB, IN_UNIV] THEN
    SIMP_TAC std_ss[RING_ADD_AC, RING_MUL_AC, IN_UNIV]);
  val sth = (UNDISCH o SPEC_ALL o prove)
   (“!r. ring_carrier r = univ(:'a)
          ==> (!x. ring_neg r x = ring_mul r (ring_of_int r (- &1)) x) /\
              (!x y. ring_sub r x y =
                     ring_add r x (ring_mul r (ring_of_int r (- &1)) y))”,
    SIMP_TAC std_ss[RING_OF_INT_NEG, RING_MUL_LNEG, IN_UNIV, ring_sub] THEN
    REWRITE_TAC[RING_OF_INT_OF_NUM, RING_OF_NUM_1, CONJUNCT1 ring_of_num] THEN
    SIMP_TAC std_ss[ring_sub, RING_MUL_LNEG, RING_MUL_LID, IN_UNIV]);
  val RING_INT_ADD_CONV =
      GEN_REWRITE_CONV I [GSYM RING_OF_INT_ADD] THENC
      RAND_CONV INT_ADD_CONV;
  val RING_INT_MUL_CONV =
      GEN_REWRITE_CONV I [GSYM RING_OF_INT_MUL] THENC
      RAND_CONV INT_MUL_CONV;
  val RING_INT_POW_CONV =
      GEN_REWRITE_CONV I [GSYM RING_OF_INT_POW] THENC
      RAND_CONV INT_POW_CONV;
  val ith = prove
    (“ring_0 r = ring_of_int r (&0) /\
      ring_1 r = ring_of_int r (&1)”,
      REWRITE_TAC[RING_OF_INT_OF_NUM, RING_OF_NUM_1, CONJUNCT1 ring_of_num]);
  fun term_lt u t = (Term.compare(u,t) = LESS);
  val (_,_,_,_,_,RING_POLY_CONV) =
    SEMIRING_NORMALIZERS_CONV pth sth
     (is_ringconst,
      RING_INT_ADD_CONV,RING_INT_MUL_CONV,RING_INT_POW_CONV)
     term_lt
in
val RING_POLY_UNIVERSAL_CONV =
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [ith, GSYM RING_OF_INT_OF_NUM]
    THENC RING_POLY_CONV
end;

(* 2. RING_INTEGRAL_DOMAIN_UNIVERSAL and ring_ring_cofactors_universal *)
local
  val RING_INTEGRAL = repeat UNDISCH RING_INTEGRAL_LEMMA;
  val neth_b = prove
   (“ring_of_int r n :'a = ring_of_int r n <=> T”,
    REWRITE_TAC[]);
  val neth_l = (UNDISCH o prove)
   (“integral_domain (r :'a Ring)
     ==> ((ring_of_int r (&1) = ring_of_int r (&0)) <=> F)”,
    REWRITE_TAC[RING_OF_INT_OF_NUM, RING_OF_NUM_0, RING_OF_NUM_1] THEN
    SIMP_TAC std_ss[integral_domain]);
  val neth_r = (UNDISCH o prove)
   (“integral_domain (r :'a Ring)
     ==> (ring_of_int r (&0) = ring_of_int r (&1) <=> F)”,
    REWRITE_TAC[RING_OF_INT_OF_NUM, RING_OF_NUM_0, RING_OF_NUM_1] THEN
    SIMP_TAC std_ss[integral_domain]);
  val neth_g = prove
   (“(ring_of_int r m :'a = ring_of_int r n <=> F) <=>
     ~(&(ring_char r) int_divides (m - n))”,
    REWRITE_TAC[RING_OF_INT_EQ]);
  val neth_h = prove
   (“(&(ring_char(r :'a Ring)) int_divides -(&n) <=> ring_char r divides n) /\
     (&(ring_char(r :'a Ring)) int_divides &n <=> ring_char r divides n)”,
    REWRITE_TAC[num_divides, INT_DIVIDES_NEG]);
  val rule1 = PART_MATCH (lhand o lhand) neth_g;
  val conv1 =
    RAND_CONV INT_SUB_CONV THENC
    GEN_REWRITE_CONV TRY_CONV [neth_h];
  fun RING_EQ_CONV tm =
    PART_MATCH lhand neth_b tm
    handle HOL_ERR _ =>
      PART_MATCH lhand neth_l tm
      handle HOL_ERR _ =>
        PART_MATCH lhand neth_r tm
        handle HOL_ERR _ =>
          let val th1 = rule1 tm;
              val th2 = CONV_RULE(RAND_CONV(RAND_CONV conv1)) th1
          in
            UNDISCH(snd(EQ_IMP_RULE th2))
          end
          handle HOL_ERR _ => failwith "RING_EQ_CONV";
  val dest_intconst = Arbrat.fromAInt o int_of_term;
  val mk_intconst = term_of_int o Arbrat.toAInt;
  fun dest_ringconst tm =
    if is_ring_of_int tm then
       dest_intconst (snd (dest_ring_of_int tm))
    else
       failwith "dest_ringconst";
  val mk_ringconst =
      let val ptm = “ring_of_int (r :'a Ring)” in
        fn n => mk_comb(ptm,mk_intconst n)
      end;
  val cth = prove
   (“ring_0 r :'a = ring_of_int r (&0) /\
     ring_1 r :'a = ring_of_int r (&1)”,
    REWRITE_TAC[RING_OF_INT_OF_NUM, RING_OF_NUM_0, RING_OF_NUM_1]);
  val decorule =
    GEN_REWRITE_CONV ONCE_DEPTH_CONV [cth, GSYM RING_OF_INT_OF_NUM];
  val (basic_rule,idealconv) =
    RING_AND_IDEAL_CONV
     (dest_ringconst,
      mk_ringconst,
      RING_EQ_CONV,
      “ring_neg(r :'a Ring)”,
      “ring_add(r :'a Ring)”,
      “ring_sub(r :'a Ring)”,
      “ring_inv(r :'a Ring)”,
      “ring_mul(r :'a Ring)”,
      “ring_div(r :'a Ring)”,
      “ring_pow(r :'a Ring)”,
      RING_INTEGRAL,TRUTH,RING_POLY_UNIVERSAL_CONV);
  fun rule tm =
    let val th = decorule tm in
      EQ_MP (SYM th) (basic_rule(rand(concl th)))
    end
in
val (RING_INTEGRAL_DOMAIN_UNIVERSAL,ring_ring_cofactors_universal) =
    (rule,idealconv)
end;

(* ------------------------------------------------------------------------- *)
(* Derived rule to take a theorem asserting a monomorphism between r and r'  *)
(* and a term that is some Boolean combination of equations in the ring r    *)
(* and prove it equivalent to a "transferred" version in r' where all the    *)
(* variables x (in r) in the original map to "f x" (in r').                  *)
(* ------------------------------------------------------------------------- *)

(* 3. RING_MONOMORPHIC_IMAGE_RULE *)
fun RING_MONOMORPHIC_IMAGE_RULE hth = let
    val pth = RING_MONOMORPHIC_IMAGE_RULE_THM;
    val ([pth_eq, pth_asm,
          pth_0, pth_1,
          pth_num, pth_int,
          pth_neg, pth_pow,
          pth_add, pth_sub], pth_mul) = splitlist CONJ_PAIR (MATCH_MP pth hth)
    and htm = rand(concl hth);
    fun mterm tm =
        if is_ring_0 tm then
           pth_0
        else if is_ring_1 tm then
           pth_1
        else if is_ring_of_num tm then
           SPEC (snd (dest_ring_of_num tm)) pth_num
        else if is_ring_of_int tm then
           SPEC (snd (dest_ring_of_int tm)) pth_int
        else if is_ring_neg tm then
           MATCH_MP pth_neg (mterm (snd (dest_ring_neg tm)))
        else if is_ring_pow tm then
           let val (_,s,n) = dest_ring_pow tm in
             MATCH_MP (SPEC n pth_pow) (mterm s)
           end
        else if is_ring_add tm then
           let val (_,s,t) = dest_ring_add tm in
             MATCH_MP pth_add (CONJ (mterm s) (mterm t))
           end
        else if is_ring_sub tm then
           let val (_,s,t) = dest_ring_sub tm in
             MATCH_MP pth_sub (CONJ (mterm s) (mterm t))
           end
        else if is_ring_mul tm then
           let val (_,s,t) = dest_ring_mul tm in
             MATCH_MP pth_mul (CONJ (mterm s) (mterm t))
           end
        else
           UNDISCH(SPEC tm pth_asm);
    fun mform tm =
      if is_neg tm then
         RAND_CONV mform tm
      else if is_iff tm orelse is_imp tm orelse is_conj tm orelse is_disj tm then
         BINOP_CONV mform tm
      else if is_eq tm then
         let val (s,t) = dest_eq tm in
           MATCH_MP pth_eq (CONJ (mterm s) (mterm t))
         end
      else
         failwith "RING_MONOMORPHIC_IMAGE_RULE: unhandled formula";
in
    mform
end;

(* ------------------------------------------------------------------------- *)
(* A decision procedure for the universal theory of rings, mapping           *)
(* momomorphically into a "total" ring to leverage earlier stuff.            *)
(* It will prove either the exact thing you request, or if you omit some     *)
(* carrier membership hypotheses, will add those as an antecedent.           *)
(* ------------------------------------------------------------------------- *)

(* 4. RING_WORD_UNIVERSAL *)
local
  val cth = prove
    (“ring_0 r = ring_of_int (r :'a Ring) (&0) /\
      ring_1 r = ring_of_int (r :'a Ring) (&1)”,
      REWRITE_TAC[RING_OF_INT_OF_NUM, RING_OF_NUM_0, RING_OF_NUM_1]);
  val pth = (UNDISCH o prove)
    (“ring_carrier r = univ(:'a) ==>
      (x = y <=> ring_sub r x y = ring_of_int r (&0))”,
      SIMP_TAC bool_ss[RING_SUB_EQ_0, IN_UNIV, RING_OF_INT_OF_NUM, RING_OF_NUM_0]);
  val bth = REFL “ring_of_int r (&0) :'a”;
  val mth = (UNDISCH o prove)
    (“ring_carrier r = univ(:'a) ==>
      p = ring_of_int r (&0) ==> !c. ring_mul r c p = ring_of_int r (&0)”,
      SIMP_TAC bool_ss[RING_MUL_RZERO, RING_OF_INT_OF_NUM, RING_OF_NUM_0, IN_UNIV]);
  val dth = (UNDISCH o prove)
    (“ring_carrier r = univ(:'a) ==>
      p = ring_of_int r (&0) /\ q = ring_of_int r (&0) ==>
        ring_add r p q = ring_of_int r (&0)”,
      SIMP_TAC bool_ss[RING_ADD_RZERO, RING_OF_INT_OF_NUM, RING_OF_NUM_0, IN_UNIV]);
  val decorule =
      GEN_REWRITE_RULE (RAND_CONV o ONCE_DEPTH_CONV)
                       [cth, GSYM RING_OF_INT_OF_NUM] o
      PART_MATCH lhand pth
in
fun RING_WORD_UNIVERSAL tm = let
      val (avs,bod) = strip_forall tm
    in
      if is_imp bod then let
        val (ant,con) = dest_imp bod;
        val aths =
          mapfilter (CONV_RULE decorule) (CONJUNCTS(ASSUME ant))
        and cth = decorule con;
        val atms = map (lhand o concl) aths
        and ctm = lhand(rand(concl cth));
        val ctms = ring_ring_cofactors_universal atms ctm;
        val zths = map2 (fn c => fn th => SPEC c (MATCH_MP mth th)) ctms aths;
        val zth =
          end_itlist (fn th1 => fn th2 => MATCH_MP dth (CONJ th1 th2)) zths;
        val eth =
          TRANS (RING_POLY_UNIVERSAL_CONV ctm)
                (SYM(RING_POLY_UNIVERSAL_CONV (lhand(concl zth))))
      in
        GENL avs (DISCH ant (EQ_MP (SYM cth) (TRANS eth zth)))
      end
      else
        let val th1 = decorule tm;
            val th2 = CONV_RULE
                        (RAND_CONV (LAND_CONV RING_POLY_UNIVERSAL_CONV)) th1
        in
          EQ_MP (SYM th2) bth
        end
    end
end;

(* 5. RING_RING_WORD *)
local
  (* NOTE: These rules require Ho_Rewrite.GEN_REWRITE_RULE *)
  val imp_imp_rule     = GEN_REWRITE_RULE TRY_CONV [IMP_IMP];
  val left_exists_rule = GEN_REWRITE_RULE TRY_CONV
                                          [LEFT_FORALL_IMP_THM];
  val or_elim_rule     = GEN_REWRITE_RULE TRY_CONV
                           [TAUT `(p ==> q) /\ (p' ==> q) <=> p \/ p' ==> q`];
in
  fun RING_RING_WORD ths tm = let
      val dty = type_of(rand tm);
      val rty = mk_type(ring_tyname,[dty]);
      val rtms = filter (curry (=) rty o type_of) (freesl(tm::map concl ths))
   in
      if length rtms <> 1
      then failwith "RING_RULE: can't deduce which ring" else
      let val rtm = hd rtms;
          val tvs = itlist (union o type_vars_in_term o concl) ths
                           (type_vars_in_term tm);
          val dty' = mk_vartype("Z"^itlist (curry (^) o dest_vartype) tvs "");
          val rty' = mk_type(ring_tyname,[dty']);
          val avvers = HOLset.listItems
                         (itlist (fn th => fn s =>
                                    HOLset.addList (s,all_vars (concl th))) ths
                                 (HOLset.addList (empty_tmset, all_vars tm)));
          val rtm' = variant avvers (mk_var("r'",rty'))
          and htm = variant avvers (mk_var("h",dty --> dty'));
          val hasm = list_mk_icomb ring_monomorphism_tm [mk_pair(rtm,rtm'), htm];
          val hth = ASSUME hasm;
          val ths' = mapfilter (CONV_RULE(RING_MONOMORPHIC_IMAGE_RULE hth)) ths;
          val th' = RING_MONOMORPHIC_IMAGE_RULE hth tm;
          val utm =
              if null ths' then rand(concl th')
              else mk_imp(list_mk_conj (map concl ths'),rand(concl th'));
       (* NOTE: HOL-Light's "find_terms" also removes duplication, we can use
                liteLib.setify_term in addition to HOL4's find_terms. *)
          val hvs = find_terms
               (fn t => is_comb t andalso
                        rator t ~~ htm andalso is_var(rand t)) utm |> setify_term;
          val gvs = map (genvar o type_of) hvs;
       (* "let vtm = subst (zip gvs hvs) utm in" (hvs |-> gvs) *)
          val vtm = subst (map2 (fn s => fn t => s |-> t) hvs gvs) utm;
          val aty = Type.alpha;
          val arty = mk_type(ring_tyname,[aty]);
          val atm =
              subst [mk_var(fst(dest_var rtm'),arty) |-> mk_var("r",arty)]
                    (inst [dty' |-> aty] vtm);
          val th1 = RING_WORD_UNIVERSAL atm;
          val th2 = INST_TYPE [aty |-> dty'] th1;
          val th3 = INST [mk_var("r",rty') |-> rtm'] th2;
       (* "let th4 = INST (zip hvs gvs) th3 in" (gvs |-> hvs) *)
          val th4 = INST (map2 (fn s => fn t => s |-> t) gvs hvs) th3;
          val th5 = if null ths' then th4
                    else MP th4 (end_itlist CONJ ths');
          val th6 = itlist PROVE_HYP ths (EQ_MP (SYM th') th5);
          val ueq = mk_eq(list_mk_icomb ring_carrier_tm [rtm'],
                          inst [aty |-> dty'] univ_tm);
          val th7 = imp_imp_rule (DISCH ueq (DISCH hasm th6));
          val th8 = left_exists_rule(GEN htm th7);
          val th9 = left_exists_rule(GEN rtm' th8);
          val th10 = ISPEC rtm RING_TOTALIZATION;
          val th11 = CONJ (PART_MATCH lhand th9 (lhand(concl th10)))
                          (PART_MATCH lhand th9 (rand(concl th10)));
      in
        MP (or_elim_rule th11) th10
      end
    end
end;

(* 6. RING_RING_HORN *)
local
  val ddj_conv =
      GEN_REWRITE_CONV (RAND_CONV o DEPTH_CONV)
        [TAUT ‘~p \/ ~q <=> ~(p /\ q)’] THENC
      GEN_REWRITE_CONV TRY_CONV  [TAUT ‘p \/ ~q <=> q ==> p’]
in
  fun RING_RING_HORN tm =
    if not(is_disj tm) then RING_RING_WORD [] tm else
       let val th0 = ddj_conv tm;
           val tm' = rand(concl th0);
           val abod = lhand tm';
           val ths = CONJUNCTS(ASSUME abod);
           val th1 = RING_RING_WORD ths (rand tm')
       in
           EQ_MP (SYM th0) (DISCH abod (itlist PROVE_HYP ths th1))
       end
end;

(* 7. RING_RING_CORE *)
local
  val pth = TAUT ‘p ==> q <=> (p \/ q <=> q)’
  and ptm = “p:bool” and qtm = “q:bool”
in
  fun RING_RING_CORE tm = let
      val (negdjs,posdjs) = partition is_neg (strip_disj tm);
      val th = tryfind
                 (fn p => RING_RING_HORN (list_mk_disj(p::negdjs))) posdjs;
      val th1 = INST [ptm |-> concl th, qtm |-> tm] pth;
      val tm2 = rand(concl th1);
    in
      MP (EQ_MP (SYM th1) (DISJ_ACI_RULE tm2)) th
    end
end;

(* 8. init_conv *)
val init_conv =
    TOP_DEPTH_CONV BETA_CONV THENC
    PRESIMP_CONV THENC
    CONDS_ELIM_CONV THENC
    NNFC_CONV THENC CNF_CONV THENC
    SKOLEM_CONV THENC PRENEX_CONV THENC
    GEN_REWRITE_CONV REDEPTH_CONV
       [RIGHT_AND_EXISTS_THM, LEFT_AND_EXISTS_THM] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [GSYM DISJ_ASSOC] THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [GSYM CONJ_ASSOC];

(* 9. RING_RULE_BASIC *)
fun RING_RULE_BASIC tm = let
    val (avs,bod) = strip_forall tm;
    val th1 = init_conv bod;
    val tm' = rand(concl th1);
    val (avs',bod') = strip_forall tm';
    val th2 = end_itlist CONJ (map RING_RING_CORE (strip_conj bod'));
    val th3 = EQ_MP (SYM th1) (GENL avs' th2);
    val imps = hyp th3;
    val th4 =
      if null imps then th3
      else DISCH_ALL
             (itlist PROVE_HYP (CONJUNCTS(ASSUME(list_mk_conj imps))) th3)
in
    GENL avs th4
end;

(* 10. RING_RULE

   The final version of RULE_RULE only temporarily changes the type variable
   alpha of input term to something fresh and then call RING_RULE_BASIC to
   do the actual job.
 *)
fun RING_RULE tm = let
    val tvs = type_vars_in_term tm;
    val ty = mk_vartype("Y" ^ itlist (curry (^) o dest_vartype) tvs "");
    val aty = Type.alpha;
    val tm' = inst [aty |-> ty] tm;
in
    INST_TYPE [ty |-> aty] (RING_RULE_BASIC tm')
end;

(* ------------------------------------------------------------------------- *)
(* A naive tactic form, pulling in equations in the assumptions and          *)
(* either solving outright or leaving some ring carrier membership           *)
(* ------------------------------------------------------------------------- *)

(* 11. RING_TAC *)
val RING_TAC = let
    fun check p x = if p x then x else failwith "check in RING_TAC"
in
  REPEAT GEN_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_eq o concl))) THEN
  W(fn (asl,w) =>
       let val th = RING_RULE w in
          (MATCH_ACCEPT_TAC th ORELSE
           ((fn g => MATCH_MP_TAC th g) THEN ASM_REWRITE_TAC[]))
       end)
end;

end (* struct *)
