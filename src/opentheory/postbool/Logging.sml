structure Logging :> Logging =
struct

open OpenTheoryCommon
structure Map = OpenTheoryMap.Map

val ERR = Feedback.mk_HOL_ERR "Logging"

fun uptodate_const Thy Name =
  Theory.uptodate_term (Term.prim_mk_const {Thy=Thy,Name=Name})
  handle Feedback.HOL_ERR {origin_function="prim_mk_const",...} => false

val verbosity = ref 0
val _ = Feedback.register_trace("opentheory logging",verbosity,5)

val proof_type = let open Thm fun
 f Axiom_prf = "Axiom"
|f (ABS_prf _) = "ABS"
|f (ALPHA_prf _) = "ALPHA"
|f (AP_TERM_prf _) = "AP_TERM"
|f (AP_THM_prf _) = "AP_THM"
|f (ASSUME_prf _) = "ASSUME"
|f (BETA_CONV_prf _) = "BETA_CONV"
|f (CCONTR_prf _) = "CCONTR"
|f (CHOOSE_prf _) = "CHOOSE"
|f (CONJ_prf _) = "CONJ"
|f (CONJUNCT1_prf _) = "CONJUNCT1"
|f (CONJUNCT2_prf _) = "CONJUNCT2"
|f (DISCH_prf _) = "DISCH"
|f (DISJ_CASES_prf _) = "DISJ_CASES"
|f (DISJ1_prf _) = "DISJ1"
|f (DISJ2_prf _) = "DISJ2"
|f (EQ_IMP_RULE1_prf _) = "EQ_IMP_RULE1"
|f (EQ_IMP_RULE2_prf _) = "EQ_IMP_RULE2"
|f (EQ_MP_prf _) = "EQ_MP"
|f (EXISTS_prf _) = "EXISTS"
|f (GEN_prf _) = "GEN"
|f (GEN_ABS_prf _) = "GEN_ABS"
|f (INST_TYPE_prf _) = "INST_TYPE"
|f (INST_prf _) = "INST"
|f (MK_COMB_prf _) = "MK_COMB"
|f (MP_prf _) = "MP"
|f (NOT_INTRO_prf _) = "NOT_INTRO"
|f (NOT_ELIM_prf _) = "NOT_ELIM"
|f (REFL_prf _) = "REFL"
|f (SPEC_prf _) = "SPEC"
|f (SUBST_prf _) = "SUBST"
|f (SYM_prf _) = "SYM"
|f (TRANS_prf _) = "TRANS"
|f (Beta_prf _) = "Beta"
|f (Def_tyop_prf _) = "Def_tyop"
|f (Def_const_prf _) = "Def_const"
|f (Def_const_list_prf _) = "Def_const_list"
|f (Def_spec_prf _) = "Def_spec"
|f (Mk_abs_prf _) = "Mk_abs"
|f (Mk_comb_prf _) = "Mk_comb"
|f (Specialize_prf _) = "Specialize"
|f (deductAntisym_prf _) = "deductAntisym"
in f end

datatype log_state =
  Not_logging
| Active_logging of TextIO.outstream

val log_state = ref Not_logging

fun log_raw s =
  case !log_state of
    Active_logging h => TextIO.output (h,s^"\n")
  | Not_logging => ()

fun log_num n = log_raw (Int.toString n)

fun log_name s = log_raw ("\""^(OpenTheoryMap.otname_to_string s)^"\"")

fun log_comment s = log_raw ("#"^(String.translate (fn #"\n" => "\n#" | c => String.str c) s))

fun log_command s = log_raw s

fun log_nil () = log_command "nil"

fun log_list log = let
  fun logl []     = log_nil ()
    | logl (h::t) = (log h; logl t; log_command "cons")
in logl end

fun log_pair (loga,logb) (a,b) = let
  val _ = loga a
  val _ = logb b
  val _ = log_nil ()
  val _ = log_command "cons"
  val _ = log_command "cons"
in () end

fun log_redres loga logb {redex,residue} =
  log_pair (loga,logb) (redex,residue)

type thy_tyop  = OpenTheoryMap.thy_tyop
type thy_const = OpenTheoryMap.thy_const
type otname    = OpenTheoryMap.otname

val (log_term, log_thm, log_clear,
     set_const_name_handler, reset_const_name_handler,
     set_tyop_name_handler, reset_tyop_name_handler) = let
  val (reset_key,next_key) = let
    val key = ref 0
    fun reset() = key := 0
    fun next()  = let val k = !key in (key := k+1; k) end
    in (reset,next) end

  val (reset_dict,peek_dict,save_dict) = let
    fun new_dict() = Map.mkDict object_compare
    val dict = ref (new_dict())
    fun reset() = dict := new_dict()
    fun peek x = Map.peek(!dict,x)
    fun save x = case peek x of
      SOME k => k
    | NONE => let
        val k = next_key()
        val _ = dict := Map.insert(!dict,x,k)
        val _ = log_num k
        val _ = log_command "def"
      in k end
    in (reset,peek,save) end
  fun saved ob = case peek_dict ob of
    SOME k => let
      val _ = log_num k
      val _ = log_command "ref"
      in true end
  | NONE => false

  fun log_type_var ty = log_name (tyvar_to_ot (Type.dest_vartype ty))

  local
    open OpenTheoryMap
    fun default_tnh t = raise ERR "log_tyop_name"
      ("No OpenTheory name for type "^(#Thy t)^"$"^(#Tyop t))
    fun default_cnh c = raise ERR "log_const_name"
      ("No OpenTheory name for constant "^(#Thy c)^"$"^(#Name c))
    val tnh = ref default_tnh
    val cnh = ref default_cnh
  in
    fun log_tyop_name tyop = let
      val n = Map.find(tyop_to_ot_map(),tyop)
              handle Map.NotFound => (!tnh) tyop
      val _ = log_name n
      in n end
    fun log_const_name {Thy="Logging",Name} =
      log_raw ("\""^Name^"\"")
    |   log_const_name const = let
      val n = Map.find(const_to_ot_map(),const)
              handle Map.NotFound => (!cnh) const
      in log_name n end
    fun set_const_name_handler h =
      cnh := (fn c => h c handle _ => default_cnh c)
    fun reset_const_name_handler() = cnh := default_cnh
    fun set_tyop_name_handler h =
      tnh := (fn t => h t handle _ => default_tnh t)
    fun reset_tyop_name_handler() = tnh := default_tnh
  end

  fun log_tyop tyop = let
    val ob = OTypeOp tyop
  in if saved ob then () else let
    val _ = log_tyop_name tyop
    val _ = log_command "typeOp"
    val _ = save_dict ob
    in () end
  end

  fun log_const const = let
    val ob = OConst const
  in if saved ob then () else let
    val _ = log_const_name const
    val _ = log_command "const"
    val _ = save_dict ob
    in () end
  end

  fun log_type ty = let
    val ob = OType ty
  in if saved ob then () else let
    open Feedback
    val _ = let
      val {Thy,Args,Tyop} = Type.dest_thy_type ty
      val _ = log_tyop {Thy=Thy,Tyop=Tyop}
      val _ = log_list log_type Args
      val _ = log_command "opType"
    in () end handle HOL_ERR {origin_function="dest_thy_type",...} => let
      val _ = log_type_var ty
      val _ = log_command "varType"
    in () end
    val _ = save_dict ob
    in () end
  end

  fun log_var v = let
    val ob = OVar v
  in if saved ob then () else let
    val (n,ty) = Term.dest_var v
    val _ = log_name ([],n)
    val _ = log_type ty
    val _ = log_command "var"
    val _ = save_dict ob
    in () end
  end

  fun strip_old s = let
    open Substring
    val s = triml 3 (trimr 5 (full s))
    val (_,s) = splitl Char.isDigit s
    val s = triml 2 s
  in string s end

  fun log_term tm = let
    val ob = OTerm tm
  in if saved ob then () else let
    open Term Feedback
    val _ = let
      val {Thy,Name,Ty} = dest_thy_const tm
      val Name = if uptodate_const Thy Name then Name else strip_old Name
      val _ = log_const {Thy=Thy,Name=Name}
      val _ = log_type Ty
      val _ = log_command "constTerm"
    in () end handle HOL_ERR {origin_function="dest_thy_const",...} => let
      val (t1,t2) = dest_comb tm
      val _ = log_term t1
      val _ = log_term t2
      val _ = log_command "appTerm"
    in () end handle HOL_ERR {origin_function="dest_comb",...} => let
      val (v,b) = dest_abs tm
      val _ = log_var v
      val _ = log_term b
      val _ = log_command "absTerm"
    in () end handle HOL_ERR {origin_function="dest_abs",...} => let
      val _ = log_var tm
      val _ = log_command "varTerm"
    in () end
    val _ = save_dict ob
    in () end
  end

  val log_subst =
    log_pair
      (log_list (log_redres log_type_var log_type),
       log_list (log_redres log_var log_term))
  fun log_type_subst s = log_subst (s,[])
  fun log_term_subst s = log_subst ([],s)

  (* Attribution: ideas (and code) for reconstructing DISCH, SPEC, GEN, etc.
                  taken from HOL Light *)
  local open Thm Conv boolTheory boolSyntax Term Type Lib Drule in
    fun proveHyp th1 th2 =
    case HOLset.find (aconv (concl th1)) (hypset th2) of
        SOME _ => EQ_MP (deductAntisym th1 th2) th1
      | NONE => th2
    val p = ``p:bool``
    val q = ``q:bool``
    val eqtIntro = let
      val pth = let
        val th1 = deductAntisym (ASSUME p) TRUTH
        val th2 = EQT_ELIM(ASSUME(concl th1))
        in deductAntisym th2 th1 end
      in fn th => EQ_MP (INST[p|->concl th] pth) th end
    (* These are in the OpenTheory standard library, so we can give them axiom proofs *)
    val IMP_DEF = mk_thm([],``$==> = \p q. p /\ q <=> p``)
    val EXISTS_DEF = mk_thm([],``$? = \P:'a->bool. !q. (!x. P x ==> q) ==> q``)
    val AND_DEF = mk_thm([],``$/\ = \p q. (\f:bool->bool->bool. f p q) = (\f. f T T)``)
    val EXISTS_THM = boolTheory.EXISTS_DEF
    val DISCH_pth = SYM(BETA_RULE (AP_THM (AP_THM IMP_DEF p) q))
    val MP_pth = let
      val th1 = BETA_RULE (AP_THM (AP_THM IMP_DEF p) q)
      val th2 = EQ_MP th1 (ASSUME ``p ==> q``)
    in CONJUNCT2 (EQ_MP (SYM th2) (ASSUME p)) end
    val P = mk_var("P",alpha-->bool)
    val x = mk_var("x",alpha)
    val SPEC_pth = let
      val th1 = EQ_MP (AP_THM FORALL_DEF P) (ASSUME (mk_comb(universal,P)))
      val th2 = AP_THM (CONV_RULE BETA_CONV th1) x
      val th3 = CONV_RULE (RAND_CONV BETA_CONV) th2
      in DISCH_ALL (EQT_ELIM th3) end
    val GEN_pth = let
      val th1 = ASSUME (mk_eq(P,mk_abs(x,T)))
      val th2 = AP_THM FORALL_DEF P
    in EQ_MP (SYM(CONV_RULE(RAND_CONV BETA_CONV) th2)) th1 end
    val Q = mk_var("Q",bool)
    val EXISTS_pth = let
      val th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM EXISTS_DEF P)
      val tm  = (mk_forall(x,mk_imp(mk_comb(P,x),Q)))
      val th2 = SPEC x (ASSUME tm)
      val th3 = DISCH tm (MP th2 (ASSUME (mk_comb(P,x))))
    in EQ_MP (SYM th1) (GEN Q th3) end
    val CHOOSE_pth = let
      val th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM EXISTS_DEF P)
      val th2 = SPEC Q (UNDISCH(fst(EQ_IMP_RULE th1)))
    in DISCH_ALL (DISCH (mk_comb(existential,P)) (UNDISCH th2)) end
    val f = mk_var("f",bool-->bool-->bool)
    val CONJ_pth = let
      val pth = ASSUME p
      val qth = ASSUME q
      val th1 = MK_COMB(AP_TERM f (eqtIntro pth),eqtIntro qth)
      val th2 = ABS f th1
      val th3 = BETA_RULE (AP_THM (AP_THM AND_DEF p) q)
      in EQ_MP (SYM th3) th2 end
    val P = mk_var("P",bool)
    val REBETA_RULE = CONV_RULE(REDEPTH_CONV BETA_CONV)
    fun CONJUNCT_pth t = let
      val th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM AND_DEF P)
      val th2 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM th1 Q)
      val th3 = EQ_MP th2 (ASSUME (mk_conj(P,Q)))
      in EQT_ELIM(REBETA_RULE (AP_THM th3 (mk_abs(p,mk_abs(q,t))))) end
    val CONJUNCT1_pth = CONJUNCT_pth p
    val CONJUNCT2_pth = CONJUNCT_pth q
    val th1 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM OR_DEF P)
    val th2 = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM th1 Q)
    fun DISJ_pth t = let
      val th3 = MP (ASSUME (mk_imp(t,p))) (ASSUME t)
      val th4 = GEN p (DISCH (mk_imp(P,p)) (DISCH (mk_imp(Q,p)) th3))
      in EQ_MP (SYM th2) th4 end
    val DISJ1_pth = DISJ_pth P
    val DISJ2_pth = DISJ_pth Q
    val R = mk_var("R",bool)
    val DISJ_CASES_pth = let
      val th3 = SPEC R (EQ_MP th2 (ASSUME (mk_disj(P,Q))))
    in UNDISCH (UNDISCH th3) end
    val NOT_ELIM_pth = CONV_RULE (RAND_CONV BETA_CONV) (AP_THM NOT_DEF P)
    val NOT_INTRO_pth = SYM NOT_ELIM_pth
    val SEL_CONV = RATOR_CONV (REWR_CONV EXISTS_THM) THENC BETA_CONV
    val SEL_RULE = CONV_RULE SEL_CONV
    fun specify c (th,defs) = let
      val th1 = SEL_RULE th
      val (l,r) = dest_comb(concl th1)
      val {Thy,Name,...} = dest_thy_const c
      val Name = if uptodate_const Thy Name then Name else strip_old Name
      val th2 = mk_proof_thm (Def_const_prf({Thy=Thy,Name=Name},r)) ([],mk_eq(c,r))
      val defs = th2 :: defs
      val th = CONV_RULE BETA_CONV (EQ_MP (AP_TERM l (SYM th2)) th1)
      in (th,defs) end
    val EXISTENCE_RULE = CONV_RULE (SEL_CONV THENC (RATOR_CONV ETA_CONV))
    fun mk_ra (b,r,rep,abs) = mk_eq(mk_abs(r,mk_eq(mk_comb(rep,mk_comb(abs,r)),r)),
                                    mk_abs(r,mk_comb(b,r)))
    fun mk_ar (abs,rep,a)   = mk_eq(mk_abs(a,mk_comb(abs,mk_comb(rep,a))),
                                    mk_abs(a,a))
    fun absspec x th = CONV_RULE(BINOP_CONV BETA_CONV)(AP_THM th x)
    val Def_tyop_pth = let
      val phi = mk_var("phi",alpha-->bool)
      val abs = mk_var("abs",alpha-->beta)
      val rep = mk_var("rep",beta-->alpha)
      val a   = mk_var("a",beta)
      val r   = mk_var("r",alpha)
      val ar  = ASSUME (mk_ar(abs,rep,a))
      val ra  = ASSUME (mk_ra(phi,r,rep,abs))
      val c             = concl TYPE_DEFINITION
      val tyd           = lhs c
      val (c1,c2)       = dest_conj(snd(dest_abs(snd(dest_abs(rhs c)))))
      val ([x',x''],_)  = strip_forall c1
      val (x,_)         = dest_forall c2
      val w   = mk_comb(mk_comb(tyd,phi),rep)
      val th1 = BETA_RULE (AP_THM (AP_THM TYPE_DEFINITION phi) rep)
      val rx' = mk_comb(rep,x')
      val rr  = mk_eq(rx',mk_comb(rep,x''))
      val xar = absspec x' ar
      val th2 = TRANS (TRANS (SYM xar) (AP_TERM abs (ASSUME rr))) (absspec x'' ar)
      val th3 = GEN x' (GEN x'' (DISCH rr th2))
      val phx = mk_comb(phi,x)
      val xre = mk_eq(x,rx')
      val exr = mk_exists(x',xre)
      val xra = absspec x ra
      val th4 = DISCH phx (EXISTS (exr,mk_comb(abs,x)) (SYM (EQ_MP (SYM xra) (ASSUME phx))))
      val xrt = ASSUME xre
      val th5 = TRANS (REFL rx') (SYM xrt)
      val th6 = TRANS (AP_TERM rep (TRANS (AP_TERM abs xrt) xar)) th5
      val th7 = DISCH exr (CHOOSE (x',ASSUME exr) (EQ_MP xra th6))
      val th8 = GEN x (deductAntisym (UNDISCH th7) (UNDISCH th4))
      in EXISTS (mk_exists(rep,w),rep) (EQ_MP (SYM th1) (CONJ th3 th8)) end
  end

  fun log_thm th = let
    open Thm Term Type Lib Drule Conv boolSyntax Feedback
    val ob = OThm th
  in if saved ob then () else let
    val ths = Susp.delay (fn () => (Lib.ppstring Parse.pp_thm th))
    val pt  = proof_type (proof th)
    val _ = if !verbosity >= 4 then HOL_MESG("Start a "^pt^" proof for "^(Susp.force ths))
       else if !verbosity >= 3 then HOL_MESG(proof_type (proof th))
       else ()
    (*
    val _ = log_comment ("("^pt)
    *)
    val _ = case proof th of

      Axiom_prf => let
      val _ = log_list log_term (hyp th)
      val _ = log_term (concl th)
      val _ = log_command "axiom"
      in () end
    | ASSUME_prf tm => let
      val _ = log_term tm
      val _ = log_command "assume"
      in () end
    | BETA_CONV_prf tm => let
      val _ = log_term tm
      val _ = log_command "betaConv"
      in () end
    | REFL_prf tm => let
      val _ = log_term tm
      val _ = log_command "refl"
      in () end
    | Def_const_prf (c,t) => let
      val _ = log_const_name c
      val _ = log_term t
      val _ = log_command "defineConst"
      val k = save_dict ob
      val _ = log_command "pop"
      val _ = save_dict (OConst c)
      val _ = log_command "pop"
      val _ = log_num k
      val _ = log_command "ref"
      in () end
    | ABS_prf (v,th) => let
      val _ = log_var v
      val _ = log_thm th
      val _ = log_command "absThm"
      in () end
    | deductAntisym_prf (th1,th2) => let
      val _ = log_thm th1
      val _ = log_thm th2
      val _ = log_command "deductAntisym"
      in () end
    | EQ_MP_prf (th1,th2) => let
      val _ = log_thm th1
      val _ = log_thm th2
      val _ = log_command "eqMp"
      in () end
    | INST_prf (s,th) => let
      val _ = log_term_subst s
      val _ = log_thm th
      val _ = log_command "subst"
      in () end
    | INST_TYPE_prf (s,th) => let
      val _ = log_type_subst s
      val _ = log_thm th
      val _ = log_command "subst"
      in () end
    | MK_COMB_prf (th1,th2) => let
      val _ = log_thm th1
      val _ = log_thm th2
      val _ = log_command "appThm"
      in () end
    | ALPHA_prf (t1,t2) => let
      val t = mk_comb(inst[alpha|->type_of t1]equality, t1)
      val _ = log_thm (EQ_MP (MK_COMB (REFL t, REFL t2)) (REFL t1))
      in () end
    | TRANS_prf (th1,th2) => let
      val _ = log_thm th1
      val _ = log_thm th2
      val _ = log_command "trans"
      in () end
    | SYM_prf th => let
      val _ = log_thm th
      val _ = log_command "sym"
      in () end
    | AP_TERM_prf (tm,th) => log_thm (MK_COMB(REFL tm, th))
    | AP_THM_prf  (th,tm) => log_thm (MK_COMB(th, REFL tm))
    | Mk_comb_prf (th,th1,th2) => log_thm (TRANS th (MK_COMB(th1,th2)))
    | Mk_abs_prf (th,bv,th1) => log_thm (TRANS th (ABS bv th1))
    | CONJ_prf (th1,th2) => let
      val th = INST [p|->concl th1,q|->concl th2] CONJ_pth
      val _ = log_thm (proveHyp th2 (proveHyp th1 th))
      in () end
    | CONJUNCT1_prf th => let
      val (l,r) = dest_conj(concl th)
      val _ = log_thm (proveHyp th (INST [P|->l,Q|->r] CONJUNCT1_pth))
      in () end
    | CONJUNCT2_prf th => let
      val (l,r) = dest_conj(concl th)
      val _ = log_thm (proveHyp th (INST [P|->l,Q|->r] CONJUNCT2_pth))
      in () end
    | DISCH_prf (tm,th) => let
      val th1 = CONJ (ASSUME tm) th
      val th2 = CONJUNCT1 (ASSUME (concl th1))
      val pth = INST [p|->tm, q|->concl th] DISCH_pth
      val _ = log_thm (EQ_MP pth (deductAntisym th1 th2))
      in () end
    | MP_prf (th1,th2) => let
      val tm = concl th1
      val (ant,con) = dest_imp tm
      val th1 = if is_neg tm
                then let open boolTheory in
                       (CONV_RULE BETA_CONV)
                       (SUBS_OCCS [([1],NOT_DEF)] th1)
                     end
                else th1
      val pth = INST [p|->ant, q|->con] MP_pth
      val _ = log_thm (EQ_MP (deductAntisym th1
                               (EQ_MP (deductAntisym th2 pth)
                                      th2))
                             th1)
      in () end
    | SUBST_prf (map,tm,sth) => let
      val (h,source) = dest_thm sth
      val fvs = FVL (source::h) empty_varset
      fun f (m as {redex,residue},(fvs,allfvs,map,tm)) = let
        val (h,c) = dest_thm residue
        val allfvs = FVL (c::h) allfvs
      in
        if HOLset.member(fvs,redex) then let
            val vv = prim_variant (HOLset.listItems fvs) redex
            val fvs = HOLset.add(fvs,vv)
            val m = {redex=vv,residue=residue}
            val tm = subst [redex|->vv] tm
          in (fvs,allfvs,m::map,tm) end
        else (fvs,allfvs,m::map,tm)
      end
      val (_,fvs,map,tm) = foldl f (fvs,fvs,[],tm) map
      fun rconv fvs source template = (* |- source = template[rhs/vars] *)
        ALPHA source template
      handle HOL_ERR _ =>
        if is_var template
        then valOf(subst_assoc (equal template) map)
      else let
        val (sf,sa) = dest_comb source
        val (tf,ta) = dest_comb template
        val f = rconv fvs sf tf
        val a = rconv fvs sa ta
      in MK_COMB (f,a) end handle HOL_ERR _ => let
        val (sv,sb) = dest_abs source
        val (tv,tb) = dest_abs template
        val vv = prim_variant (HOLset.listItems fvs) tv
        val sb = subst [sv|->vv] sb
        val tb = subst [tv|->vv] tb
        val b = rconv (HOLset.add(fvs,vv)) sb tb
      in ABS vv b end
      val _ = log_thm (EQ_MP (rconv fvs source tm) sth)
      in () end
    | GEN_prf (v,th) => let
      val vty = type_of v
      val P   = mk_var("P",vty-->bool)
      val pth = INST_TY_TERM ([P|->mk_abs(v,concl th)],[alpha|->vty]) GEN_pth
      val _ = log_thm (proveHyp (ABS v (eqtIntro th)) pth)
      in () end
    | DISJ1_prf (th,tm) => let
      val _ = log_thm (proveHyp th (INST [P|->concl th,Q|->tm] DISJ1_pth))
      in () end
    | DISJ2_prf (tm,th) => let
      val _ = log_thm (proveHyp th (INST [Q|->concl th,P|->tm] DISJ2_pth))
      in () end
    | SPEC_prf (tm,th) => let
      val abs = rand(concl th)
      val (v,_) = dest_abs abs
      val vty = type_of v
      val pth = INST_TY_TERM ([mk_var("P",vty-->bool)|->abs,mk_var("x",vty)|->tm],[alpha|->vty]) SPEC_pth
      val _ = log_thm (CONV_RULE BETA_CONV (MP pth th))
      in () end
    | Specialize_prf (t,th) => log_thm (SPEC t th)
    | GEN_ABS_prf (c,vlist,th) => let
      val dom = fst o dom_rng
      fun foo th = let val (_,_,ty) = dest_eq_ty(concl th) in dom ty end
      val f = case c of
        SOME c => let val ty = dom(dom(type_of c))
        in fn th => AP_TERM (inst[ty|->foo th] c) th end
      | NONE => I
      val _ = log_thm (List.foldr (f o uncurry ABS) th vlist)
      in () end
    | EQ_IMP_RULE1_prf th => let
      val (t1,t2) = dest_eq(concl th)
      val _ = log_thm (DISCH t1 (EQ_MP th (ASSUME t1)))
      in () end
    | EQ_IMP_RULE2_prf th => let
      val (t1,t2) = dest_eq(concl th)
      val _ = log_thm (DISCH t2 (EQ_MP (SYM th) (ASSUME t2)))
      in () end
    | EXISTS_prf (fm,tm,th) => let
      val ty = type_of tm
      val (_,abs) = dest_comb fm
      val bth = BETA_CONV(mk_comb(abs,tm))
      val cth = INST_TY_TERM ([mk_var("P",ty-->bool)|->abs,mk_var("x",ty)|->tm],[alpha|->ty]) EXISTS_pth
      val _ = log_thm (proveHyp (EQ_MP (SYM bth) th) cth)
      in () end
    | CHOOSE_prf (v,th1,th2) => let
      val vty = type_of v
      val abs = rand(concl th1)
      val (bv,bod) = dest_abs abs
      val cmb = mk_comb(abs,v)
      val pat = subst [bv|->v] bod
      val th3 = CONV_RULE BETA_CONV (ASSUME cmb)
      val th4 = GEN v (DISCH cmb (MP (DISCH pat th2) th3))
      val th5 = INST_TY_TERM ([mk_var("P",vty-->bool)|->abs,Q|->concl th2],[alpha|->vty]) CHOOSE_pth
      val _ = log_thm (MP (MP th5 th4) th1)
      in () end
    | DISJ_CASES_prf (th0,th1,th2) => let
      val c1 = concl th1
      val c2 = concl th2
      val (l,r) = dest_disj (concl th0)
      val th = INST [P|->l,Q|->r,R|->c1] DISJ_CASES_pth
      val _ = log_thm (proveHyp (DISCH r th2) (proveHyp (DISCH l th1) (proveHyp th0 th)))
      in () end
    | NOT_INTRO_prf th => let
      val _ = log_thm (EQ_MP (INST [P|->rand(rator(concl th))] NOT_INTRO_pth) th)
      in () end
    | NOT_ELIM_prf th => let
      val _ = log_thm (EQ_MP (INST [P|->rand(concl th)] NOT_ELIM_pth) th)
      in () end
    | CCONTR_prf (tm,th) => let
      open boolTheory
      val th1 = RIGHT_BETA(AP_THM NOT_DEF tm)
      val tmF = ASSUME(mk_eq(tm,F))
      val th2 = EQT_ELIM (ASSUME(mk_eq(tm,T)))
      val th3 = SUBST [P|->th1] (mk_imp(P,F)) (DISCH (mk_neg tm) th)
      val th4 = SUBST [P|->(tmF)] (mk_imp(mk_imp(P,F),F)) th3
      val th5 = MP th4 (SPEC F FALSITY)
      val th6 = EQ_MP (SYM(tmF)) th5
      val _ = log_thm (DISJ_CASES (SPEC tm BOOL_CASES_AX) th2 th6)
      in () end
    | Beta_prf th => log_thm (RIGHT_BETA th)
    | Def_spec_prf (cs,th) => let
      val (th,defs) = rev_itlist specify cs (th,[])
      val _ = app log_thm (rev defs)
      val _ = log_thm th
      in () end
    | Def_const_list_prf (thyname,stys,th) => let
      val nvars = map (fn (s,ty) => ({Thy=thyname,Name=s},mk_var(s,ty))) stys
      val _ = log_list (log_pair (log_const_name, log_var)) nvars
      val _ = log_thm th
      val _ = log_command "defineConstList"
      val k = save_dict ob
      val _ = log_command "pop"
      val _ = app (fn _ => log_command "hdTl") nvars
      val _ = log_command "pop"
      val _ = app (ignore o save_dict o OConst o #1) (rev nvars)
      val _ = log_num k
      val _ = log_command "ref"
      in () end
    | Def_tyop_prf (name,tyvars,th,aty) => let
      val n = log_tyop_name name
      val (ns,n) = n
      val ns'    = ns@[n]
      val abs_name = (ns',"abs")
      val rep_name = (ns',"rep")
      val _ = log_name abs_name
      val _ = log_name rep_name
      val _ = log_list log_type_var tyvars
      val _ = log_thm (EXISTENCE_RULE th)
      val _ = log_command "defineTypeOp"
      val (phi,_) = dest_comb (snd(dest_exists(concl th)))
      val (rty,_) = dom_rng(type_of phi)
      val a       = mk_var("a",aty)
      val r       = mk_var("r",rty)
      val absty   = rty --> aty
      val repty   = aty --> rty
      val ots     = OpenTheoryMap.otname_to_string
      val abstc   = {Thy="Logging",Name=ots abs_name}
      val reptc   = {Thy="Logging",Name=ots rep_name}
      val abs     = prim_new_const abstc absty
      val rep     = prim_new_const reptc repty
      val ra      = mk_thm([],mk_ra(phi,r,rep,abs))
      val _       = save_dict (OThm ra)
      val _       = log_command "pop"
      val ar      = mk_thm([],mk_ar(abs,rep,a))
      val _       = save_dict (OThm ar)
      val _       = log_command "pop"
      val _       = save_dict (OConst reptc)
      val _       = log_command "pop"
      val _       = save_dict (OConst abstc)
      val _       = log_command "pop"
      val _       = save_dict (OTypeOp name)
      val _       = log_command "pop"
      val pth     = INST_TY_TERM ([mk_var("phi",rty-->bool)|->phi,
                                   mk_var("abs",rty-->aty)|->abs,
                                   mk_var("rep",aty-->rty)|->rep],
                                  [alpha|->rty,beta|->aty]) Def_tyop_pth
      val _       = log_thm (proveHyp ra (proveHyp ar pth))
      in () end
    val _ = if !verbosity >= 4 then HOL_MESG("Finish proof for "^(Susp.force ths)) else ()
    (*
    val _ = log_comment(pt^")")
    *)
    val _ = save_dict ob
    (*
    val _ = log_pair (log_list log_term, log_term) (dest_thm th)
    val _ = log_command "pop"
    *)
    in () end
  end
in (log_term, log_thm, reset_dict,
    set_const_name_handler, reset_const_name_handler,
    set_tyop_name_handler, reset_tyop_name_handler)
end

val definitions = ref []

fun log_definitions () =
  (List.app log_thm (List.rev (!definitions));
   definitions := [])

fun export_thm th = let
  open Thm Feedback Parse
  val _ = case !log_state of
      Not_logging => ()
    | Active_logging _ => let
      val _ = log_definitions ()
      val v = !verbosity >= 1
      val s = Susp.delay (fn () => Lib.ppstring pp_thm th)
      val _ = if v then HOL_MESG("Start logging\n"^(Susp.force s)^"\n") else ()
      val _ = log_thm th
      val _ = log_list log_term (hyp th)
      val _ = log_term (concl th)
      val _ = log_command "thm"
      val _ = if v then HOL_MESG("Finish logging\n"^(Susp.force s)^"\n") else ()
      in () end
    val _ = delete_proof th
in th end

fun mk_path name = OS.Path.concat(OS.FileSys.getDir(),OS.Path.joinBaseExt{base=name,ext=SOME"art"})

fun mkpair f x = (f,x)

datatype OTDirective = DeleteConstant | DeleteType | SkipThm | DeleteProof

fun log_some_thms axdefs th =
  (if (case Thm.proof th of
         Thm.Def_const_prf (thyrec, _) =>
           Lib.mem (DeleteConstant, #Name thyrec) axdefs
       | Thm.Def_const_list_prf (_,stys,_) =>
           List.exists (Lib.C Lib.mem axdefs o mkpair DeleteConstant o #1)
                       stys
       | Thm.Def_spec_prf (cs,_) =>
           List.exists (Lib.C Lib.mem axdefs o mkpair DeleteConstant o #1 o
                        Term.dest_const) cs
       | Thm.Def_tyop_prf (thyrec,_,_,_) =>
           Lib.mem (DeleteType, #Tyop thyrec) axdefs
       | _ => false)
   then Thm.delete_proof th
   else ();
   definitions := th::(!definitions))

fun raw_start_logging axdefs out =
  case !log_state of
    Not_logging => let
      val _ = Thm.set_definition_callback (log_some_thms axdefs)
      val _ = log_state := Active_logging out
      val _ = log_num 6
      val _ = log_command "version"
    in () end
  | Active_logging _ => ()

fun read_otdfile fname =
  let
    val instrm = TextIO.openIn fname
    val _ = Feedback.HOL_MESG("Reading "^fname)
    fun recurse acc =
      case Option.map (Substring.splitl (not o Char.isSpace) o Substring.full) (TextIO.inputLine instrm) of
          NONE => List.rev acc
        | SOME (d,nm) =>
          let
            val d = Substring.string d
            val dir = case d of
                          "deltype" => SOME DeleteType
                        | "delconst" => SOME DeleteConstant
                        | "delproof" => SOME DeleteProof
                        | "skipthm" => SOME SkipThm
                        | _ => (Feedback.HOL_WARNING "Logging" "read_otdfile"
                                                     ("Bad directive "^d);
                                NONE)
            val fixnm = Substring.string o Substring.dropl Char.isSpace o Substring.trimr 1
          in
            recurse (case dir of NONE => acc | SOME dir => (dir,fixnm nm) :: acc)
          end
  in
    recurse [] before TextIO.closeIn instrm
  end

fun start_logging nm =
  let
    val mungefilename = nm ^ ".otd"
    val axiomatic_defs = read_otdfile mungefilename handle IO.Io _ => []
  in
    case !log_state of
        Not_logging =>
        let
          val name = Theory.current_theory()
          val path = mk_path name
          val file = TextIO.openOut path
        in raw_start_logging axiomatic_defs file end
      | Active_logging _ => ()
  end

fun stop_logging() =
  case !log_state of
    Active_logging h => let
      val _ = log_clear ()
      val _ = TextIO.closeOut h
      val _ = Thm.clear_definition_callback()
    in log_state := Not_logging end
  | Not_logging => ()

end
