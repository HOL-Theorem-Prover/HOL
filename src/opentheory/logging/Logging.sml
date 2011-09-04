structure Logging :> Logging =
struct

open OpenTheoryCommon
structure Map = OpenTheoryMap.Map

val ERR = Feedback.mk_HOL_ERR "Logging"

datatype log_state =
  Not_logging
| Active_logging of TextIO.outstream

val log_state = ref Not_logging

fun log_raw s =
  case !log_state of
    Active_logging h => TextIO.output (h,s^"\n")
  | Not_logging => ()

fun log_num n = log_raw (Int.toString n)

fun log_name s = log_raw ("\""^String.toString s^"\"")

fun log_command s = log_raw s

fun log_nil () = log_command "nil"

fun log_list log = let
  fun logl []     = log_nil ()
    | logl (h::t) = (log h; logl t; log_command "cons")
in logl end

fun log_pair loga logb (a,b) = let
  val _ = loga a
  val _ = logb b
  val _ = log_nil ()
  val _ = log_command "cons"
  val _ = log_command "cons"
in () end

fun log_redres loga logb {redex,residue} =
  log_pair loga logb (redex,residue)

val (log_term, log_thm, log_clear) = let
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
        val _ = Map.insert(!dict,x,k)
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

  fun log_type_var ty = log_name (Type.dest_vartype ty)

  local open OpenTheoryMap in
    fun log_tyop_name tyop =
      Map.find(tyop_to_ot_map(),tyop)
    handle Map.NotFound
    => raise ERR "log_tyop_name" ("No OpenTheory name for "^(#Thy tyop)^"$"^(#Tyop tyop))
    fun log_const_name const =
      Map.find(const_to_ot_map(),const)
    handle Map.NotFound
    => raise ERR "log_const_name" ("No OpenTheory name for "^(#Thy const)^"$"^(#Name const))
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
    in () end handle HOL_ERR _ => let
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
    val _ = log_name n
    val _ = log_type ty
    val _ = log_command "var"
    val _ = save_dict ob
    in () end
  end

  fun log_term tm = let
    val ob = OTerm tm
  in if saved ob then () else let
    open Term Feedback
    val _ = let
      val {Thy,Name,Ty} = dest_thy_const tm
      val _ = log_const {Thy=Thy,Name=Name}
      val _ = log_type Ty
      val _ = log_command "constTerm"
    in () end handle HOL_ERR _ => let
      val (t1,t2) = dest_comb tm
      val _ = log_term t1
      val _ = log_term t2
      val _ = log_command "appTerm"
    in () end handle HOL_ERR _ => let
      val (v,b) = dest_abs tm
      val _ = log_var v
      val _ = log_term b
      val _ = log_command "absTerm"
    in () end handle HOL_ERR _ => let
      val _ = log_var tm
      val _ = log_command "varTerm"
    in () end
    val _ = save_dict ob
    in () end
  end

  val log_subst =
    log_pair
      (log_list (log_redres log_type_var log_type))
      (log_list (log_redres log_var log_term))
  fun log_type_subst s = log_subst (s,[])
  fun log_term_subst s = log_subst ([],s)

  (* Attribution: ideas (and code) for reconstructing DISCH, SPEC, GEN, etc.
                  taken from HOL Light *)
  local open metisLib Thm Conv boolTheory boolSyntax Term Drule in
    (* These are in the OpenTheory standard library, so we can give them axiom proofs *)
    val IMP_DEF = mk_thm([],``$==> = \p q. p /\ q <=> p``)
    val EXISTS_DEF = mk_thm([],``$? = \P:'a->bool. !q. (!x. P x ==> q) ==> q``)
    val AND_DEF = mk_thm([],``$/\ = \p q. (\f:bool->bool->bool. f p q) = (\f. f T T)``)
    val p = ``p:bool``
    val q = ``q:bool``
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
      val th1 = MK_COMB(AP_TERM f (EQT_INTRO pth),EQT_INTRO qth)
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
    val CCONTR_pth = SPEC P (EQ_MP F_DEF (ASSUME F))
  end

  fun log_thm th = let
    open Thm val op |-> = Lib.|->
    val ob = OThm th
  in if saved ob then () else let
    val _ = case proof th of
      Axiom_prf => let
      val _ = log_list log_term (hyp th)
      val _ = log_term (concl th)
      val _ = log_command "axiom"
      in () end
    | ALPHA_prf (t1,t2) => let
      open Term Lib Type boolSyntax
      val _ = log_thm (REFL (mk_comb(inst[alpha|->type_of t1]equality,t1)))
      val _ = log_thm (REFL t2)
      val _ = log_command "appThm"
      val _ = log_thm (REFL t1)
      val _ = log_command "eqMp"
      in () end
    | ASSUME_prf tm => let
      val _ = log_term tm
      val _ = log_command "assume"
      in () end
    | REFL_prf tm => let
      val _ = log_term tm
      val _ = log_command "refl"
      in () end
    | BETA_CONV_prf tm => let
      val _ = log_term tm
      val _ = log_command "betaConv"
      in () end
    | ABS_prf (v,th) => let
      val _ = log_var v
      val _ = log_thm th
      val _ = log_command "absThm"
      in () end
    | DISCH_prf (tm,th) => let
      val th1 = CONJ (ASSUME tm) th
      val th2 = CONJUNCT1 (ASSUME (concl th1))
      val th4 = INST [tm|->p, concl th|->q] DISCH_pth
      val _ = log_thm th4
      val _ = log_thm th1
      val _ = log_thm th2
      val _ = log_command "deductAntisym"
      val _ = log_command "eqMp"
      in () end
    | MP_prf (th1,th2) => let
      open boolSyntax
      val (ant,con) = dest_imp(concl th1)
      val _ = log_thm th1
      val _ = log_thm th2
      val _ = log_thm (INST [p|->ant, q|->con] MP_pth)
      val _ = log_command "deductAntisym"
      val _ = saved (OThm th2)
      val _ = log_command "eqMp"
      val _ = log_command "deductAntisym"
      val _ = saved (OThm th1)
      val _ = log_command "eqMp"
      in () end
    | SUBST_prf (map,tm,th) => let
      open Term Feedback HOLset Lib
      fun log_rconv bvs source template = (* return |- source = template[rhs/vars] *)
        log_thm(ALPHA source template)
      handle HOL_ERR _ =>
        if is_var template
        then if member(bvs,template)
             then log_thm (REFL template)
             else log_thm (valOf(subst_assoc (equal template) map))
      else let
        val (sf,sa) = dest_comb source
        val (tf,ta) = dest_comb template
        val _ = log_rconv bvs sf tf
        val _ = log_rconv bvs sa ta
        val _ = log_command "appThm"
      in () end handle HOL_ERR _ => let
        val (sv,sb) = dest_abs source
        val (tv,tb) = dest_abs template
        val _ = log_rconv (add(bvs,tv)) sb tb
        val _ = log_var tv
        val _ = log_command "absThm"
      in () end
      val _ = log_rconv empty_varset (concl th) tm
      val _ = log_thm th
      val _ = log_command "eqMp"
      in () end
    | INST_TYPE_prf (s,th) => let
      val _ = log_type_subst s
      val _ = log_thm th
      val _ = log_command "subst"
      in () end
    | INST_prf (s,th) => let
      val _ = log_term_subst s
      val _ = log_thm th
      val _ = log_command "subst"
      in () end
    | GEN_ABS_prf (c,vlist,th) => let
      open Type Lib boolSyntax
      val dom = fst o dom_rng
      fun foo th = let val (_,_,ty) = dest_eq_ty(concl th) in dom ty end
      val f = case c of
        SOME c => let val ty = dom(dom(type_of c))
        in fn th => AP_TERM (inst[ty|->foo th] c) th end
      | NONE => I
      val _ = log_thm (List.foldr (f o uncurry ABS) th vlist)
      in () end
    | SYM_prf th => let
      val tm = concl th
      val (l,r) = boolSyntax.dest_eq tm
      val lth = REFL l
      val _ = log_term (Term.rator(Term.rator tm))
      val _ = log_command "refl"
      val _ = log_thm th
      val _ = log_command "appThm"
      val _ = log_thm lth
      val _ = log_command "appThm"
      val _ = log_thm lth
      val _ = log_command "eqMp"
      in () end
    | TRANS_prf (th1,th2) => let
      val _ = log_term (Term.rator(concl th1))
      val _ = log_command "refl"
      val _ = log_thm th2
      val _ = log_command "appThm"
      val _ = log_thm th1
      val _ = log_command "eqMp"
      in () end
    | MK_COMB_prf (th1,th2) => let
      val _ = log_thm th1
      val _ = log_thm th2
      val _ = log_command "appThm"
      in () end
    | AP_TERM_prf (tm,th) => log_thm (MK_COMB(REFL tm, th))
    | AP_THM_prf  (th,tm) => log_thm (MK_COMB(th, REFL tm))
    | EQ_MP_prf (th1,th2) => let
      val _ = log_thm th1
      val _ = log_thm th2
      val _ = log_command "eqMp"
      in () end
    | EQ_IMP_RULE1_prf th => let
      open boolSyntax
      val (t1,t2) = dest_eq(concl th)
      val _ = log_thm (DISCH t1 (EQ_MP th (ASSUME t1)))
      in () end
    | EQ_IMP_RULE2_prf th => let
      open boolSyntax
      val (t1,t2) = dest_eq(concl th)
      val _ = log_thm (DISCH t2 (EQ_MP (SYM th) (ASSUME t2)))
      in () end
    | SPEC_prf (tm,th) => let
      open Term Type Drule Lib
      val abs = rand(concl th)
      val (v,_) = dest_abs abs
      val vty = type_of v
      val pth = INST_TY_TERM ([mk_var("P",vty-->bool)|->abs,mk_var("x",vty)|->tm],[alpha|->vty]) SPEC_pth
      val _ = log_thm (CONV_RULE BETA_CONV (MP pth th))
      in () end
    | GEN_prf (v,th) => let
      open Term Type Drule Lib
      val vty = type_of v
      val pth = INST_TY_TERM ([mk_var("P",vty-->bool)|->mk_abs(x,concl th)],[alpha|->vty]) GEN_pth
      val _ = log_thm (PROVE_HYP (ABS x (EQT_INTRO th)) pth)
      in () end
    | EXISTS_prf (fm,tm,th) => let
      open Term Drule Lib
      val ty = type_of tm
      val (qf,abs) = dest_comb fm
      val bth = BETA_CONV(mk_comb(abs,tm))
      val cth = INST_TY_TERM ([mk_var("P",ty)|->abs,mk_var("x",ty)|->tm],[alpha|->ty]) EXISTS_pth
      val _ = log_thm (PROVE_HYP (EQ_MP (SYM bth) th) cth)
      in () end
    | CHOOSE_prf (v,th1,th2) => let
      open Term Drule Lib
      val vty = type_of v
      val abs = rand(concl th1)
      val (bv,bod) = dest_abs abs
      val cmb = mk_comb(abs,v)
      val pat = subst [bv|->v] bod
      val th3 = CONV_RULE BETA_CONV (ASSUME cmb)
      val th4 = GEN v (DISCH cmb (MP (DISCH pat th2) th3))
      val th5 = INST_TY_TERM ([P|->abs,Q|->concl th2],[alpha|->vty]) CHOOSE_pth
      val _ = log_thm (MP (MP th5 th4) th1)
      in () end
    | CONJ_prf (th1,th2) => let
      open Drule Lib
      val th = INST [p|->concl th1,q|->concl th2] CONJ_pth
      val _ = log_thm (PROVE_HYP th2 (PROVE_HYP th1 th))
      in () end
    | CONJUNCT1_prf th => let
      open Term boolSyntax Lib
      val (l,r) = dest_conj(concl th)
      val _ = log_thm (PROVE_HYP th (INST [P|->l,Q|->r] CONJUNCT1_pth))
      in () end
    | CONJUNCT2_prf th => let
      open Term boolSyntax Lib
      val (l,r) = dest_conj(concl th)
      val _ = log_thm (PROVE_HYP th (INST [P|->l,Q|->r] CONJUNCT2_pth))
      in () end
    | DISJ1_prf (th,tm) => let
      open Drule Lib
      val _ = log_thm (PROVE_HYP th (INST [P|->concl th,Q|->tm] DISJ1_pth))
      in () end
    | DISJ2_prf (tm,th) => let
      open Drule Lib
      val _ = log_thm (PROVE_HYP th (INST [P|->concl th,Q|->tm] DISJ2_pth))
      in () end
    | DISJ_CASES_prf (th0,th1,th2) => let
      open boolSyntax
      val c1 = concl th1
      val c2 = concl th2
      val (l,r) = dest_disj (concl th0)
      val th = INST [P|->l,Q|->r,R|->c1] DISJ_CASES_pth
      val _ = log_thm (PROVE_HYP (DISCH r th2) (PROVE_HYP (DISCH l th1) (PROVE_HYP th0 th)))
      in () end
    | NOT_INTRO_prf th => let
      open Term Lib
      val _ = log_thm (EQ_MP (INST [P|->rand(rator(concl th))] NOT_INTRO_pth) th)
      in () end
    | NOT_ELIM_prf th => let
      open Term Lib
      val _ = log_thm (EQ_MP (INST [P|->rand(concl th)] NOT_ELIM_pth) th)
      in () end
    | CCONTR_prf (tm,th) => let
      open Lib
      val _ = log_thm (PROVE_HYP th (INST [P|->tm] CCONTR_pth))
      in () end
    | Beta_prf th => log_thm (Drule.RIGHT_BETA th)
    | Mk_comb_prf (th,th1,th2) => log_thm (TRANS th (MK_COMB(th1,th2)))
    | Mk_abs_prf (th,bv,th1) => log_thm (TRANS th (ABS bv th1))
    | Specialize_prf (t,th) => log_thm (SPEC t th)
    | TODO_prf =>
      raise ERR "log_thm" "TODO_prf not implemented"
    val _ = save_dict ob
    in () end
  end

in (log_term, log_thm, reset_dict) end

fun export_thm th = let
  val _ = case !log_state of
      Not_logging => ()
    | Active_logging _ => let
      val _ = log_thm th
      val _ = log_list log_term (hyp th)
      val _ = log_term (concl th)
           in log_command "thm" end
(*  val _ = delete_proof th *)
in () end

local val op ^ = OS.Path.concat in
  val opentheory_dir = Globals.HOLDIR^"src"^"opentheory"
end

val mk_path = let
  exception exists
  fun mk_path name = let
    val path = OS.Path.concat(opentheory_dir,OS.Path.joinBaseExt{base=name,ext=SOME"4rt"})
  in if OS.FileSys.access(path,[]) then raise exists else path end
in fn name => let
     fun try n = mk_path (name^(Int.toString n)) handle exists => try (n+1)
   in mk_path name handle exists => try 0 end
end

fun start_logging() =
  case !log_state of
    Not_logging => let
      val name = Theory.current_theory()
      val path = mk_path name
      val file = TextIO.openOut path
    in log_state := Active_logging file end
  | Active_logging _ => ()

fun stop_logging() =
  case !log_state of
    Active_logging h => let
      val _ = log_clear ()
      val _ = TextIO.closeOut h
    in log_state := Not_logging end
  | Not_logging => ()

end
