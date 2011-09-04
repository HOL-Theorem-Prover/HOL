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

  (* Attribution: ideas for reconstructing DISCH, MP, etc.
     taken from HOL Light code *)
  (* Note: Using Metis below may be untenable (it could introduce a loop).
     So it would be better to construct the proof by hand (possibly
     after looking at a trace). But the theorem is in the OpenTheory
     standard library, so maybe the best thing to do is to special-case it
     with an Axiom_prf. (Other theorems might need that treatment too.) *)
  local open metisLib Thm Conv HOLset in
    val IMP_DEF = METIS_PROVE[]``$==> = \p q. p /\ q <=> p``
    val p = ``p:bool``
    val q = ``q:bool``
    val DISCH_pth = SYM(BETA_RULE (AP_THM (AP_THM IMP_DEF p) q))
    val MP_pth = let
      val th1 = BETA_RULE (AP_THM (AP_THM IMP_DEF p) q)
      val th2 = EQ_MP th1 (ASSUME ``p ==> q``)
    in CONJUNCT2 (EQ_MP (SYM th2) (ASSUME p)) end
    fun MP_PROVE_HYP ath bth =
      if member (hypset bth, concl ath)
      then EQ_MP (DEDUCT_ANTISYM ath bth) ath
      else bth
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
      val th3 = INST [ant|->p, con|->q] MP_pth
      val th4 = MP_PROVE_HYP th1 th3
      val _ = log_thm (MP_PROVE_HYP th2 th4)
      in () end
    | SUBST_prf (map,tm,th) => let
      open Thm Term Feedback HOLset Lib
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
      val _ = log_list log_term (Thm.hyp th)
      val _ = log_term (Thm.concl th)
           in log_command "thm" end
(*  val _ = Thm.delete_proof th *)
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
