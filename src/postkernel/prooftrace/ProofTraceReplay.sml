open ProofTraceParser
open Redblackmap

fun mk_rules {string,term,thm,hol_type,list,pair,opt,compute_prep} =
   Array.fromList [
      ("ABS", [term, thm]),
      ("ALPHA", [term, term]),
      ("AP_TERM", [term, thm]),
      ("AP_THM", [thm, term]),
      ("ASSUME", [term]),
      ("Axiom", []),
      ("BETA_CONV", [term]),
      ("Beta", [thm]),
      ("CCONTR", [term, thm]),
      ("CHOOSE", [term, thm, thm]),
      ("CONJUNCT1", [thm]),
      ("CONJUNCT2", [thm]),
      ("CONJ", [thm, thm]),
      ("DISCH", [term, thm]),
      ("DISJ1", [thm, term]),
      ("DISJ2", [term, thm]),
      ("DISJ_CASES", [thm, thm, thm]),
      ("Def_const_list", [string, list (pair (string, hol_type)), thm]),
      ("Def_const", [pair (string, string), term]),
      ("Def_spec", [list term, thm]),
      ("Def_tyop", [pair (string, string), list hol_type, thm, hol_type]),
      ("EQ_IMP_RULE1", [thm]),
      ("EQ_IMP_RULE2", [thm]),
      ("EQ_MP", [thm, thm]),
      ("EXISTS", [term, term, thm]),
      ("GENL", [list term, thm]),
      ("GEN_ABS", [opt term, list term, thm]),
      ("GEN", [term, thm]),
      ("INST_TYPE", [list (pair (hol_type, hol_type)), thm]),
      ("INST", [list (pair (term, term)), thm]),
      ("MK_COMB", [thm, thm]),
      ("MP", [thm, thm]),
      ("Mk_abs", [thm, term, thm]),
      ("Mk_comb", [thm, thm, thm]),
      ("NOT_ELIM", [thm]),
      ("NOT_INTRO", [thm]),
      ("REFL", [term]),
      ("SPEC", [term, thm]),
      ("SUBST", [list (pair (term, thm)), term, thm]),
      ("SYM", [thm]),
      ("Specialize", [term, thm]),
      ("TRANS", [thm, thm]),
      ("compute", [compute_prep, term]),
      ("deductAntisym", [thm, thm]),
      ("deleted", [])
  ]

(* 
  compute_prf of (compute_args * thm list) * term
  where compute_args = {
    num_type   : hol_type,
    char_eqns  : (string * thm) list,
    cval_type  : hol_type,
    cval_terms : (string * term) list }
*)
fun do_all_thms heap f = {
  hol_type = K (),
  list = fn f => appList heap f o castPtr,
  opt = fn f => ignore o option heap f o castPtr,
  pair = fn fg => ignore o tuple2 heap fg o castPtr,
  string = K (),
  term = K (),
  thm = f,
  compute_prep = let
    val a = tuple4 heap (I, appList heap (tuple2 heap (I, f)), I, I)
  in ignore o tuple2 heap (tuple2 heap (a, appList heap f), I) o castPtr end
}

(*
  val [(_,thm_ptr)] = listItems (!tm_defs)
  val debug_ptr: thm ptr ref = ref (castPtr root_ptr)
  val thm_ptr = !debug_ptr
  ("Def_const_list", [string, list (pair (string, hol_type)), thm]),
  ("Def_const", [pair (string, string), term]),
  ("Def_spec", [list term, thm]),
  ("Def_tyop", [pair (string, string), list hol_type, thm, hol_type]),
  val thm_ptr = el 1 thm_ptrs
*)
fun mk_add_def thyname heap = let
  val tm_defs : (string, thm ptr) dict ref = ref (mkDict String.compare)
  val ty_defs : (string, thm ptr) dict ref = ref (mkDict String.compare)
  val seen = BoolArray.array(heapSize heap, false)
  fun add_def (thm_ptr: thm ptr) =
    if BoolArray.sub(seen, ptr thm_ptr) then () else let
    (*
    val () = print ("ptr thm_ptr: " ^ Int.toString(ptr thm_ptr) ^ "\n")
    val () = debug_ptr := thm_ptr
    *)
    val () = BoolArray.update(seen, ptr thm_ptr, true)
    val (_, _, proof_ptr) = shThm heap thm_ptr
    val (i, args_ptrs) = shVariant heap proof_ptr
    val rs = mk_rules (do_all_thms heap (add_def o castPtr)) 
    val (rule_name, args_rs) = Array.sub(rs, i)
    fun add_thm_ptr NONE = thm_ptr
      | add_thm_ptr _ = raise Fail "add_def dup" 
    fun check_thy defthy = 
      if defthy = thyname then () else raise Fail "add_def thy"
    fun add_const nm = tm_defs := update(!tm_defs, nm, add_thm_ptr)
    val () = if rule_name <> "Def_const_list" then () else let
      (* val () = print "Def_const_list\n" *)
      val () = check_thy $ str heap (castPtr (el 1 args_ptrs)) 
      val names = list heap (#1 o tuple2 heap (str heap, I))
                            (castPtr (el 2 args_ptrs))
    in List.app add_const names end
    val () = if rule_name <> "Def_const" then () else let
      (* val () = print "Def_const\n" *)
      val ((),nm) = tuple2 heap (check_thy o str heap, str heap)
                                (castPtr (el 1 args_ptrs))
    in add_const nm end
    fun get_const (Const (idp,_)) = ident heap idp
      | get_const _ = raise Fail "add_def spec"
    val () = if rule_name <> "Def_spec" then () else let
      (* val () = print "Def_spec\n" *)
      val shtms = list heap (shTerm heap) (castPtr (el 1 args_ptrs))
      val (defthys, nms) = unzip (List.map get_const shtms)
      val () = List.app check_thy defthys
    in List.app add_const nms end
    val () = if rule_name <> "Def_tyop" then () else let
      (* val () = print "Def_tyop\n" *)
      val ((),tyop) = tuple2 heap (check_thy o str heap, str heap)
                                  (castPtr (el 1 args_ptrs))
    in ty_defs := update(!ty_defs, tyop, add_thm_ptr)
    end
    val _ = map2 (fn f => fn g => f g) args_rs args_ptrs
  in () end
in (tm_defs, ty_defs, add_def) end

val trDB : (string, (string, thm) dict) dict ref 
  = ref (mkDict String.compare)

val replay_prefix = "tr_"; (* can be empty if we start from min *)

datatype hol_obj = Ty of hol_type | Tm of term | Th of thm | Unknown
fun destTy (Ty ty) = ty | destTy _ = raise Fail "destTy"
fun destTm (Tm tm) = tm | destTm _ = raise Fail "destTm"
fun destTh (Th th) = th | destTh _ = raise Fail "destTh"

(*
val thyname = "bool";
*)

fun replay thyname = let

  val filename =  thyname ^ "Theory.tr.gz";
  val (root_ptr, heap) = parse filename;
  val {all_thms, ...} = shRoot heap root_ptr;
  (*
    val all_ptrs = list heap (tuple3 heap (I, I, I)) all_thms
    val thm_ptrs = List.map (fn (_,(p,_)) => p) all_ptrs
  *)
  val (tm_defs, ty_defs) =
    let val (tms,tys,ad) = mk_add_def thyname heap
        val () = appList heap (tuple3 heap (I, ad, I)) all_thms
    in (!tms, !tys) end

  val replay_thyname = replay_prefix ^ thyname; 
  val replayed_heap = Array.array(heapSize heap, Unknown);

  fun cache (mk_obj,dest_obj) mk_x x_ptr = let
    val key = ptr x_ptr
  in case Array.sub(replayed_heap, key) of Unknown =>
       let val obj = mk_obj(mk_x())
       in (Array.update(replayed_heap, key, obj); dest_obj obj) end
     | obj => dest_obj obj
  end

  fun check_def map Thy nm =
    if Thy = thyname then case peek (map, nm)
    of SOME thp => ignore (replay_thm thp)
     | _ => () else ()

  and replay_type ty_ptr =
  cache (Ty,destTy) (fn () =>
    case shType heap ty_ptr of
      Tyv s => mk_vartype s
    | Tyapp (idp, args_ptr) => let
        val (Thy,Tyop) = ident heap idp
        val Args = list heap replay_type args_ptr
        val () = check_def ty_defs Thy Tyop
        in mk_thy_type {Thy=replay_prefix^Thy, Tyop=Tyop, Args=Args} end
  ) ty_ptr

  and replay_term tm_ptr =
  cache (Tm,destTm) (fn () =>
    case shTerm heap tm_ptr of
      Abs (t1,t2) => mk_abs (replay_term t1, replay_term t2)
    | Comb (t1,t2) => mk_comb (replay_term t1, replay_term t2)
    | Fv (s, ty) => mk_var (s, replay_type ty)
    | Const (idp, typ) => let
        val (Thy,Name) = ident heap idp
        val () = check_def tm_defs Thy Name
        val ty = replay_type typ 
        in mk_thy_const {Thy=replay_prefix^Thy, Name=Name, Ty=ty} end
    | _ => raise Fail "replay_term"
  ) tm_ptr

  and replay_thm (thm_ptr: thm ptr) =
  cache (Th,destTh) (fn () => raise Fail "replay_thm") thm_ptr

  fun export p = let
    val (nm, (th, _)) = tuple3 heap (str heap, replay_thm, I) p
  in (nm, th) end
  val thyDB = fromList String.compare (list heap export all_thms)
  val () = trDB := update(!trDB, replay_thyname, fn NONE => thyDB
                                      | _ => raise Fail "dup thy")
in () end
