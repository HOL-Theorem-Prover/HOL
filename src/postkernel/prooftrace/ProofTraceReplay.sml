val _ = use "/home/mario/HOL4-stable/src/postkernel/prooftrace/ProofTraceParser.sig";
val _ = use "/home/mario/HOL4-stable/src/postkernel/prooftrace/ProofTraceParser.sml";
val _ = use "/home/mario/HOL4-stable/src/postkernel/prooftrace/ProofTraceConverter.sig";
val _ = use "/home/mario/HOL4-stable/src/postkernel/prooftrace/ProofTraceConverter.sml";
open ProofTraceParser
open Redblackmap

fun apply f g = f g

fun mk_rules {string,term,thm,hol_type,list,pair,opt,four} =
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
      ("compute", [pair (four (hol_type, list (pair (string, thm)),
                               hol_type, list (pair (string, term))),
                         list thm), term]),
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

fun do_all_thms heap (f: unit parser) = {
  hol_type = K (),
  list = fn f => appList heap f o castPtr,
  opt = fn f => ignore o option heap f o castPtr,
  pair = fn fg => ignore o tuple2 heap fg o castPtr,
  string = K (),
  term = K (),
  thm = f,
  four = fn fghi => ignore o tuple4 heap fghi o castPtr
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
    val _ = map2 apply args_rs args_ptrs
  in () end
in (tm_defs, ty_defs, add_def) end

val trDB : (string, (string, thm) dict) dict ref
  = ref (mkDict String.compare)

val replay_prefix = "tr_"; (* can be empty if we start from min *)

datatype hol_obj =
   Ty of hol_type
 | CTm of term
 | OTm of int * int * term
 | Th of thm
 | Str of string
 | Pair of hol_obj * hol_obj
 | List of hol_obj list
 | Opt of hol_obj option
 | Four of hol_obj * (hol_obj * (hol_obj * hol_obj))
 | Unknown
fun destTy (Ty ty) = ty | destTy _ = raise Fail "destTy"
(* fun destTm (Tm tm) = tm | destTm _ = raise Fail "destTm" *)
fun destTh (Th th) = th | destTh _ = raise Fail "destTh"
fun destStr (Str x) = x | destStr _ = raise Fail "destStr"
fun destPair (Pair x) = x | destPair _ = raise Fail "destPair"
fun destList (List x) = x | destList _ = raise Fail "destList"
fun destOpt (Opt x) = x | destOpt _ = raise Fail "destOpt"
fun destFour (Four x) = x | destFour _ = raise Fail "destFour"

(*
val thyname = "bool";
*)

fun replay thyname = let

  val filename = thyname ^ "Theory.tr.gz";
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
  fun mk_thyname rawThy = if rawThy = "min" then rawThy
                          else replay_thyname ^ rawThy
  val replayed_heap = Array.array(heapSize heap, Unknown);

  fun cache (mk_obj,dest_obj) mk_x x_ptr = let
    val key = ptr x_ptr
  in case Array.sub(replayed_heap, key) of Unknown =>
       let val obj = mk_obj(mk_x x_ptr)
       in (Array.update(replayed_heap, key, obj); dest_obj obj) end
     | obj => dest_obj obj
  end

  val replay_str = cache (Str,destStr) (str heap)
  fun replay_pair f = cache (Pair,destPair) (tuple2 heap f)
  fun replay_list f = cache (List,destList) (list heap f)
  fun replay_opt f = cache (Opt,destOpt) (option heap f)
  fun replay_four f = cache (Four,destFour) (tuple4 heap f)

  val snum = ref 0

  fun check_def map rawThy nm =
    if rawThy = thyname then case peek (map, nm)
    of SOME thp => ignore (replay_thm thp)
     | _ => () else ()

  and replay_type ty_ptr =
  cache (Ty,destTy) (fn ty_ptr =>
    case shType heap ty_ptr of
      Tyv s => mk_vartype s
    | Tyapp (idp, args_ptr) => let
        val (rawThy,Tyop) = ident heap idp
        val Args = list heap replay_type args_ptr
        val () = check_def ty_defs rawThy Tyop
        in mk_thy_type {Thy=mk_thyname rawThy, Tyop=Tyop, Args=Args} end
  ) ty_ptr

  and replay_term_core (p as (sid, s)) tm_ptr = let
    val key = ptr tm_ptr
    fun build () = let
      val (depth, tm) = case shTerm heap tm_ptr of
        Abs (t1,t2) => let
        val (_, x) = replay_term_core p t1
        val n = !snum; val _ = snum := n + 1
        val (d, t2) = replay_term_core (n, Subst.cons (s, x)) t2
        in (Int.max (0, d - 1), mk_abs (x, t2)) end
      | Comb (t1,t2) => let
        val (d1, t1) = replay_term_core p t1
        val (d2, t2) = replay_term_core p t2
        in (Int.max (d1, d2), mk_comb (t1, t2)) end
      | Fv (s, ty) => (0, mk_var (s, replay_type ty))
      | Const (idp, typ) => let
        val (rawThy,Name) = ident heap idp
        val () = check_def tm_defs rawThy Name
        val ty = replay_type typ
        in (0, mk_thy_const {Thy=mk_thyname rawThy, Name=Name, Ty=ty}) end
      | Clos _ => raise Fail "replay_term Clos"
      | Bv n => case Subst.exp_rel (s, n) of
          (_, SOME t) => (n + 1, t)
        | (_, NONE) => raise Fail "open term"
      val value = if depth = 0 then CTm tm else OTm (depth, sid, tm)
      in Array.update(replayed_heap, key, value); (depth, tm) end
    in
      case Array.sub(replayed_heap, key) of
        Unknown => build ()
      | CTm tm => (0, tm)
      | OTm (d, sid', tm) => if sid = sid' then (d, tm) else build ()
      | _ => raise Fail "destTm"
    end

  and replay_term tm_ptr = #2 (replay_term_core (0, Subst.id) tm_ptr)

  and replay_thm (thm_ptr: thm ptr) =
  cache (Th,destTh) (fn thm_ptr => let
    val (_, _, proof_ptr) = shThm heap thm_ptr
    val (i, args_ptrs) = shVariant heap proof_ptr
    val (name, args_rs) = Array.sub(rules(), i)
    val args_objs = map2 apply args_rs args_ptrs
  in
    raise Fail ("replay_thm " ^ name)
  end) thm_ptr

  and rules() = mk_rules {
    string = Str o replay_str o castPtr,
    term = CTm o replay_term o castPtr,
    thm = Th o replay_thm o castPtr,
    hol_type = Ty o replay_type o castPtr,
    list = fn f => List o replay_list f o castPtr,
    pair = fn f => Pair o replay_pair f o castPtr,
    opt = fn f => Opt o replay_opt f o castPtr,
    four = fn f => Four o replay_four f o castPtr
  }

  fun export p = let
    val (nm, (th, _)) = tuple3 heap (str heap, replay_thm, I) p
  in (nm, th) end

  val thyDB = fromList String.compare (list heap export all_thms)

  val () = trDB := update(!trDB, replay_thyname, fn NONE => thyDB
                                      | _ => raise Fail "dup thy")
in () end
