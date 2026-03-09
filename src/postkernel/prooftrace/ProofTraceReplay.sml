(*
val _ = PolyML.use (OS.Path.concat(Globals.HOLDIR, "tools-poly/holinteractive.ML"));
*)
open Lib HolKernel Redblackmap ProofTraceParser

fun apply f g = f g
fun mk_eq(l,r) = list_mk_icomb equality [l,r]
(* TODO: remove after merging HolKernel that has this *)
datatype thm_id = SavedAnon of int | SavedName of string

fun mk_rules {string,term,thm,hol_type,list,pair,opt,four,
              new_term,new_type,thm_id} =
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
      ("Def_spec", [list new_term, thm]),
      ("Def_tyop", [pair (string, string), list hol_type, thm, new_type]),
      ("Disk", [string, thm_id]),
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
  hol_type = K (), new_type = K (),
  list = fn f => appList heap f o castPtr,
  opt = fn f => ignore o option heap f o castPtr,
  pair = fn fg => ignore o tuple2 heap fg o castPtr,
  string = K (), thm_id = K (),
  term = K (), new_term = K (),
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

val trDB : (string, (string, thm) dict * thm list) dict ref
  = ref (mkDict String.compare)

datatype hol_obj =
   Ty of hol_type
 | Tm of term
 | Th of thm
 | Id of thm_id
 | Str of string
 | Pair of hol_obj * hol_obj
 | List of hol_obj list
 | Opt of hol_obj option
 | Four of hol_obj * (hol_obj * (hol_obj * hol_obj))
 | Unknown
fun destTy (Ty ty) = ty | destTy _ = raise Fail "destTy"
fun destTm (Tm tm) = tm | destTm _ = raise Fail "destTm"
fun destTh (Th th) = th | destTh _ = raise Fail "destTh"
fun destId (Id id) = id | destId _ = raise Fail "destId"
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
  val {all_thms, anon_thms, ...} = shRoot heap root_ptr;
  (*
    val all_ptrs = list heap (tuple3 heap (I, I, I)) all_thms
    val thm_ptrs = List.map (fn (_,(p,_)) => p) all_ptrs
  *)
  val (tm_defs, ty_defs) =
    let val (tms,tys,ad) = mk_add_def thyname heap
        val () = appList heap (tuple3 heap (I, ad, I)) all_thms
        val () = appList heap ad anon_thms
    in (!tms, !tys) end

  val replayed_heap = Array.array(heapSize heap, Unknown);

  val next_axiom_name = let
    val names = ref ["BOOL_CASES_AX", "SELECT_AX", "ETA_AX", "INFINITY_AX"]
  in 
    fn () => case !names of x::xs => x before names := xs
             | _ => raise Fail "next_axiom_name"
  end

  fun cache (mk_obj,dest_obj) mk_x x_ptr = let
    val key = ptr x_ptr
  in case Array.sub(replayed_heap, key) of Unknown =>
       let val obj = mk_obj(mk_x x_ptr)
       in (Array.update(replayed_heap, key, obj); dest_obj obj) end
     | obj => dest_obj obj
  end

  val debug : thm list ref = ref []
  val dbg_print = print

  fun get_const_id tm_ptr =
    case shTerm heap tm_ptr of Const (idp,_) => ident heap idp
    | _ => raise Fail "get_const_id"

  fun get_thm_id (id_ptr: thm_id ptr) = let
    val (i,ps) = shVariant heap id_ptr
    val p = el 1 ps
  in if i = 0 then SavedAnon (int (castPtr p))
     else SavedName (str heap (castPtr p)) end

  val replay_str = cache (Str,destStr) (str heap)
  fun replay_pair f = cache (Pair,destPair) (tuple2 heap f)
  fun replay_list f = cache (List,destList) (list heap f)
  fun replay_opt f = cache (Opt,destOpt) (option heap f)
  fun replay_four f = cache (Four,destFour) (tuple4 heap f)

  fun check_def map Thy nm =
    if Thy = thyname then case peek (map, nm)
    of SOME thp => ignore (replay_thm thp)
     | _ => () else ()

  and replay_type ty_ptr =
  cache (Ty,destTy) (fn ty_ptr =>
    case shType heap ty_ptr of
      Tyv s => mk_vartype s
    | Tyapp (idp, args_ptr) => let
        val (Thy,Tyop) = ident heap idp
        val Args = list heap replay_type args_ptr
        val () = check_def ty_defs Thy Tyop
        in mk_thy_type {Thy=Thy, Tyop=Tyop, Args=Args} end
  ) ty_ptr

  and replay_term_core env tm_ptr =
    case shTerm heap tm_ptr of
      Abs (t1,t2) => let
        val x = replay_term_core env t1
        val g = genvar(type_of x)
        val b = replay_term_core (g::env) t2
      in mk_abs(g,b) end
    | Comb (t1,t2) => let
        val f = replay_term_core env t1
        val x = replay_term_core env t2
      in mk_comb(f,x) end
    | Const (idp,typ) => let
        val (Thy,Name) = ident heap idp
        val () = dbg_print ("check_def "^Name^",")
        val () = check_def tm_defs Thy Name
        val ty = replay_type typ
      in mk_thy_const {Thy=Thy, Name=Name, Ty=ty}
         handle e as (HOL_ERR _) =>
           if Thy = thyname then
             prim_new_const {Thy=Thy, Name=Name} ty
           else raise e
      end
    | Fv (s,typ) => mk_var(s, replay_type typ)
    | Bv n => List.nth(env, n)
    | _ => raise Fail "replay_term_core Clos"

  and replay_term tm_ptr =
  cache (Tm,destTm) (replay_term_core []) tm_ptr

  and replay_thm (thm_ptr: thm ptr) =
  cache (Th,destTh) (fn thm_ptr => let
    val (hyp_ptr, concl_ptr, proof_ptr) = shThm heap thm_ptr
    val (i, args_ptrs) = shVariant heap proof_ptr
    val (name, args_rs) = Array.sub(rules(), i)
    val () = dbg_print (name^",")
    val aos = map2 apply args_rs args_ptrs
  in
    if name = "ABS" then
      ABS (destTm (el 1 aos)) (destTh (el 2 aos))
    else if name = "ALPHA" then
      ALPHA (destTm (el 1 aos)) (destTm (el 2 aos))
    else if name = "AP_TERM" then
      AP_TERM (destTm (el 1 aos)) (destTh (el 2 aos))
    else if name = "AP_THM" then
      AP_THM (destTh (el 1 aos)) (destTm (el 2 aos))
    else if name = "ASSUME" then
      ASSUME (destTm (el 1 aos))
    else if name = "Axiom" then let
      val h = ref (HOLset.empty Term.compare)
      fun add t = h := HOLset.add(!h, t)
      val () = appSet heap (add o replay_term) hyp_ptr
      val h = !h 
      val c = replay_term concl_ptr
      (* TODO: search for previously exported theoerms *)
      val () = if HOLset.isEmpty h then () else raise Fail "Axiom hyps"
    in new_axiom(next_axiom_name(), c) end
    else if name = "BETA_CONV" then
      BETA_CONV (destTm (el 1 aos))
    else if name = "Beta" then
      raise Fail ("replay_thm: Beta not yet implemented")
    else if name = "CCONTR" then
      CCONTR (destTm (el 1 aos)) (destTh (el 2 aos))
    else if name = "CHOOSE" then
      CHOOSE (destTm (el 1 aos), destTh (el 2 aos)) (destTh (el 3 aos))
    else if name = "CONJUNCT1" then
      CONJUNCT1 (destTh (el 1 aos))
    else if name = "CONJUNCT2" then
      CONJUNCT2 (destTh (el 1 aos))
    else if name = "CONJ" then
      CONJ (destTh (el 1 aos)) (destTh (el 2 aos))
    else if name = "DISCH" then
      DISCH (destTm (el 1 aos)) (destTh (el 2 aos))
    else if name = "DISJ1" then
      DISJ1 (destTh (el 1 aos)) (destTm (el 2 aos))
    else if name = "DISJ2" then
      DISJ2 (destTm (el 1 aos)) (destTh (el 2 aos))
    else if name = "DISJ_CASES" then
      DISJ_CASES (destTh (el 1 aos)) (destTh (el 2 aos)) (destTh (el 3 aos))
    else if name = "Def_const_list" then
      raise Fail ("replay_thm: Def_const_list not yet implemented")
    else if name = "Def_const" then let
      val (Thy,Name) = (destStr ## destStr) (destPair (el 1 aos))
      val rhs = destTm (el 2 aos)
      val th = ASSUME (mk_eq(mk_var(Name, type_of rhs), rhs))
      in #2 (gen_prim_specification Thy th) end
    else if name = "Def_spec" then let
      val ids = List.map ((destStr ## destStr) o destPair)
                         (destList (el 1 aos))
      val () = if List.all (equal thyname) (List.map #1 ids) then ()
               else raise Fail "Def_spec thy"
      val cnames = List.map #2 ids
      val th = destTh (el 2 aos)
    in prim_specification thyname cnames th end
    else if name = "Def_tyop" then let
      val (Thy,Tyop) = (destStr ## destStr) (destPair (el 1 aos))
      val th = destTh (el 3 aos)
      val () = if thyname = "bool"
               then check_def tm_defs thyname "TYPE_DEFINITION"
               else ()
    in prim_type_definition ({Thy=Thy, Tyop=Tyop},th) end
    else if name = "Disk" then
      case destStr (el 1 aos) of thy => (
      case peek(!trDB, thy) of
        NONE => raise Fail ("Disk thy "^thy)
      | SOME (named,anons) => (
        case (destId (el 2 aos)) of
          SavedAnon i => List.nth(anons, i)
        | SavedName s => (
            case peek(named, s) of
              NONE => raise Fail ("Disk thy "^thy^"$"^s)
            | SOME th => th)))
    else if name = "EQ_IMP_RULE1" then
      #1 (EQ_IMP_RULE (destTh (el 1 aos)))
    else if name = "EQ_IMP_RULE2" then
      #2 (EQ_IMP_RULE (destTh (el 1 aos)))
    else if name = "EQ_MP" then
      EQ_MP (destTh (el 1 aos)) (destTh (el 2 aos))
    else if name = "EXISTS" then
      EXISTS (destTm (el 1 aos), destTm (el 2 aos)) (destTh (el 3 aos))
    else if name = "GENL" then
      raise Fail ("replay_thm: GENL not yet implemented")
    else if name = "GEN_ABS" then
      raise Fail ("replay_thm: GEN_ABS not yet implemented")
    else if name = "GEN" then
      GEN (destTm (el 1 aos)) (destTh (el 2 aos))
    else if name = "INST_TYPE" then let
      val s = List.map (op |-> o (destTy ## destTy) o destPair)
                       (destList (el 1 aos))
      val th = destTh (el 2 aos)
    in INST_TYPE s th end
    else if name = "INST" then let
      val s = List.map (op |-> o (destTm ## destTm) o destPair)
                       (destList (el 1 aos))
      val th = destTh (el 2 aos)
    in INST s th end
    else if name = "MK_COMB" then
      MK_COMB (destTh (el 1 aos), destTh (el 2 aos))
    else if name = "MP" then
      MP (destTh (el 1 aos)) (destTh (el 2 aos))
    else if name = "Mk_abs" then
      raise Fail ("replay_thm: Mk_abs not yet implemented")
    else if name = "Mk_comb" then
      raise Fail ("replay_thm: Mk_comb not yet implemented")
    else if name = "NOT_ELIM" then
      NOT_ELIM (destTh (el 1 aos))
    else if name = "NOT_INTRO" then
      NOT_INTRO (destTh (el 1 aos))
    else if name = "REFL" then
      REFL (destTm (el 1 aos))
    else if name = "SPEC" then
      SPEC (destTm (el 1 aos)) (destTh (el 2 aos))
    else if name = "SUBST" then let
      val s = List.map (op |-> o (destTm ## destTh) o destPair)
                       (destList (el 1 aos))
      val t = destTm (el 2 aos)
      val th = destTh (el 3 aos)
    in SUBST s t th end
    else if name = "SYM" then
      SYM (destTh (el 1 aos))
    else if name = "Specialize" then
      raise Fail ("replay_thm: Specialize not yet implemented")
    else if name = "TRANS" then
      TRANS (destTh (el 1 aos)) (destTh (el 2 aos))
      handle e as (HOL_ERR _) => (debug := [
        destTh (el 1 aos), destTh (el 2 aos) ]; raise e)
    else if name = "compute" then
      raise Fail ("replay_thm: compute not yet implemented")
    else if name = "deductAntisym" then
      raise Fail ("replay_thm: deductAntisym not yet implemented")
    else if name = "deleted" then
      raise Fail ("replay_thm: deleted not yet implemented")
    else raise Fail ("replay_thm " ^ name)
  end) thm_ptr

  and rules() = mk_rules {
    string = Str o replay_str o castPtr,
    term = Tm o replay_term o castPtr,
    thm = Th o replay_thm o castPtr,
    thm_id = Id o get_thm_id o castPtr,
    hol_type = Ty o replay_type o castPtr,
    new_type = K Unknown,
    new_term = Pair o (Str ## Str) o get_const_id o castPtr,
    list = fn f => List o replay_list f o castPtr,
    pair = fn f => Pair o replay_pair f o castPtr,
    opt = fn f => Opt o replay_opt f o castPtr,
    four = fn f => Four o replay_four f o castPtr
  }

  fun export p = let
    val (nm, (thp, _)) = tuple3 heap (str heap, I, I) p
    val () = dbg_print ("Replaying "^nm^"...")
    val th = replay_thm thp
    val () = dbg_print " done\n"
  in (nm, th) end

  val named = fromList String.compare (list heap export all_thms)
  val anons = list heap replay_thm anon_thms

  val () = trDB := update(!trDB, thyname,
             fn NONE => (named, anons)
              | _    => raise Fail "dup thy")
in () end

(*
val () = replay "bool"
val () = replay "marker"
val rm = find(!trDB,"bool")

fun print_ty ty =
  if is_vartype ty then dest_vartype ty
  else let
    val (opn, args) = dest_type ty
    val args = List.map print_ty args
  in if List.null args then opn
     else String.concat["(", String.concatWith "," args, ") ", opn]
  end

fun print_tm tm =
  if is_var tm then let
    val (x,ty) = dest_var tm
  in String.concat[x,":",print_ty ty] end
  else if is_const tm then let
    val (x,ty) = dest_const tm
  in x end
  else if is_abs tm then let
    val (x,b) = dest_abs tm
  in String.concat["(\\", print_tm x, ". ", print_tm b, ")"] end
  else let val (f,x) = dest_comb tm in
    String.concat["(", print_tm f, " ", print_tm x, ")"]
  end

print_tm(concl(find(rm,"INFINITY_AX")))
*)
