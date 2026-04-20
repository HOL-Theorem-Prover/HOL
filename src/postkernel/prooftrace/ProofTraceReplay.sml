structure ProofTraceReplay :> ProofTraceReplay = struct

(*
(* interactive use in hol --min *)
val _ = PolyML.use (OS.Path.concat(Globals.HOLDIR, "tools-poly/holinteractive.ML"));
qload "ProofTraceParser";
qload "PIntMap";
*)

open Feedback Lib Type Term Thm Redblackmap ProofTraceParser

infix |->

fun mk_eq(l,r) = list_mk_comb(inst[alpha |-> type_of l]equality, [l,r])

val trDB : (string, (string, thm) dict * thm list) dict ref
  = ref (mkDict String.compare)

datatype hol_obj = Ty of hol_type | Tm of term | Th of thm | Unknown
fun destTy (Ty ty) = ty | destTy _ = raise Fail "destTy"
fun destTm (Tm tm) = tm | destTm _ = raise Fail "destTm"
fun destTh (Th th) = th | destTh _ = raise Fail "destTh"

val (next_axiom_name, add_axiom_name) = let
  val names = ref ["BOOL_CASES_AX", "SELECT_AX", "ETA_AX", "INFINITY_AX"]
  fun next () = case !names of x::xs => x before names := xs
                | _ => raise Fail "next_axiom_name"
  fun add name = names := (!names)@[name]
in
  (next, add)
end
val skip_standard_axiom = next_axiom_name

(*
val thyname = "bool";
*)
val print_statistics = ref false
val debug = ref false
val quiet = ref false
fun dbg_print s = if !debug then print s else ()
fun msg_print s = if !quiet then () else print s

fun register_bool_def "bool" "T" = register_T
  | register_bool_def "bool" "!" = register_forall
  | register_bool_def "bool" "?" = register_exists
  | register_bool_def "bool" "F" = register_F
  | register_bool_def "bool" "~" = register_neg
  | register_bool_def "bool" "/\\" = register_conj
  | register_bool_def "bool" "\\/" = register_disj
  | register_bool_def "bool" "TYPE_DEFINITION" = register_type_definition
  | register_bool_def _ _ = K ()

exception NeedsAncestor of string

fun thyname_from_path path =
  let
    val {file, ...} = OS.Path.splitDirFile path
  in
    if String.isSuffix "Theory.tr.gz" file then
      String.extract(file, 0,
        SOME(String.size file - String.size "Theory.tr.gz"))
    else if String.isSuffix "Theory.tr" file then
      String.extract(file, 0,
        SOME(String.size file - String.size "Theory.tr"))
    else raise Fail ("ProofTraceReplay.replay: unexpected filename: " ^ file)
  end

fun replay path =
  let val thyname = thyname_from_path path in
  if inDomain(!trDB, thyname)
  then msg_print("skip ")
  else
let
  val (root_ptr, heap) = parse path;
  val {all_thms, anon_thms, constants, types, ...} = shRoot heap root_ptr;

  val register_def = if thyname = "bool" then register_bool_def
                     else K (K (K ()))

  (* Pre-pass: closedness, refcounts, def collection *)
  val refcounts = Word8Array.array(heapSize heap, 0w0 : Word8.word)
  val pinned = BoolArray.array(heapSize heap, false)
  fun incr p = if isPtr p then let val k = ptr p
    val c = Word8Array.sub(refcounts, k)
  in if c < 0wxFF then Word8Array.update(refcounts, k, c + 0w1) else ()
  end else ()
  fun on_def_thm thm_ptr = BoolArray.update(pinned, ptr thm_ptr, true)

  val {tm_defs, ty_defs, is_closed, get_const_id, get_type_id} =
    ProofTraceWalk.walk
      {heap = heap, thyname = thyname,
       named_thms = all_thms, anon_thms = anon_thms,
       incr = incr, on_def_thm = on_def_thm}

  val replayed_heap = Array.array(heapSize heap, Unknown);

  val cached_compute_ptr : compute_args ptr ref = ref (castPtr root_ptr)
  val cached_compute : (thm list -> term -> thm) ref
    = ref (fn _ => raise Bind)

  fun cache (mk_obj, dest_obj) mk_x p =
  if isPtr p then let
    val key = ptr p
    fun maybe_evict () =
      if BoolArray.sub(pinned, key) then () else let
        val rc = Word8Array.sub(refcounts, key)
      in if rc = 0wxFF then () (* saturated, never evict *)
         else if rc <= 0w1
         then (Word8Array.update(refcounts, key, 0w0);
               Array.update(replayed_heap, key, Unknown))
         else Word8Array.update(refcounts, key, rc - 0w1)
      end
  in case Array.sub(replayed_heap, key) of
       Unknown => let
         val x = mk_x p
         val () = Array.update(replayed_heap, key, mk_obj x)
         val () = maybe_evict ()
       in x end
     | obj => (maybe_evict (); dest_obj obj)
  end else mk_x p

  fun get_thm_id (id_ptr: thm_id ptr) = thmId heap id_ptr

  fun check_def map Thy nm =
    if Thy = thyname then case peek (map, nm)
    of SOME thps => List.app (ignore o replay_thm) thps
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

  and replay_subst env (sb_ptr: term Subst.subs ptr) =
    case shSubs heap sb_ptr of
      Cons (sbp,tmp) =>
        Subst.cons (replay_subst env sbp,
                    replay_term_sub env tmp)
    | Id => Subst.id
    | Lift (i,sbp) => Subst.lift(i, replay_subst env sbp)
    | Shift (i,sbp) => Subst.shift(i, replay_subst env sbp)

  and replay_term_sub env tm_ptr =
    if is_closed tm_ptr then replay_term tm_ptr
    else replay_term_core env tm_ptr

  and replay_term_core env tm_ptr =
    case shTerm heap tm_ptr of
      Abs (t1,t2) => let
        val x = replay_term_sub env t1
        val (s,ty) = dest_var x
        val g = genvar ty
        val b = replay_term_sub (Subst.cons(env,g)) t2
      in rename_bvar s (mk_abs(g,b)) end
    | Comb (t1,t2) => let
        val f = replay_term_sub env t1
        val x = replay_term_sub env t2
      in mk_comb(f,x) end
    | Const (idp,typ) => let
        val (Thy,Name) = ident heap idp
        val () = check_def tm_defs Thy Name
        val ty = replay_type typ
      in mk_thy_const {Thy=Thy, Name=Name, Ty=ty}
         handle e as (HOL_ERR _) =>
           if Thy = thyname then
             (msg_print("WARNING: prim_new_const "^Thy^"$"^Name^"\n");
              prim_new_const {Thy=Thy, Name=Name} ty)
           else raise e
      end
    | Fv (s,typ) => mk_var(s, replay_type typ)
    | Bv n => (case Subst.exp_rel(env, n) of
                 (0, SOME t) => t
               | (n, SOME t) => raise Fail "replay_term_core reloc"
               | _ => raise Fail "replay_term_core Bv")
    | Clos (sbp,tmp) =>
        replay_term_sub (Subst.comp #2 (env,replay_subst env sbp)) tmp

  and replay_term tm_ptr =
  cache (Tm,destTm) (replay_term_core Subst.id) tm_ptr

  and replay_thm (thm_ptr: thm ptr) =
  cache (Th,destTh) (fn thm_ptr => let
    val (hyp_ptr, concl_ptr, proof_ptr) = shThm heap thm_ptr
    val tm = replay_term
    val th = replay_thm
    val ty = replay_type
  in case shProof heap proof_ptr of
      ABS_prf (a, b) =>        ABS (tm a) (th b)
    | ALPHA_prf (a, b) =>      ALPHA (tm a) (tm b)
    | AP_TERM_prf (a, b) =>    AP_TERM (tm a) (th b)
    | AP_THM_prf (a, b) =>     AP_THM (th a) (tm b)
    | ASSUME_prf a =>          ASSUME (tm a)
    | Axiom_prf => let
        val h = ref (HOLset.empty Term.compare)
        fun add t = h := HOLset.add(!h, t)
        val () = appSet heap (add o replay_term) hyp_ptr
        val h = !h
        val c = replay_term concl_ptr
        val () = if HOLset.isEmpty h then () else raise Fail "Axiom hyps"
      in mk_axiom_thm(Nonce.mk(next_axiom_name()), c) end
    | BETA_CONV_prf a =>       BETA_CONV (tm a)
    | Beta_prf a =>            Beta (th a)
    | CCONTR_prf (a, b) =>     CCONTR (tm a) (th b)
    | CHOOSE_prf (a, b, c) =>  CHOOSE (tm a, th b) (th c)
    | CONJUNCT1_prf a =>       CONJUNCT1 (th a)
    | CONJUNCT2_prf a =>       CONJUNCT2 (th a)
    | CONJ_prf (a, b) =>       CONJ (th a) (th b)
    | DISCH_prf (a, b) =>      DISCH (tm a) (th b)
    | DISJ1_prf (a, b) =>      DISJ1 (th a) (tm b)
    | DISJ2_prf (a, b) =>      DISJ2 (tm a) (th b)
    | DISJ_CASES_prf (a, b, c) => DISJ_CASES (th a) (th b) (th c)
    | Def_const_list_prf (a, b) => let
        val ids = list heap get_const_id b
        val () = if List.all (equal thyname) (List.map #1 ids) then ()
                 else raise Fail "Def_const_list thy"
      in #2 (gen_prim_specification thyname (th a)) end
    | Def_const_prf (a, b) => let
        val (Thy,Name) = get_const_id b
        val rhs = tm a
        val thm = ASSUME (mk_eq(mk_var(Name, type_of rhs), rhs))
        val (_, thm) = gen_prim_specification Thy thm
        val () = register_def Thy Name thm
      in thm end
    | Def_spec_prf (a, b) => let
        val ids = list heap get_const_id b
        val () = if List.all (equal thyname) (List.map #1 ids) then ()
                 else raise Fail "Def_spec thy"
        val cnames = List.map #2 ids
      in prim_specification thyname cnames (th a) end
    | Def_tyop_prf (_, b, c) => let
        val (Thy,Tyop) = get_type_id c
        val thm = th b
        val () = if thyname = "bool"
                 then check_def tm_defs thyname "TYPE_DEFINITION"
                 else ()
      in prim_type_definition ({Thy=Thy, Tyop=Tyop}, thm) end
    | Disk_prf (thy, b) => let
        val id = get_thm_id b
      in case peek(!trDB, thy) of
          NONE => raise NeedsAncestor thy
        | SOME (named,anons) => (case id of
            SavedAnon i => (
              List.nth(anons, i) handle Subscript =>
                raise Fail ("Disk thy "^thy^":"^(Int.toString i)))
          | SavedName s => (
              case peek(named, s) of
                NONE => raise Fail ("Disk thy "^thy^"$"^s)
              | SOME th => th))
      end
    | EQ_IMP_RULE1_prf a => #1 (EQ_IMP_RULE (th a))
    | EQ_IMP_RULE2_prf a => #2 (EQ_IMP_RULE (th a))
    | EQ_MP_prf (a, b) =>      EQ_MP (th a) (th b)
    | EXISTS_prf (a, b, c) =>  EXISTS (tm a, tm b) (th c)
    | GENL_prf (a, b) =>       GENL (list heap replay_term a) (th b)
    | GEN_ABS_prf (a, b, c) => let
        val opt_tm = option heap replay_term a
        val tms = list heap replay_term b
      in GEN_ABS opt_tm tms (th c) end
    | GEN_prf (a, b) =>        GEN (tm a) (th b)
    | INST_TYPE_prf (a, b) => let
        val s = list heap (fn p => let
          val (a,b) = tuple2 heap (replay_type, replay_type) p
        in a |-> b end) a
      in INST_TYPE s (th b) end
    | INST_prf (a, b) => let
        val s = list heap (fn p => let
          val (a,b) = tuple2 heap (replay_term, replay_term) p
        in a |-> b end) a
      in INST s (th b) end
    | MK_COMB_prf (a, b) =>    MK_COMB (th a, th b)
    | MP_prf (a, b) =>         MP (th a) (th b)
    | Mk_abs_prf (a, _, c) => let
        val (_,_,mka) = Mk_abs (th a)
      in mka (th c) end
    | Mk_comb_prf (a, b, c) => let
        val (_,_,mkc) = Mk_comb (th a)
      in mkc (th b) (th c) end
    | NOT_ELIM_prf a =>        NOT_ELIM (th a)
    | NOT_INTRO_prf a =>       NOT_INTRO (th a)
    | REFL_prf a =>            REFL (tm a)
    | SPEC_prf (a, b) =>       SPEC (tm a) (th b)
    | SUBST_prf (a, b, c) => let
        val s = list heap (fn p => let
          val (a,b) = tuple2 heap (replay_term, replay_thm) p
        in a |-> b end) a
      in SUBST s (tm b) (th c) end
    | SYM_prf a =>        SYM (th a)
    | Specialize_prf (a, b) => Specialize (tm a) (th b)
    | TRANS_prf (a, b) =>      TRANS (th a) (th b)
    | compute_prf (a, b) => let
        val (compute_args_ptr, ths) = tuple2 heap (I, list heap replay_thm) a
        val t = tm b
        val () = if castPtr (!cached_compute_ptr) = castPtr compute_args_ptr then ()
          else let
            val {num_type, char_eqns, cval_type, cval_terms} =
              shComputeArgs heap compute_args_ptr
            val num_type = replay_type num_type
            val char_eqns = list heap (tuple2 heap (str heap, replay_thm)) char_eqns
            val cval_type = replay_type cval_type
            val cval_terms = list heap (tuple2 heap (str heap, replay_term)) cval_terms
          in
            cached_compute_ptr := compute_args_ptr;
            cached_compute := Thm.compute
              {num_type = num_type, char_eqns = char_eqns,
               cval_type = cval_type, cval_terms = cval_terms}
          end
      in (!cached_compute) ths t end
    | deductAntisym_prf (a, b) => raise Fail "replay_thm: deductAntisym not yet implemented"
    | deleted_prf =>              raise Fail "replay_thm: deleted not yet implemented"
    | save_dep_prf a => th a
  end) thm_ptr

  fun export p = let
    val (nm, (thp, _)) = tuple3 heap (str heap, I, I) p
    val () = dbg_print ("Replaying "^nm^"...")
    val th = replay_thm thp
    val () = dbg_print " done\n"
  in (nm, th) end

  val named = fromList String.compare (list heap export all_thms)
  val anons = list heap replay_thm anon_thms

  fun ensure_const p = let
    val (Name, ty) = tuple2 heap (str heap, replay_type) p
    val () = check_def tm_defs thyname Name
  in
    prim_mk_const {Thy=thyname, Name=Name}
    handle HOL_ERR _ =>
      (msg_print("WARNING: prim_new_const "^thyname^"$"^Name^"\n");
       prim_new_const {Thy=thyname, Name=Name} ty)
  end

  fun ensure_type p = let
    val (Tyop, ar) = tuple2 heap (str heap, int) p
    val () = check_def ty_defs thyname Tyop
  in case op_arity {Thy=thyname, Tyop=Tyop}
     of SOME n => if n = ar then () else
                  raise Fail ("ensure_type arity "^Tyop)
      | NONE => (msg_print("WARNING: prim_new_type "^thyname^"$"^Tyop^"\n");
                 prim_new_type {Thy=thyname, Tyop=Tyop} ar)
  end

  val () = appList heap ensure_const constants
  val () = appList heap ensure_type types

  val () = if !print_statistics then let
  val (live_ty, live_tm, live_th) =
    Array.foldl (fn (Ty _, (a,b,c)) => (a+1,b,c)
                  | (Tm _, (a,b,c)) => (a,b+1,c)
                  | (Th _, (a,b,c)) => (a,b,c+1)
                  | (_, acc) => acc) (0,0,0) replayed_heap
  val saturated = Word8Array.foldl (fn (0wxFF, n) => n+1 | (_, n) => n) 0 refcounts
  val pinned_count = BoolArray.foldl (fn (true, n) => n+1 | (_, n) => n) 0 pinned
  val () = print (concat [
    "  heap: ", Int.toString (heapSize heap),
    "  live: ", Int.toString live_ty, "ty/",
               Int.toString live_tm, "tm/",
               Int.toString live_th, "th",
    "  pinned: ", Int.toString pinned_count,
    "  sat: ", Int.toString saturated,
    "  named: ", Int.toString (numItems named),
    "  anons: ", Int.toString (length anons), "\n"])
  in () end else ()

in trDB := insert(!trDB, thyname, (named, anons)) end
handle e as (NeedsAncestor s) => (print("Ancestor missing: "^s^"\n"); raise e)
     | e as (HOL_ERR m) => (print("HOL_ERR: "^(Feedback.message_of m)^"\n"); raise e)
end (* let val thyname *)

fun trDB_size () = foldl (fn (_,(n,a), acc) =>
  acc + numItems n + length a) 0 (!trDB)

fun replay_sequence [] = ()
  | replay_sequence (thy::thys) =
    (msg_print thy; print ": ";
     if !print_statistics then
       print ("trDB: " ^ Int.toString (trDB_size ()) ^ " thms  ")
     else ();
     (if !print_statistics then time else I) replay (thy ^ "Theory.tr.gz");
     replay_sequence thys)

fun replayed_thms s = find(!trDB, s)

(*

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

*)
end
