structure ProofTraceReplay :> ProofTraceReplay = struct

(*
(* interactive use in hol --min *)
val _ = PolyML.use (OS.Path.concat(Globals.HOLDIR, "tools-poly/holinteractive.ML"));
qload "ProofTraceParser";
qload "PIntMap";
*)

open Feedback Lib Type Term Thm Redblackmap ProofTraceParser

fun mk_eq(l,r) = list_mk_comb(inst[alpha |-> type_of l]equality, [l,r])
datatype thm_id = SavedAnon of int | SavedName of string

(*
  Proof rule indices (source of truth for both walk_thm and replay_thm):
   0  ABS (term, thm)            23 EQ_IMP_RULE2 (thm)
   1  ALPHA (term, term)         24 EQ_MP (thm, thm)
   2  AP_TERM (term, thm)        25 EXISTS (term, term, thm)
   3  AP_THM (thm, term)         26 GENL (list term, thm)
   4  ASSUME (term)              27 GEN_ABS (opt term, list term, thm)
   5  Axiom ()                   28 GEN (term, thm)
   6  BETA_CONV (term)           29 INST_TYPE (list(pair(ty,ty)), thm)
   7  Beta (thm)                 30 INST (list(pair(tm,tm)), thm)
   8  CCONTR (term, thm)         31 MK_COMB (thm, thm)
   9  CHOOSE (term, thm, thm)    32 MP (thm, thm)
  10  CONJUNCT1 (thm)            33 Mk_abs (thm, term, thm)
  11  CONJUNCT2 (thm)            34 Mk_comb (thm, thm, thm)
  12  CONJ (thm, thm)            35 NOT_ELIM (thm)
  13  DISCH (term, thm)          36 NOT_INTRO (thm)
  14  DISJ1 (thm, term)          37 REFL (term)
  15  DISJ2 (term, thm)          38 SPEC (term, thm)
  16  DISJ_CASES (thm,thm,thm)   39 SUBST (list(pair(tm,th)), term, thm)
  17  Def_const_list (thm,       40 SYM (thm)
        list new_term)           41 Specialize (term, thm)
  18  Def_const (term, new_term) 42 TRANS (thm, thm)
  19  Def_spec (thm,             43 compute (pair(four(ty,list(pair(str,th)),
        list new_term)                 ty,list(pair(str,tm))),list th),term)
  20  Def_tyop (list ty,         44 deductAntisym (thm, thm)
        thm, new_type)           45 deleted ()
  21  Disk (string, thm_id)
  22  EQ_IMP_RULE1 (thm)
*)

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

exception NeedsAncestor of string

fun replay thyname =
  if inDomain(!trDB, thyname)
  then msg_print("skip ")
  else
let
  val filename = thyname ^ "Theory.tr.gz";
  val (root_ptr, heap) = parse filename;
  val {all_thms, anon_thms, ...} = shRoot heap root_ptr;

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

  val cached_compute_ptr : unit ptr ref = ref (castPtr root_ptr)
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

  fun get_thm_id (id_ptr: thm_id ptr) = let
    val (i,ps) = shVariant heap id_ptr
    val p = el 1 ps
  in if i = 0 then SavedAnon (int (castPtr p))
     else SavedName (str heap (castPtr p)) end

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
    val (i, args_ptrs) = shVariant heap proof_ptr
    fun tm n = replay_term (castPtr (el n args_ptrs))
    fun th n = replay_thm (castPtr (el n args_ptrs))
    fun ty n = replay_type (castPtr (el n args_ptrs))
  in case i of
      0  => (* ABS *)        ABS (tm 1) (th 2)
    | 1  => (* ALPHA *)      ALPHA (tm 1) (tm 2)
    | 2  => (* AP_TERM *)    AP_TERM (tm 1) (th 2)
    | 3  => (* AP_THM *)     AP_THM (th 1) (tm 2)
    | 4  => (* ASSUME *)     ASSUME (tm 1)
    | 5  => (* Axiom *) let
        val h = ref (HOLset.empty Term.compare)
        fun add t = h := HOLset.add(!h, t)
        val () = appSet heap (add o replay_term) hyp_ptr
        val h = !h
        val c = replay_term concl_ptr
        val () = if HOLset.isEmpty h then () else raise Fail "Axiom hyps"
      in mk_axiom_thm(Nonce.mk(next_axiom_name()), c) end
    | 6  => (* BETA_CONV *)  BETA_CONV (tm 1)
    | 7  => (* Beta *)       Beta (th 1)
    | 8  => (* CCONTR *)     CCONTR (tm 1) (th 2)
    | 9  => (* CHOOSE *)     CHOOSE (tm 1, th 2) (th 3)
    | 10 => (* CONJUNCT1 *)  CONJUNCT1 (th 1)
    | 11 => (* CONJUNCT2 *)  CONJUNCT2 (th 1)
    | 12 => (* CONJ *)       CONJ (th 1) (th 2)
    | 13 => (* DISCH *)      DISCH (tm 1) (th 2)
    | 14 => (* DISJ1 *)      DISJ1 (th 1) (tm 2)
    | 15 => (* DISJ2 *)      DISJ2 (tm 1) (th 2)
    | 16 => (* DISJ_CASES *) DISJ_CASES (th 1) (th 2) (th 3)
    | 17 => (* Def_const_list *) let
        val ids = list heap get_const_id (castPtr (el 2 args_ptrs))
        val () = if List.all (equal thyname) (List.map #1 ids) then ()
                 else raise Fail "Def_const_list thy"
      in #2 (gen_prim_specification thyname (th 1)) end
    | 18 => (* Def_const *) let
        val (Thy,Name) = get_const_id (castPtr (el 2 args_ptrs))
        val rhs = tm 1
        val thm = ASSUME (mk_eq(mk_var(Name, type_of rhs), rhs))
      in #2 (gen_prim_specification Thy thm) end
    | 19 => (* Def_spec *) let
        val ids = list heap get_const_id (castPtr (el 2 args_ptrs))
        val () = if List.all (equal thyname) (List.map #1 ids) then ()
                 else raise Fail "Def_spec thy"
        val cnames = List.map #2 ids
      in prim_specification thyname cnames (th 1) end
    | 20 => (* Def_tyop *) let
        val (Thy,Tyop) = get_type_id (castPtr (el 3 args_ptrs))
        val thm = th 2
        val () = if thyname = "bool"
                 then check_def tm_defs thyname "TYPE_DEFINITION"
                 else ()
      in prim_type_definition ({Thy=Thy, Tyop=Tyop}, thm) end
    | 21 => (* Disk *) let
        val thy = str heap (castPtr (el 1 args_ptrs))
        val id = get_thm_id (castPtr (el 2 args_ptrs))
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
    | 22 => (* EQ_IMP_RULE1 *) #1 (EQ_IMP_RULE (th 1))
    | 23 => (* EQ_IMP_RULE2 *) #2 (EQ_IMP_RULE (th 1))
    | 24 => (* EQ_MP *)      EQ_MP (th 1) (th 2)
    | 25 => (* EXISTS *)     EXISTS (tm 1, tm 2) (th 3)
    | 26 => (* GENL *)       GENL (list heap (replay_term o castPtr)
                                   (castPtr (el 1 args_ptrs))) (th 2)
    | 27 => (* GEN_ABS *) let
        val opt_tm = option heap (replay_term o castPtr)
                                 (castPtr (el 1 args_ptrs))
        val tms = list heap (replay_term o castPtr)
                            (castPtr (el 2 args_ptrs))
      in GEN_ABS opt_tm tms (th 3) end
    | 28 => (* GEN *)        GEN (tm 1) (th 2)
    | 29 => (* INST_TYPE *) let
        val s = list heap (fn p => let
          val (a,b) = tuple2 heap
            (replay_type o castPtr, replay_type o castPtr) (castPtr p)
        in a |-> b end) (castPtr (el 1 args_ptrs))
      in INST_TYPE s (th 2) end
    | 30 => (* INST *) let
        val s = list heap (fn p => let
          val (a,b) = tuple2 heap
            (replay_term o castPtr, replay_term o castPtr) (castPtr p)
        in a |-> b end) (castPtr (el 1 args_ptrs))
      in INST s (th 2) end
    | 31 => (* MK_COMB *)    MK_COMB (th 1, th 2)
    | 32 => (* MP *)         MP (th 1) (th 2)
    | 33 => (* Mk_abs *) let
        val (_,_,mka) = Mk_abs (th 1)
      in mka (th 3) end
    | 34 => (* Mk_comb *) let
        val (_,_,mkc) = Mk_comb (th 1)
      in mkc (th 2) (th 3) end
    | 35 => (* NOT_ELIM *)   NOT_ELIM (th 1)
    | 36 => (* NOT_INTRO *)  NOT_INTRO (th 1)
    | 37 => (* REFL *)       REFL (tm 1)
    | 38 => (* SPEC *)       SPEC (tm 1) (th 2)
    | 39 => (* SUBST *) let
        val s = list heap (fn p => let
          val (a,b) = tuple2 heap
            (replay_term o castPtr, replay_thm o castPtr) (castPtr p)
        in a |-> b end) (castPtr (el 1 args_ptrs))
      in SUBST s (tm 2) (th 3) end
    | 40 => (* SYM *)        SYM (th 1)
    | 41 => (* Specialize *) Specialize (tm 1) (th 2)
    | 42 => (* TRANS *)      TRANS (th 1) (th 2)
    | 43 => (* compute *) let
        val (compute_args_ptr, ths_ptr) =
          tuple2 heap (I, I) (castPtr (el 1 args_ptrs))
        val ths = list heap (replay_thm o castPtr) ths_ptr
        val t = tm 2
        val () = if !cached_compute_ptr = compute_args_ptr then ()
          else let
            val (num_type_ptr, (eqns_ptr, (cval_type_ptr, cterms_ptr))) =
              tuple4 heap (I, I, I, I) (castPtr compute_args_ptr)
            val num_type = replay_type (castPtr num_type_ptr)
            val char_eqns = list heap (fn p =>
              tuple2 heap (str heap, replay_thm o castPtr) (castPtr p))
              eqns_ptr
            val cval_type = replay_type (castPtr cval_type_ptr)
            val cval_terms = list heap (fn p =>
              tuple2 heap (str heap, replay_term o castPtr) (castPtr p))
              cterms_ptr
          in
            cached_compute_ptr := compute_args_ptr;
            cached_compute := Thm.compute
              {num_type = num_type, char_eqns = char_eqns,
               cval_type = cval_type, cval_terms = cval_terms}
          end
      in (!cached_compute) ths t end
    | 44 => (* deductAntisym *)
        raise Fail "replay_thm: deductAntisym not yet implemented"
    | 45 => (* deleted *)
        raise Fail "replay_thm: deleted not yet implemented"
    | n => raise Fail ("replay_thm: unknown rule " ^ Int.toString n)
  end) thm_ptr

  fun export p = let
    val (nm, (thp, _)) = tuple3 heap (str heap, I, I) p
    val () = dbg_print ("Replaying "^nm^"...")
    val th = replay_thm thp
    val () = dbg_print " done\n"
  in (nm, th) end

  val named = fromList String.compare (list heap export all_thms)
  val anons = list heap replay_thm anon_thms

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

fun trDB_size () = foldl (fn (_,(n,a), acc) =>
  acc + numItems n + length a) 0 (!trDB)

fun replay_sequence [] = ()
  | replay_sequence (thy::thys) =
    (msg_print thy; print ": ";
     if !print_statistics then
       print ("trDB: " ^ Int.toString (trDB_size ()) ^ " thms  ")
     else ();
     (if !print_statistics then time else I) replay thy;
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
