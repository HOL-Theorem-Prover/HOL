(*
val _ = PolyML.use (OS.Path.concat(Globals.HOLDIR, "tools-poly/holinteractive.ML"));
*)
open Lib HolKernel Redblackmap ProofTraceParser

fun apply f g = f g
fun mk_eq(l,r) = list_mk_icomb equality [l,r]
datatype thm_id = SavedAnon of int | SavedName of string

fun mk_rules {string,term,thm,hol_type,list,pair,opt,four,
              new_term,new_type,thm_id} =
   Array.fromList [
      (* 0  *) ("ABS", [term, thm]),
      (* 1  *) ("ALPHA", [term, term]),
      (* 2  *) ("AP_TERM", [term, thm]),
      (* 3  *) ("AP_THM", [thm, term]),
      (* 4  *) ("ASSUME", [term]),
      (* 5  *) ("Axiom", []),
      (* 6  *) ("BETA_CONV", [term]),
      (* 7  *) ("Beta", [thm]),
      (* 8  *) ("CCONTR", [term, thm]),
      (* 9  *) ("CHOOSE", [term, thm, thm]),
      (* 10 *) ("CONJUNCT1", [thm]),
      (* 11 *) ("CONJUNCT2", [thm]),
      (* 12 *) ("CONJ", [thm, thm]),
      (* 13 *) ("DISCH", [term, thm]),
      (* 14 *) ("DISJ1", [thm, term]),
      (* 15 *) ("DISJ2", [term, thm]),
      (* 16 *) ("DISJ_CASES", [thm, thm, thm]),
      (* 17 *) ("Def_const_list", [thm, list new_term]),
      (* 18 *) ("Def_const", [term, new_term]),
      (* 19 *) ("Def_spec", [thm, list new_term]),
      (* 20 *) ("Def_tyop", [list hol_type, thm, new_type]),
      (* 21 *) ("Disk", [string, thm_id]),
      (* 22 *) ("EQ_IMP_RULE1", [thm]),
      (* 23 *) ("EQ_IMP_RULE2", [thm]),
      (* 24 *) ("EQ_MP", [thm, thm]),
      (* 25 *) ("EXISTS", [term, term, thm]),
      (* 26 *) ("GENL", [list term, thm]),
      (* 27 *) ("GEN_ABS", [opt term, list term, thm]),
      (* 28 *) ("GEN", [term, thm]),
      (* 29 *) ("INST_TYPE", [list (pair (hol_type, hol_type)), thm]),
      (* 30 *) ("INST", [list (pair (term, term)), thm]),
      (* 31 *) ("MK_COMB", [thm, thm]),
      (* 32 *) ("MP", [thm, thm]),
      (* 33 *) ("Mk_abs", [thm, term, thm]),
      (* 34 *) ("Mk_comb", [thm, thm, thm]),
      (* 35 *) ("NOT_ELIM", [thm]),
      (* 36 *) ("NOT_INTRO", [thm]),
      (* 37 *) ("REFL", [term]),
      (* 38 *) ("SPEC", [term, thm]),
      (* 39 *) ("SUBST", [list (pair (term, thm)), term, thm]),
      (* 40 *) ("SYM", [thm]),
      (* 41 *) ("Specialize", [term, thm]),
      (* 42 *) ("TRANS", [thm, thm]),
      (* 43 *) ("compute", [pair (four (hol_type, list (pair (string, thm)),
                               hol_type, list (pair (string, term))),
                         list thm), term]),
      (* 44 *) ("deductAntisym", [thm, thm]),
      (* 45 *) ("deleted", [])
  ]
(*
  compute_prf of (compute_args * thm list) * term
  where compute_args = {
    num_type   : hol_type,
    char_eqns  : (string * thm) list,
    cval_type  : hol_type,
    cval_terms : (string * term) list }
*)

val trDB : (string, (string, thm) dict * thm list) dict ref
  = ref (mkDict String.compare)

datatype hol_obj = Ty of hol_type | Tm of term | Th of thm | Unknown
fun destTy (Ty ty) = ty | destTy _ = raise Fail "destTy"
fun destTm (Tm tm) = tm | destTm _ = raise Fail "destTm"
fun destTh (Th th) = th | destTh _ = raise Fail "destTh"

val next_axiom_name = let
  val names = ref ["BOOL_CASES_AX", "SELECT_AX", "ETA_AX", "INFINITY_AX"]
in
  fn () => case !names of x::xs => x before names := xs
           | _ => raise Fail "next_axiom_name"
end

(*
val thyname = "bool";
*)
val dbg_print : string -> unit = (* print *) K ()

exception NeedsAncestor of string

fun replay thyname =
  if inDomain(!trDB, thyname)
  then print("skip ")
  else
let
  val filename = thyname ^ "Theory.tr.gz";
  val (root_ptr, heap) = parse filename;
  val {all_thms, anon_thms, ...} = shRoot heap root_ptr;

  val id_cache : (string * string) PIntMap.t ref = ref PIntMap.empty
  fun cache_id f p =
    let val key = ptr p
        val idc = !id_cache
    in PIntMap.find key idc
       handle PIntMap.NotFound =>
         let val x = f p
         in (id_cache := PIntMap.add key x idc; x)
         end
    end
  val get_const_id = cache_id (fn tm_ptr =>
    case shTerm heap tm_ptr of Const (idp,_) => ident heap idp
    | _ => raise Fail "get_const_id")
  val get_type_id = cache_id (fn ty_ptr =>
    case shType heap ty_ptr of Tyapp (idp,_) => ident heap idp
    | _ => raise Fail "get_type_id")

  (* Closedness pre-pass: compute max free Bv index for each term pointer.
     ~1 means closed (no free Bv's), n >= 0 means max free Bv index.
     ~2 = unvisited. Clos is treated conservatively as open. *)
  val closedness = Array.array(heapSize heap, ~2 : int)
  fun compute_closedness tm_ptr =
    if not (isPtr tm_ptr) then ~1
    else let val key = ptr tm_ptr
             val c = Array.sub(closedness, key)
    in if c <> ~2 then c else let
      val result = case shTerm heap tm_ptr of
          Const _ => ~1
        | Fv _    => ~1
        | Bv n    => n
        | Comb (t1, t2) =>
            Int.max(compute_closedness t1, compute_closedness t2)
        | Abs (_, t2) =>
            compute_closedness t2 - 1
        | Clos _ => 999
      in Array.update(closedness, key, result); result end
    end
  fun is_closed tm_ptr = isPtr tm_ptr andalso compute_closedness tm_ptr < 0

  (* Combined pre-pass: collect defs and count thm+term+type references *)
  val tm_defs : (string, thm ptr list) dict ref = ref (mkDict String.compare)
  val ty_defs : (string, thm ptr list) dict ref = ref (mkDict String.compare)
  val refcounts = Array.array(heapSize heap, 0 : int)
  val pinned = BoolArray.array(heapSize heap, false)
  val () = let
    val seen = BoolArray.array(heapSize heap, false)
    fun incr p = if isPtr p then let val k = ptr p in
      Array.update(refcounts, k, Array.sub(refcounts, k) + 1)
    end else ()
    fun first_seen p =
      if not (isPtr p) then false
      else if BoolArray.sub(seen, ptr p) then false
      else (BoolArray.update(seen, ptr p, true); true)
    (* Walk type structure. Increment refcount on every encounter,
       but only recurse into sub-types on first encounter (matching
       replay_type's cache behavior). *)
    fun walk_type (ty_ptr: hol_type ptr) =
      if not (first_seen ty_ptr) then () else
      case shType heap ty_ptr of
        Tyv _ => ()
      | Tyapp (_, args_ptr) =>
          appList heap (fn p => (incr p; walk_type (castPtr p))) args_ptr
    (* Walk term structure to count references to closed sub-terms and types.
       Mirrors what replay_term_core will do: closed sub-terms go through
       cache (so count them and recurse on first encounter), open sub-terms
       are traversed inline. *)
    fun walk_term (tm_ptr: term ptr) =
      if is_closed tm_ptr
      then (incr tm_ptr;
            if first_seen tm_ptr then walk_term_inner tm_ptr else ())
      else walk_term_inner tm_ptr
    and walk_term_inner tm_ptr =
      if not (isPtr tm_ptr) then () else
      case shTerm heap tm_ptr of
        Abs (t1, t2) => (walk_term t1; walk_term t2)
      | Comb (t1, t2) => (walk_term t1; walk_term t2)
      | Const (_, typ) => (incr typ; walk_type (castPtr typ))
      | Fv (_, typ) => (incr typ; walk_type (castPtr typ))
      | Bv _ => ()
      | Clos (sbp, tmp) => (walk_subs sbp; walk_term tmp)
    and walk_subs sbp =
      case shSubs heap sbp of
        Cons (sbp', tmp) => (walk_subs sbp'; walk_term tmp)
      | Id => ()
      | Lift (_, sbp') => walk_subs sbp'
      | Shift (_, sbp') => walk_subs sbp'
    fun walk_thm (thm_ptr: thm ptr) =
      if not (isPtr thm_ptr) then ()
      else if BoolArray.sub(seen, ptr thm_ptr) then ()
      else let
        val () = BoolArray.update(seen, ptr thm_ptr, true)
        val (_, _, proof_ptr) = shThm heap thm_ptr
        val (i, args_ptrs) = shVariant heap proof_ptr
        val rs = mk_rules {
          string = K (), new_term = K (), new_type = K (), thm_id = K (),
          hol_type = fn p => (incr p; walk_type (castPtr p)),
          term = fn p => (incr p;
            if first_seen (castPtr p) then walk_term_inner (castPtr p)
            else ()),
          thm = fn p => (incr p; walk_thm (castPtr p)),
          list = fn f => appList heap f o castPtr,
          opt = fn f => ignore o option heap f o castPtr,
          pair = fn fg => ignore o tuple2 heap fg o castPtr,
          four = fn fghi => ignore o tuple4 heap fghi o castPtr
        }
        val (rule_name, args_rs) = Array.sub(rs, i)
        (* Collect defs and pin their thm pointers *)
        fun add_thm_ptr nm prev =
              (BoolArray.update(pinned, ptr thm_ptr, true);
               case prev of NONE => [thm_ptr]
                 | SOME ls => (print("WARNING: multiple defs for "^nm^"\n");
                               thm_ptr::ls))
        fun check_thy defthy =
          if defthy = thyname then () else raise Fail "add_def thy"
        fun add_const nm = tm_defs := update(!tm_defs, nm, add_thm_ptr nm)
        val () = if rule_name <> "Def_const_list" andalso
                    rule_name <> "Def_spec" then () else let
          val ids = list heap get_const_id (castPtr (el 2 args_ptrs))
          fun go (thy,nm) = (check_thy thy; add_const nm)
        in List.app go ids end
        val () = if rule_name <> "Def_const" then () else let
          val (thy,nm) = get_const_id (castPtr (el 2 args_ptrs))
          val () = check_thy thy
        in add_const nm end
        val () = if rule_name <> "Def_tyop" then () else let
          val (thy,tyop) = get_type_id (castPtr (el 3 args_ptrs))
          val () = check_thy thy
        in ty_defs := update(!ty_defs, tyop, add_thm_ptr tyop) end
        val _ = map2 apply args_rs args_ptrs
      in () end
    fun pre_named p = let
      val (_, (thp, _)) = tuple3 heap (I, I, I) p
    in incr thp; walk_thm thp end
    fun pre_anon p = (incr p; walk_thm (castPtr p))
  in
    appList heap pre_named all_thms;
    appList heap pre_anon anon_thms
  end
  val tm_defs = !tm_defs
  val ty_defs = !ty_defs

  val replayed_heap = Array.array(heapSize heap, Unknown);

  val cached_compute_ptr : unit ptr ref = ref (castPtr root_ptr)
  val cached_compute : (thm list -> term -> thm) ref
    = ref (fn _ => raise Bind)

  fun cache (mk_obj, dest_obj) mk_x ptr_ =
  if isPtr ptr_ then let
    val key = ptr ptr_
    fun maybe_evict () =
      if BoolArray.sub(pinned, key) then () else let
        val rc = Array.sub(refcounts, key) - 1
        val () = Array.update(refcounts, key, rc)
      in if rc <= 0
         then Array.update(replayed_heap, key, Unknown)
         else ()
      end
  in case Array.sub(replayed_heap, key) of
       Unknown => let
         val x = mk_x ptr_
         val () = Array.update(replayed_heap, key, mk_obj x)
         val () = maybe_evict ()
       in x end
     | obj => (maybe_evict (); dest_obj obj)
  end else mk_x ptr_

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
             (print("WARNING: prim_new_const "^Thy^"$"^Name^"\n");
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
      in new_axiom(next_axiom_name(), c) end
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

in trDB := insert(!trDB, thyname, (named, anons)) end

fun replay_seq [] = ()
  | replay_seq (thy::thys) =
    (print thy; print ": ";
     PolyML.fullGC();
     time replay thy;
     replay_seq thys)

val seq = ["bool", "marker", "num", "sat", "combin",
           "relation", "prim_rec", "quotient", "pair",
           "arithmetic", "numeral", "cv", "numpair",
           "ind_type", "one", "sum", "option", "While",
           "reduce", "divides", "normalForms", "pred_set",
           "basicSize", "list", "rich_list", "sorting",
           "finite_map", "alist", "indexedLists", "logroot",
           "sptree", "permutes", "iterate", "fcp", "bit",
           "ternaryComparisons", "string", "numposrep",
           "ASCIInumbers", "sum_num", "numeral_bit", "words",
           "set_sep", "byte", "bitstring", "set_relation",
           "llist", "poset", "fixedPoint", "path", "alignment",
           "address", "bag", "misc", "toto", "comparison",
           "mergesort", "mllist", "mlstring", "normalizer", "gcd",
           "integer", "int_arith", "cooper", "Omega", "integer_word",
           "hrat", "hreal", "realax", "real_arith", "real", "intreal",
           "blast", "multiword", "tailrec", "mc_multiword",
           "binary_ieee", "machine_ieee", "namespace", "location",
           "quantHeuristics", "ConseqConv", "patternMatches",
           "balanced_map", "ast", "asm", "ffi", "lprefix_lub", "fpSem",
           "semanticPrimitives", "ml_monadBase", "backend_common",
           "backendProps", "reg_alloc", "linear_scan",
           "stackLang", "wordLang", "wordConvs",
           "word_bignum", "word_alloc", "word_remove", "word_unreach",
           "word_inst", "word_copy", "word_cse", "word_simp",
           "word_to_word", "wordSem", "wordProps",
           "word_bignumProof", "word_simpProof",
           "reg_allocProof", "linear_scanProof", "word_allocProof",
           "wordConvsProof", "word_unreachProof", "word_cseProof",
           "word_instProof", "word_copyProof", "word_removeProof",
           "word_to_wordProof"]

val () = replay_seq seq

(*
val (boolDB, boolAs) = find(!trDB,"bool")
val (markerDB, markerAs) = find(!trDB,"marker")
val (numDB, numAs) = find(!trDB,"num")
val (listDB, listAs) = find(!trDB,"list")
val (miscDB, miscAs) = find(!trDB,"misc")

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

print_tm(concl(List.nth(miscAs,0)))
print_tm(concl(List.nth(listAs,3)))
val LENGTH_MAP = find(listDB,"LENGTH_MAP")
Tag.dest_tag $ Thm.tag LENGTH_MAP
print_tm(concl LENGTH_MAP)
print_tm(concl(find(boolDB,"INFINITY_AX")))
print_tm(concl(find(markerDB,"Case_def")))
print_tm(concl(find(numDB,"NOT_SUC")))
*)
