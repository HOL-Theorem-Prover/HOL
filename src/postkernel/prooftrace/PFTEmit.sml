structure PFTEmit :> PFTEmit = struct

open Lib Redblackmap ProofTraceParser

(* --- ID allocator for a PFT namespace ------------------------------------ *)

type id_alloc = {
  alloc : unit -> int,
  free : int -> unit,
  peak : unit -> int
}

fun mk_id_alloc () : id_alloc = let
  val next = ref 0
  val peak = ref 0
  val freelist : int list ref = ref []
  fun alloc () = case !freelist of
      i :: rest => (freelist := rest; i)
    | [] => let val i = !next in
        next := i + 1;
        peak := Int.max(!peak, i + 1);
        i
      end
  fun free_id i = freelist := i :: !freelist
  fun get_peak () = !peak
in {alloc = alloc, free = free_id, peak = get_peak} end

(* --- Utilities ----------------------------------------------------------- *)

fun thyname_of_path path = let
  val file = OS.Path.file path
in
  if String.isSuffix "Theory.tr.gz" file
  then String.substring(file, 0, String.size file - 12)
  else raise Fail ("PFTEmit: expected <thy>Theory.tr.gz, got " ^ file)
end

(* thm_id as stored in Disk references *)
datatype thm_id = DiskAnon of int | DiskName of string

fun get_thm_id heap (id_ptr : thm_id ptr) = let
  val (i, ps) = shVariant heap id_ptr
  val p = el 1 ps
in if i = 0 then DiskAnon (int (castPtr p))
   else DiskName (str heap (castPtr p))
end

fun disk_save_name thy (DiskAnon i) = thy ^ "#" ^ Int.toString i
  | disk_save_name thy (DiskName s) = thy ^ "$" ^ s

(* --- emit_theory --------------------------------------------------------- *)

fun emit_theory {trace, output, binary} = let
  val thyname = thyname_of_path trace
  val (root_ptr, heap) = parse trace
  val {all_thms, anon_thms, constants, types, ...} = shRoot heap root_ptr

  val out = PFTWriter.openOut
    {file = output, binary = binary, version = 1, ruleset = "hol4"}

  val ty_ids = mk_id_alloc ()
  val tm_ids = mk_id_alloc ()
  val th_ids = mk_id_alloc ()
  val ci_ids = mk_id_alloc ()

  (* Refcounts: exact integer counts *)
  val refcounts = Array.array(heapSize heap, 0 : int)
  val pinned = BoolArray.array(heapSize heap, false)
  fun incr (p : unit ptr) = if isPtr p then
    Array.update(refcounts, ptr p, Array.sub(refcounts, ptr p) + 1)
  else ()
  fun on_def_thm (thm_ptr : Thm.thm ptr) =
    BoolArray.update(pinned, ptr thm_ptr, true)

  val {tm_defs, ty_defs, is_closed, get_const_id, get_type_id} =
    ProofTraceWalk.walk
      {heap = heap, thyname = thyname,
       named_thms = all_thms, anon_thms = anon_thms,
       incr = incr, on_def_thm = on_def_thm}

  (* Heap ptr -> PFT ID mappings (~1 = not yet emitted) *)
  val ty_map = Array.array(heapSize heap, ~1)
  val tm_map = Array.array(heapSize heap, ~1)
  val th_map = Array.array(heapSize heap, ~1)

  (* Track which constants/types have been introduced (by DEF_SPEC/DEF_TYOP
     or NEW_CONST/NEW_TYPE) so we know when to emit NEW_CONST/NEW_TYPE. *)
  val const_done : (string, unit) Redblackmap.dict ref =
    ref (mkDict String.compare)
  val type_done : (string, unit) Redblackmap.dict ref =
    ref (mkDict String.compare)
  fun mark_const name = const_done := insert(!const_done, name, ())
  fun mark_type name = type_done := insert(!type_done, name, ())
  fun is_const_done name = case peek(!const_done, name) of SOME _ => true | NONE => false
  fun is_type_done name = case peek(!type_done, name) of SOME _ => true | NONE => false

  (* Protection counter: prevents eviction of objects that have been
     captured by an outer emit_thm but whose command hasn't been written
     yet. Nested emit_thm chains can decrement refcounts to 0, but
     eviction is blocked while protect_count > 0. *)
  val protect_count = Array.array(heapSize heap, 0 : int)
  fun protect (p : 'a ptr) =
    if isPtr p then
      Array.update(protect_count, ptr p,
                   Array.sub(protect_count, ptr p) + 1)
    else ()
  fun unprotect (p : 'a ptr) =
    if isPtr p then
      Array.update(protect_count, ptr p,
                   Array.sub(protect_count, ptr p) - 1)
    else ()

  fun decr ns id_map free_id (p : 'a ptr) =
    if not (isPtr p) then () else let
      val k = ptr p
      val rc = Array.sub(refcounts, k) - 1
    in
      Array.update(refcounts, k, rc);
      if rc <= 0 andalso not (BoolArray.sub(pinned, k))
                 andalso Array.sub(protect_count, k) <= 0 then let
        val pft_id = Array.sub(id_map, k)
      in if pft_id >= 0 then
           (PFTWriter.del out ns pft_id;
            free_id pft_id;
            Array.update(id_map, k, ~1))
         else ()
      end
      else ()
    end
  val decr_ty = decr "ty" ty_map (#free ty_ids)
  val decr_tm = decr "tm" tm_map (#free tm_ids)
  val decr_th = decr "th" th_map (#free th_ids)

  (* --- Type emission --------------------------------------------------- *)

  (* emit_type: emit a type, returning its PFT ID. Cached.
     Does NOT decrement refcount — caller is responsible. *)
  fun emit_type (ty_ptr : Type.hol_type ptr) : int =
    if not (isPtr ty_ptr) then raise Fail "emit_type: not a ptr"
    else let val k = ptr ty_ptr
             val cached = Array.sub(ty_map, k)
    in if cached >= 0 then cached
       else let
         val id = #alloc ty_ids ()
         val () = Array.update(ty_map, k, id)
       in case shType heap ty_ptr of
            Tyv s => (PFTWriter.tyvar out id s; id)
          | Tyapp (idp, args_ptr) => let
              val (Thy, Tyop) = ident heap idp
              val () = check_def ty_defs Thy Tyop
              (* Protect each arg after emitting to prevent subsequent
                 arg emissions from evicting earlier args *)
              val arg_ids = list heap
                (fn p => let val r = emit_type (castPtr p)
                         in protect (castPtr p : Type.hol_type ptr); r
                         end) args_ptr
              val () = if Thy = thyname andalso not (is_type_done Tyop)
                       then (mark_type Tyop;
                             PFTWriter.new_type out (Thy ^ "$" ^ Tyop)
                               (length arg_ids))
                       else ()
              val name = Thy ^ "$" ^ Tyop
              val () = PFTWriter.tyop out id name arg_ids
              val () = appList heap
                (fn p => let val q : Type.hol_type ptr = castPtr p
                         in unprotect q; decr_ty q end)
                (castPtr args_ptr)
            in id end
       end
    end

  (* Emit a type by name (for synthesized types in Def_const).
     These are not in the heap, so no refcount tracking. *)
  and emit_tyop_by_name thy tyop args = let
    val id = #alloc ty_ids ()
  in PFTWriter.tyop out id (thy ^ "$" ^ tyop) args; id end

  (* --- Term emission --------------------------------------------------- *)

  (* De Bruijn to named variable conversion.
     env : int Subst.subs — maps de Bruijn indices to PFT term IDs.
     Closed terms are cached; open terms are emitted inline.

     Refcount convention: emit_term and emit_term_sub do NOT decrement
     the pointer they receive — the caller is responsible. This matches
     the walk where incr happens at the call site (walk_thm's tm/th/ty
     helpers, walk_term for closed sub-terms, walk_term_inner for
     Const/Fv type refs). *)

  and emit_term (tm_ptr : Term.term ptr) : int =
    if not (isPtr tm_ptr) then raise Fail "emit_term: not a ptr"
    else let val k = ptr tm_ptr
             val cached = Array.sub(tm_map, k)
    in if cached >= 0 then cached
       else emit_term_sub Subst.id tm_ptr
    end

  and emit_term_sub env (tm_ptr : Term.term ptr) : int =
    if is_closed tm_ptr then emit_term_closed tm_ptr
    else emit_term_core env tm_ptr

  and emit_term_closed (tm_ptr : Term.term ptr) : int = let
    val k = ptr tm_ptr
    val cached = Array.sub(tm_map, k)
  in if cached >= 0 then cached
     else let val id = emit_term_core Subst.id tm_ptr
          in (* Don't cache Clos: the returned PFT ID belongs to the
                body, so caching would alias two tm_map entries to the
                same PFT ID, causing double-free on eviction. *)
             case shTerm heap tm_ptr of
               Clos _ => id
             | _ => (Array.update(tm_map, k, id); id)
          end
  end

  and emit_term_core env (tm_ptr : Term.term ptr) : int =
    case shTerm heap tm_ptr of
      Fv (s, typ) => let
        val ty_id = emit_type typ
        val id = #alloc tm_ids ()
        val () = PFTWriter.var out id s ty_id
        (* decr type AFTER VAR command is written *)
        val () = decr_ty typ
      in id end
    | Const (idp, typ) => let
        val (Thy, Name) = ident heap idp
        val () = check_def tm_defs Thy Name
        val ty_id = emit_type typ
        val () = if Thy = thyname andalso not (is_const_done Name)
                 then (mark_const Name;
                       PFTWriter.new_const out (Thy ^ "$" ^ Name) ty_id)
                 else ()
        val id = #alloc tm_ids ()
        val () = PFTWriter.const out id (Thy ^ "$" ^ Name) ty_id
        (* decr type AFTER CONST command is written *)
        val () = decr_ty typ
      in id end
    | Bv n => (case Subst.exp_rel(env, n) of
                 (0, SOME tm_id) => tm_id
               | _ => raise Fail ("emit_term: unresolved Bv " ^
                                   Int.toString n))
    | Comb (t1, t2) => let
        val id1 = emit_term_sub env t1
        (* Protect t1 before emitting t2, which may trigger nested
           chains that decrement t1 *)
        val () = if is_closed t1 then protect t1 else ()
        val id2 = emit_term_sub env t2
        val id = #alloc tm_ids ()
        val () = PFTWriter.comb out id id1 id2
        val () = if is_closed t1 then (unprotect t1; decr_tm t1) else ()
        val () = if is_closed t2 then decr_tm t2 else ()
      in id end
    | Abs (t1, t2) => let
        val bvar_id = emit_binder env t1
        (* Protect t1 before emitting body, which may trigger nested
           chains that decrement t1 *)
        val () = if is_closed t1 then protect t1 else ()
        val body_id = emit_term_sub (Subst.cons(env, bvar_id)) t2
        val id = #alloc tm_ids ()
        val () = PFTWriter.abs out id bvar_id body_id
        val () = if is_closed t1 then (unprotect t1; decr_tm t1) else ()
        val () = if is_closed t2 then decr_tm t2 else ()
      in id end
    | Clos (sbp, tmp) => let
        val env' = Subst.comp (fn (_,s) => s) (env, emit_subs env sbp)
        (* No decrements here: Clos is not cached (to avoid PFT ID
           aliasing with body), so subs terms and body decrements would
           over-fire on repeated evaluation. Their walk incrs become
           minor leaks. *)
      in emit_term_sub env' tmp end

  and emit_binder env (tm_ptr : Term.term ptr) : int =
    case shTerm heap tm_ptr of
      Fv (s, typ) => let
        val ty_id = emit_type typ
        val id = #alloc tm_ids ()
        val () = PFTWriter.var out id s ty_id
        (* No decr_ty here: emit_binder is not cached (creates fresh
           VARs for alpha-renaming), so N Abs nodes sharing a binder
           would call decr_ty N times vs the walk's single incr.
           The type decr is handled by emit_term_core Fv if the Fv is
           also used as a free variable; otherwise it's a minor leak. *)
      in id end
    | _ => emit_term_sub env tm_ptr

  (* emit_subs: emit substitution terms, returning PFT-level subs.
     Does NOT decrement — Clos caller handles via decr_subs_terms. *)
  and emit_subs env (sbp : Term.term Subst.subs ptr) : int Subst.subs =
    case shSubs heap sbp of
      Id => Subst.id
    | Cons (sbp', tmp) =>
        Subst.cons(emit_subs env sbp', emit_term_sub env tmp)
    | Lift (n, sbp') => Subst.lift(n, emit_subs env sbp')
    | Shift (n, sbp') => Subst.shift(n, emit_subs env sbp')

  (* --- check_def ------------------------------------------------------- *)

  and check_def map Thy nm =
    if Thy = thyname then case peek(map, nm) of
      SOME thps => List.app (ignore o emit_thm) thps
    | _ => ()
    else ()

  (* --- Theorem emission ------------------------------------------------ *)

  and emit_thm (thm_ptr : Thm.thm ptr) : int =
    if not (isPtr thm_ptr) then raise Fail "emit_thm: not a ptr"
    else let val k = ptr thm_ptr
             val cached = Array.sub(th_map, k)
    in if cached >= 0 then cached
       else let
         val (hyp_ptr, concl_ptr, proof_ptr) = shThm heap thm_ptr
         val (i, args_ptrs) = shVariant heap proof_ptr
         (* Pending decrements: collected during child emission,
            flushed AFTER the parent PFT command is written.

            Each captured child is protected (protect_count bumped) to
            prevent nested emit_thm chains from evicting it. Unprotect
            and decrement happen in flush, after the command is written. *)
         val pend_ty : Type.hol_type ptr list ref = ref []
         val pend_tm : Term.term ptr list ref = ref []
         val pend_th : Thm.thm ptr list ref = ref []
         fun flush () = (
           List.app unprotect (!pend_ty);
           List.app unprotect (!pend_tm);
           List.app unprotect (!pend_th);
           List.app decr_ty (!pend_ty);
           List.app decr_tm (!pend_tm);
           List.app decr_th (!pend_th))
         fun tm n = let val p : Term.term ptr = castPtr (el n args_ptrs)
                        val r = emit_term p
                        val () = protect p
                    in pend_tm := p :: !pend_tm; r end
         fun th n = let val p : Thm.thm ptr = castPtr (el n args_ptrs)
                        val r = emit_thm p
                        val () = protect p
                    in pend_th := p :: !pend_th; r end
         fun ty n = let val p : Type.hol_type ptr = castPtr (el n args_ptrs)
                        val r = emit_type p
                        val () = protect p
                    in pend_ty := p :: !pend_ty; r end
         (* Helpers for inline list/option processing *)
         fun emit_type_pend q = let
           val p : Type.hol_type ptr = castPtr q
           val r = emit_type p
           val () = protect p
         in pend_ty := p :: !pend_ty; r end
         fun emit_term_pend q = let
           val p : Term.term ptr = castPtr q
           val r = emit_term p
           val () = protect p
         in pend_tm := p :: !pend_tm; r end
         fun emit_thm_pend q = let
           val p : Thm.thm ptr = castPtr q
           val r = emit_thm p
           val () = protect p
         in pend_th := p :: !pend_th; r end
         val id = #alloc th_ids ()
         val () = Array.update(th_map, k, id)
         val () = case i of
             0  => (* ABS *)        PFTWriter.HOL4.abs_thm out id (tm 1) (th 2)
           | 1  => (* ALPHA *)      PFTWriter.HOL4.alpha out id (tm 1) (tm 2)
           | 2  => (* AP_TERM *)    PFTWriter.HOL4.ap_term out id (tm 1) (th 2)
           | 3  => (* AP_THM *)     PFTWriter.HOL4.ap_thm out id (th 1) (tm 2)
           | 4  => (* ASSUME *)     PFTWriter.HOL4.assume out id (tm 1)
           | 5  => (* Axiom *) let
               val c = emit_term concl_ptr
             in PFTWriter.axiom out id c NONE end
           | 6  => (* BETA_CONV *)  PFTWriter.HOL4.beta_conv out id (tm 1)
           | 7  => (* Beta *)       PFTWriter.HOL4.beta_thm out id (th 1)
           | 8  => (* CCONTR *)     PFTWriter.HOL4.ccontr out id (tm 1) (th 2)
           | 9  => (* CHOOSE *)     PFTWriter.HOL4.choose out id (tm 1) (th 2) (th 3)
           | 10 => (* CONJUNCT1 *)  PFTWriter.HOL4.conjunct1 out id (th 1)
           | 11 => (* CONJUNCT2 *)  PFTWriter.HOL4.conjunct2 out id (th 1)
           | 12 => (* CONJ *)       PFTWriter.HOL4.conj out id (th 1) (th 2)
           | 13 => (* DISCH *)      PFTWriter.HOL4.disch out id (tm 1) (th 2)
           | 14 => (* DISJ1 *)      PFTWriter.HOL4.disj1 out id (th 1) (tm 2)
           | 15 => (* DISJ2 *)      PFTWriter.HOL4.disj2 out id (tm 1) (th 2)
           | 16 => (* DISJ_CASES *) PFTWriter.HOL4.disj_cases out id (th 1) (th 2) (th 3)
           | 17 => (* Def_const_list *) let
               val th1 = th 1
               val ids = list heap get_const_id (castPtr (el 2 args_ptrs))
               val names = List.map (fn (Thy,nm) => Thy ^ "$" ^ nm) ids
               val () = List.app (fn (_,nm) => mark_const nm) ids
             in PFTWriter.HOL4.def_spec out id th1 names end
           | 18 => (* Def_const *) emit_def_const flush id args_ptrs
           | 19 => (* Def_spec *) let
               val th1 = th 1
               val ids = list heap get_const_id (castPtr (el 2 args_ptrs))
               val names = List.map (fn (Thy,nm) => Thy ^ "$" ^ nm) ids
               val () = List.app (fn (_,nm) => mark_const nm) ids
             in PFTWriter.HOL4.def_spec out id th1 names end
           | 20 => (* Def_tyop *) let
               val _ = list heap emit_type_pend (castPtr (el 1 args_ptrs))
               val th2 = th 2
               val (Thy, Tyop) = get_type_id (castPtr (el 3 args_ptrs))
               val () = mark_type Tyop
             in PFTWriter.HOL4.def_tyop out id th2 (Thy ^ "$" ^ Tyop) end
           | 21 => (* Disk *) let
               val dep_thy = str heap (castPtr (el 1 args_ptrs))
               val dep_id = get_thm_id heap (castPtr (el 2 args_ptrs))
               val save_name = disk_save_name dep_thy dep_id
             in PFTWriter.load out id save_name end
           | 22 => (* EQ_IMP_RULE1 *) PFTWriter.HOL4.eq_imp_rule1 out id (th 1)
           | 23 => (* EQ_IMP_RULE2 *) PFTWriter.HOL4.eq_imp_rule2 out id (th 1)
           | 24 => (* EQ_MP *)      PFTWriter.HOL4.eq_mp out id (th 1) (th 2)
           | 25 => (* EXISTS *)     PFTWriter.HOL4.exists out id (tm 1) (tm 2) (th 3)
           | 26 => (* GENL *) let
               val tms = list heap emit_term_pend
                           (castPtr (el 1 args_ptrs))
               val th2 = th 2
             in PFTWriter.HOL4.genl out id th2 tms end
           | 27 => (* GEN_ABS *) let
               val opt = option heap emit_term_pend
                           (castPtr (el 1 args_ptrs))
               val c_id = case opt of SOME c => c
                 | NONE => raise Fail "GEN_ABS: missing constant"
               val tms = list heap emit_term_pend
                           (castPtr (el 2 args_ptrs))
               val th3 = th 3
             in PFTWriter.HOL4.gen_abs out id th3 c_id tms end
           | 28 => (* GEN *)        PFTWriter.HOL4.gen out id (tm 1) (th 2)
           | 29 => (* INST_TYPE *) let
               val pairs = list heap (fn p =>
                 tuple2 heap (emit_type_pend, emit_type_pend) (castPtr p))
                 (castPtr (el 1 args_ptrs))
               val th2 = th 2
             in PFTWriter.HOL4.inst_type out id th2 pairs end
           | 30 => (* INST *) let
               val pairs = list heap (fn p =>
                 tuple2 heap (emit_term_pend, emit_term_pend) (castPtr p))
                 (castPtr (el 1 args_ptrs))
               val th2 = th 2
             in PFTWriter.HOL4.inst out id th2 pairs end
           | 31 => (* MK_COMB *)    PFTWriter.HOL4.mk_comb out id (th 1) (th 2)
           | 32 => (* MP *)         PFTWriter.HOL4.mp out id (th 1) (th 2)
           | 33 => (* Mk_abs *) let
               val th1 = th 1
               (* walk does tm(el 2); we don't use it but must decr *)
               val _ = tm 2
               val th3 = th 3
             in PFTWriter.HOL4.mk_abs_thm out id th1 th3 end
           | 34 => (* Mk_comb *)    PFTWriter.HOL4.mk_comb_thm out id (th 1) (th 2) (th 3)
           | 35 => (* NOT_ELIM *)   PFTWriter.HOL4.not_elim out id (th 1)
           | 36 => (* NOT_INTRO *)  PFTWriter.HOL4.not_intro out id (th 1)
           | 37 => (* REFL *)       PFTWriter.HOL4.refl out id (tm 1)
           | 38 => (* SPEC *)       PFTWriter.HOL4.spec out id (tm 1) (th 2)
           | 39 => (* SUBST *) let
               val pairs = list heap (fn p =>
                 tuple2 heap (emit_term_pend, emit_thm_pend) (castPtr p))
                 (castPtr (el 1 args_ptrs))
               val tm2 = tm 2
               val th3 = th 3
             in PFTWriter.HOL4.subst out id tm2 th3 pairs end
           | 40 => (* SYM *)        PFTWriter.HOL4.sym out id (th 1)
           | 41 => (* Specialize *) PFTWriter.HOL4.specialize out id (tm 1) (th 2)
           | 42 => (* TRANS *)      PFTWriter.HOL4.trans out id (th 1) (th 2)
           | 43 => (* compute *)    emit_compute flush id args_ptrs
           | 44 => (* deductAntisym *) PFTWriter.HOL4.deductAntisym out id (th 1) (th 2)
           | 45 => (* deleted *)    raise Fail "emit_thm: deleted"
           | n => raise Fail ("emit_thm: unknown rule " ^ Int.toString n)
         (* Flush all pending decrements now that the command is written *)
         val () = flush ()
       in id end
    end

  (* Def_const: synthesize ASSUME(v = rhs) then DEF_SPEC.
     flush_parent flushes the parent emit_thm's pending decrements;
     called after DEF_SPEC is written (which is the parent command). *)
  and emit_def_const flush_parent thm_id args_ptrs = let
    val rhs_p = el 1 args_ptrs
    val rhs_id = emit_term (castPtr rhs_p)
    val const_ptr : Term.term ptr = castPtr (el 2 args_ptrs)
    val (Thy, Name) = get_const_id const_ptr
    val ty_ptr = case shTerm heap const_ptr of
        Const (_, tp) => tp
      | _ => raise Fail "Def_const: expected Const"
    val rhs_ty_id = emit_type ty_ptr
    (* Build equality type: ty -> (ty -> bool) *)
    val bool_ty_id = emit_tyop_by_name "bool" "bool" []
    val fun_ty1_id = emit_tyop_by_name "min" "fun" [rhs_ty_id, bool_ty_id]
    val eq_ty_id = emit_tyop_by_name "min" "fun" [rhs_ty_id, fun_ty1_id]
    (* VAR for the new constant *)
    val var_id = #alloc tm_ids ()
    val () = PFTWriter.var out var_id Name rhs_ty_id
    (* CONST for = *)
    val eq_id = #alloc tm_ids ()
    val () = PFTWriter.const out eq_id "min$=" eq_ty_id
    (* (= v) *)
    val eq_var_id = #alloc tm_ids ()
    val () = PFTWriter.comb out eq_var_id eq_id var_id
    (* (= v) rhs *)
    val eq_tm_id = #alloc tm_ids ()
    val () = PFTWriter.comb out eq_tm_id eq_var_id rhs_id
    (* ASSUME (v = rhs) *)
    val assume_id = #alloc th_ids ()
    val () = PFTWriter.HOL4.assume out assume_id eq_tm_id
    (* DEF_SPEC *)
    val () = mark_const Name
    val () = PFTWriter.HOL4.def_spec out thm_id assume_id
               [Thy ^ "$" ^ Name]
    (* Now safe to flush parent's pending decrements (which includes
       the walk's tm(el 1) incr for rhs_p) *)
    val () = flush_parent ()
  in () end

  (* compute: emit COMPUTE_INIT then COMPUTE.
     flush_parent flushes the parent emit_thm's pending decrements. *)
  and emit_compute flush_parent thm_id args_ptrs = let
    val (compute_args_ptr, ths_ptr) =
      tuple2 heap (I, I) (castPtr (el 1 args_ptrs))
    val th_id_list = list heap (fn p => emit_thm (castPtr p)) ths_ptr
    val tm_p = el 2 args_ptrs
    val tm_id = emit_term (castPtr tm_p)
    val (num_type_ptr, (eqns_ptr, (cval_type_ptr, cterms_ptr))) =
      tuple4 heap (I, I, I, I) (castPtr compute_args_ptr)
    val num_ty = emit_type (castPtr num_type_ptr)
    val cval_ty = emit_type (castPtr cval_type_ptr)
    val char_eqns = list heap (fn p =>
      tuple2 heap (str heap,
        fn q => emit_thm (castPtr q)) (castPtr p)) eqns_ptr
    val cval_terms = list heap (fn p =>
      tuple2 heap (str heap,
        fn q => emit_term (castPtr q)) (castPtr p)) cterms_ptr
    val ci_id = #alloc ci_ids ()
    val () = PFTWriter.HOL4.compute_init out ci_id num_ty cval_ty
               char_eqns cval_terms
    val () = PFTWriter.HOL4.compute out thm_id ci_id tm_id th_id_list
    (* Now safe to decrement everything *)
    val () = flush_parent ()
    val () = appList heap (fn p => decr_th (castPtr p)) (castPtr ths_ptr)
    val () = decr_tm (castPtr tm_p)
    val () = decr_ty (castPtr num_type_ptr)
    val () = decr_ty (castPtr cval_type_ptr)
    val () = appList heap (fn p =>
      ignore (tuple2 heap (K(), fn q => decr_th (castPtr q)) (castPtr p)))
      eqns_ptr
    val () = appList heap (fn p =>
      ignore (tuple2 heap (K(), fn q => decr_tm (castPtr q)) (castPtr p)))
      cterms_ptr
  in () end

  (* --- Process exports ------------------------------------------------- *)

  (* Named exports: walk pre_named does incr(castPtr thp); decr after.
     SAVE before decr so the PFT ID is still valid. *)
  val () = appList heap (fn p => let
    val (nm, (thp, _)) = tuple3 heap (str heap, I, I) p
    val _ = emit_thm (castPtr thp)
    val pft_id = Array.sub(th_map, ptr (castPtr thp : Thm.thm ptr))
    val () = PFTWriter.save out (thyname ^ "$" ^ nm) pft_id
  in decr_th thp end) all_thms

  (* Anonymous exports: walk pre_anon does incr(castPtr p); decr after. *)
  val anon_idx = ref 0
  val () = appList heap (fn p => let
    val i = !anon_idx
    val () = anon_idx := i + 1
    val _ = emit_thm (castPtr p)
    val pft_id = Array.sub(th_map, ptr (castPtr p : Thm.thm ptr))
    val () = PFTWriter.save out (thyname ^ "#" ^ Int.toString i) pft_id
  in decr_th (castPtr p) end) anon_thms

  (* --- Ensure all theory constants/types are introduced ----------------- *)
  (* Mirrors ProofTraceReplay.ensure_const / ensure_type *)

  val () = appList heap (fn p => let
    val (Name, ty_ptr) = tuple2 heap (str heap, I) p
    val () = check_def tm_defs thyname Name
  in if is_const_done Name then ()
     else let
       val ty_id = emit_type (castPtr ty_ptr)
       val () = mark_const Name
     in PFTWriter.new_const out (thyname ^ "$" ^ Name) ty_id end
  end) constants

  val () = appList heap (fn p => let
    val (Tyop, arity) = tuple2 heap (str heap, int) p
    val () = check_def ty_defs thyname Tyop
  in if is_type_done Tyop then ()
     else (mark_type Tyop;
           PFTWriter.new_type out (thyname ^ "$" ^ Tyop) arity)
  end) types

in
  PFTWriter.closeOut out
    {n_ty = #peak ty_ids (),
     n_tm = #peak tm_ids (),
     n_th = #peak th_ids (),
     n_ci = #peak ci_ids ()}
end

end
