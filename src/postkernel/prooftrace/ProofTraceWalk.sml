structure ProofTraceWalk :> ProofTraceWalk = struct

open Lib Redblackmap ProofTraceParser

fun walk {heap, thyname, named_thms, anon_thms,
          incr, on_def_thm} = let

  (* ID cache for constant/type operator identifiers *)
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

  (* Walk state *)
  val tm_defs : (string, thm ptr list) dict ref = ref (mkDict String.compare)
  val ty_defs : (string, thm ptr list) dict ref = ref (mkDict String.compare)
  val seen = BoolArray.array(heapSize heap, false)

  fun first_seen p =
    if not (isPtr p) then false
    else if BoolArray.sub(seen, ptr p) then false
    else (BoolArray.update(seen, ptr p, true); true)

  fun walk_type (ty_ptr: hol_type ptr) =
    if not (first_seen ty_ptr) then () else
    case shType heap ty_ptr of
      Tyv _ => ()
    | Tyapp (_, args_ptr) =>
        appList heap (fn p => (incr p; walk_type (castPtr p))) (castPtr args_ptr)

  fun walk_term (tm_ptr: term ptr) =
    if is_closed tm_ptr
    then (incr (castPtr tm_ptr);
          if first_seen tm_ptr then walk_term_inner tm_ptr else ())
    else walk_term_inner tm_ptr
  and walk_term_inner tm_ptr =
    if not (isPtr tm_ptr) then () else
    case shTerm heap tm_ptr of
      Abs (t1, t2) => (walk_term t1; walk_term t2)
    | Comb (t1, t2) => (walk_term t1; walk_term t2)
    | Const (_, typ) => (incr (castPtr typ); walk_type typ)
    | Fv (_, typ) => (incr (castPtr typ); walk_type typ)
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
      fun tm (p: unit ptr) = (incr p;
        if first_seen (castPtr p) then walk_term_inner (castPtr p)
        else ())
      fun th (p: unit ptr) = (incr p; walk_thm (castPtr p))
      fun ty (p: unit ptr) = (incr p; walk_type (castPtr p))
      fun add_thm_ptr nm prev =
            (on_def_thm thm_ptr;
             case prev of NONE => [thm_ptr]
               | SOME ls => (print("WARNING: multiple defs for "^nm^"\n");
                             thm_ptr::ls))
      fun check_thy defthy =
        if defthy = thyname then () else raise Fail "add_def thy"
      fun add_const nm = tm_defs := update(!tm_defs, nm, add_thm_ptr nm)
      fun add_def_const p = let
        val (thy,nm) = get_const_id (castPtr p)
        val () = check_thy thy
      in add_const nm end
    in case i of
        0  => (* ABS *)        (tm(el 1 args_ptrs); th(el 2 args_ptrs))
      | 1  => (* ALPHA *)      (tm(el 1 args_ptrs); tm(el 2 args_ptrs))
      | 2  => (* AP_TERM *)    (tm(el 1 args_ptrs); th(el 2 args_ptrs))
      | 3  => (* AP_THM *)     (th(el 1 args_ptrs); tm(el 2 args_ptrs))
      | 4  => (* ASSUME *)     tm(el 1 args_ptrs)
      | 5  => (* Axiom *)      ()
      | 6  => (* BETA_CONV *)  tm(el 1 args_ptrs)
      | 7  => (* Beta *)       th(el 1 args_ptrs)
      | 8  => (* CCONTR *)     (tm(el 1 args_ptrs); th(el 2 args_ptrs))
      | 9  => (* CHOOSE *)     (tm(el 1 args_ptrs); th(el 2 args_ptrs); th(el 3 args_ptrs))
      | 10 => (* CONJUNCT1 *)  th(el 1 args_ptrs)
      | 11 => (* CONJUNCT2 *)  th(el 1 args_ptrs)
      | 12 => (* CONJ *)       (th(el 1 args_ptrs); th(el 2 args_ptrs))
      | 13 => (* DISCH *)      (tm(el 1 args_ptrs); th(el 2 args_ptrs))
      | 14 => (* DISJ1 *)      (th(el 1 args_ptrs); tm(el 2 args_ptrs))
      | 15 => (* DISJ2 *)      (tm(el 1 args_ptrs); th(el 2 args_ptrs))
      | 16 => (* DISJ_CASES *) (th(el 1 args_ptrs); th(el 2 args_ptrs); th(el 3 args_ptrs))
      | 17 => (* Def_const_list *) let
          val () = th(el 1 args_ptrs)
          val ids = list heap get_const_id (castPtr (el 2 args_ptrs))
        in List.app (fn (thy,nm) => (check_thy thy; add_const nm)) ids end
      | 18 => (* Def_const *) (tm(el 1 args_ptrs); add_def_const (el 2 args_ptrs))
      | 19 => (* Def_spec *) let
          val () = th(el 1 args_ptrs)
          val ids = list heap get_const_id (castPtr (el 2 args_ptrs))
        in List.app (fn (thy,nm) => (check_thy thy; add_const nm)) ids end
      | 20 => (* Def_tyop *) let
          val () = appList heap ty (castPtr (el 1 args_ptrs))
          val () = th(el 2 args_ptrs)
          val (thy,tyop) = get_type_id (castPtr (el 3 args_ptrs))
          val () = check_thy thy
        in ty_defs := update(!ty_defs, tyop, add_thm_ptr tyop) end
      | 21 => (* Disk *)       ()
      | 22 => (* EQ_IMP_RULE1 *) th(el 1 args_ptrs)
      | 23 => (* EQ_IMP_RULE2 *) th(el 1 args_ptrs)
      | 24 => (* EQ_MP *)      (th(el 1 args_ptrs); th(el 2 args_ptrs))
      | 25 => (* EXISTS *)     (tm(el 1 args_ptrs); tm(el 2 args_ptrs); th(el 3 args_ptrs))
      | 26 => (* GENL *)       (appList heap tm (castPtr (el 1 args_ptrs)); th(el 2 args_ptrs))
      | 27 => (* GEN_ABS *)    (ignore (option heap tm (castPtr (el 1 args_ptrs)));
                                 appList heap tm (castPtr (el 2 args_ptrs));
                                 th(el 3 args_ptrs))
      | 28 => (* GEN *)        (tm(el 1 args_ptrs); th(el 2 args_ptrs))
      | 29 => (* INST_TYPE *)  (appList heap (fn p =>
                                  ignore (tuple2 heap (ty,ty) (castPtr p))
                                  ) (castPtr (el 1 args_ptrs));
                                 th(el 2 args_ptrs))
      | 30 => (* INST *)       (appList heap (fn p =>
                                  ignore (tuple2 heap (tm,tm) (castPtr p))
                                  ) (castPtr (el 1 args_ptrs));
                                 th(el 2 args_ptrs))
      | 31 => (* MK_COMB *)    (th(el 1 args_ptrs); th(el 2 args_ptrs))
      | 32 => (* MP *)         (th(el 1 args_ptrs); th(el 2 args_ptrs))
      | 33 => (* Mk_abs *)     (th(el 1 args_ptrs); tm(el 2 args_ptrs); th(el 3 args_ptrs))
      | 34 => (* Mk_comb *)    (th(el 1 args_ptrs); th(el 2 args_ptrs); th(el 3 args_ptrs))
      | 35 => (* NOT_ELIM *)   th(el 1 args_ptrs)
      | 36 => (* NOT_INTRO *)  th(el 1 args_ptrs)
      | 37 => (* REFL *)       tm(el 1 args_ptrs)
      | 38 => (* SPEC *)       (tm(el 1 args_ptrs); th(el 2 args_ptrs))
      | 39 => (* SUBST *)      (appList heap (fn p =>
                                  ignore (tuple2 heap (tm,th) (castPtr p))
                                  ) (castPtr (el 1 args_ptrs));
                                 tm(el 2 args_ptrs); th(el 3 args_ptrs))
      | 40 => (* SYM *)        th(el 1 args_ptrs)
      | 41 => (* Specialize *) (tm(el 1 args_ptrs); th(el 2 args_ptrs))
      | 42 => (* TRANS *)      (th(el 1 args_ptrs); th(el 2 args_ptrs))
      | 43 => (* compute *) let
          val (args_p, extra_p) = tuple2 heap (I, I) (castPtr (el 1 args_ptrs))
          val (nty_p, (ceq_p, (cvty_p, cvtm_p))) =
            tuple4 heap (I, I, I, I) (castPtr args_p)
          val () = ty nty_p
          val () = appList heap (fn p =>
            ignore (tuple2 heap (K(), th) (castPtr p))) (castPtr ceq_p)
          val () = ty cvty_p
          val () = appList heap (fn p =>
            ignore (tuple2 heap (K(), tm) (castPtr p))) (castPtr cvtm_p)
          val () = appList heap th (castPtr extra_p)
        in tm(el 2 args_ptrs) end
      | 44 => (* deductAntisym *) (th(el 1 args_ptrs); th(el 2 args_ptrs))
      | 45 => (* deleted *)    ()
      | 46 => th(el 1 args_ptrs)
      | n => raise Fail ("walk_thm: unknown rule " ^ Int.toString n)
    end

  fun pre_named p = let
    val (_, (thp, _)) = tuple3 heap (I, I, I) p
  in incr (castPtr thp); walk_thm thp end
  fun pre_anon p = (incr (castPtr p); walk_thm p)

  val () = appList heap pre_named named_thms
  val () = appList heap pre_anon anon_thms

  (* Convert closedness to BoolArray *)
  val is_closed_bits = BoolArray.tabulate(heapSize heap,
    fn i => Array.sub(closedness, i) = ~1)
  fun is_closed tm_ptr = isPtr tm_ptr andalso
    BoolArray.sub(is_closed_bits, ptr tm_ptr)

in
  { tm_defs = !tm_defs,
    ty_defs = !ty_defs,
    is_closed = is_closed,
    get_const_id = get_const_id,
    get_type_id = get_type_id }
end

end
