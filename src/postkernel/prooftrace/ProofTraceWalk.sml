structure ProofTraceWalk :> ProofTraceWalk = struct

open Lib Redblackmap ProofTraceParser

fun walk {heap, thyname, named_thms, anon_thms,
          incr, on_def_thm, on_fv} = let

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
     ~2 = unvisited. *)
  val closedness = Array.array(heapSize heap, ~2 : int)
  fun sub_closedness (sub_ptr, b) =
    if b < 0 then ~1
    else case shSubs heap sub_ptr of
      Id => b
    | Cons (sub', tm_ptr) => let
        val tm_cl = compute_closedness tm_ptr
      in if b = 0 then tm_cl
         else Int.max(tm_cl, sub_closedness(sub', b - 1))
      end
    | Shift (k, sub') => let
        val inner = sub_closedness(sub', b)
      in if inner < 0 then ~1 else inner + k end
    | Lift (k, sub') =>
        if b < k then b
        else let
          val low = k - 1
          val inner = sub_closedness(sub', b - k)
          val high = if inner < 0 then ~1 else inner + k
        in Int.max(low, high) end
  and compute_closedness tm_ptr =
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
        | Clos (sub_ptr, body_ptr) =>
            sub_closedness(sub_ptr, compute_closedness body_ptr)
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
    | Tyapp (_, args_ptr) => appList heap ty args_ptr
  and ty p = (incr (castPtr p); walk_type p)

  fun walk_term (tm_ptr: term ptr) =
    if is_closed tm_ptr then tm tm_ptr else walk_term_inner tm_ptr
  and tm p = (incr (castPtr p); if first_seen p then walk_term_inner p else ())
  and walk_term_inner tm_ptr =
    if not (isPtr tm_ptr) then () else
    case shTerm heap tm_ptr of
      Abs (t1, t2) => (walk_term t1; walk_term t2)
    | Comb (t1, t2) => (walk_term t1; walk_term t2)
    | Const (_, typ) => ty typ
    | Fv (s, typ) => (on_fv s; ty typ)
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
      fun add_thm_ptr nm prev =
            (on_def_thm thm_ptr;
             case prev of NONE => [thm_ptr]
               | SOME ls => (print("WARNING: multiple defs for "^nm^"\n");
                             thm_ptr::ls))
      fun check_thy defthy =
        if defthy = thyname then () else raise Fail "add_def thy"
      fun add_const nm = tm_defs := update(!tm_defs, nm, add_thm_ptr nm)
      fun add_def_const p = let
        val (thy,nm) = get_const_id p
        val () = check_thy thy
      in add_const nm end
    in case shProof heap proof_ptr of
        ABS_prf (a, b) => (tm a; th b)
      | ALPHA_prf (a, b) => (tm a; tm b)
      | AP_TERM_prf (a, b) => (tm a; th b)
      | AP_THM_prf (a, b) => (th a; tm b)
      | ASSUME_prf a => tm a
      | Axiom_prf => ()
      | BETA_CONV_prf a => tm a
      | Beta_prf a => th a
      | CCONTR_prf (a, b) => (tm a; th b)
      | CHOOSE_prf (a, b, c) => (tm a; th b; th c)
      | CONJUNCT1_prf a => th a
      | CONJUNCT2_prf a => th a
      | CONJ_prf (a, b) => (th a; th b)
      | DISCH_prf (a, b) => (tm a; th b)
      | DISJ1_prf (a, b) => (th a; tm b)
      | DISJ2_prf (a, b) => (tm a; th b)
      | DISJ_CASES_prf (a, b, c) => (th a; th b; th c)
      | Def_const_list_prf (a, b) => let
          val () = th a
          val ids = list heap get_const_id b
        in List.app (fn (thy,nm) => (check_thy thy; add_const nm)) ids end
      | Def_const_prf (a, b) => (tm a; add_def_const b)
      | Def_spec_prf (a, b) => let
          val () = th a
          val ids = list heap get_const_id b
        in List.app (fn (thy,nm) => (check_thy thy; add_const nm)) ids end
      | Def_tyop_prf (a, b, c) => let
          val () = appList heap ty a
          val () = th b
          val (thy,tyop) = get_type_id c
          val () = check_thy thy
        in ty_defs := update(!ty_defs, tyop, add_thm_ptr tyop) end
      | Disk_prf _ => ()
      | EQ_IMP_RULE1_prf a => th a
      | EQ_IMP_RULE2_prf a => th a
      | EQ_MP_prf (a, b) => (th a; th b)
      | EXISTS_prf (a, b, c) => (tm a; tm b; th c)
      | GENL_prf (a, b) => (appList heap tm a; th b)
      | GEN_ABS_prf (a, b, c) => (option heap tm a; appList heap tm b; th c)
      | GEN_prf (a, b) => (tm a; th b)
      | INST_TYPE_prf (a, b) =>  (appList heap (tuple2 heap (ty,ty)) a; th b)
      | INST_prf (a, b) => (appList heap (tuple2 heap (tm,tm)) a; th b)
      | MK_COMB_prf (a, b) => (th a; th b)
      | MP_prf (a, b) => (th a; th b)
      | Mk_abs_prf (a, b, c) => (th a; tm b; th c)
      | Mk_comb_prf (a, b, c) => (th a; th b; th c)
      | NOT_ELIM_prf a => th a
      | NOT_INTRO_prf a => th a
      | REFL_prf a => tm a
      | SPEC_prf (a, b) => (tm a; th b)
      | SUBST_prf (a, b, c) => (appList heap (tuple2 heap (tm,th)) a; tm b; th c)
      | SYM_prf a => th a
      | Specialize_prf (a, b) => (tm a; th b)
      | TRANS_prf (a, b) => (th a; th b)
      | compute_prf (a, b) => let
          val (args_p, extra_p) = tuple2 heap (I, I) a
          val {cval_terms, cval_type, num_type, char_eqns} = shComputeArgs heap args_p
          val () = ty num_type
          val () = appList heap (tuple2 heap (K(), th)) char_eqns
          val () = ty cval_type
          val () = appList heap (tuple2 heap (K(), tm)) cval_terms
          val () = appList heap th extra_p
        in tm b end
      | deductAntisym_prf (a, b) => (th a; th b)
      | deleted_prf => ()
      | save_dep_prf a => th a
    end
  and th p = (incr (castPtr p); walk_thm p)

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
