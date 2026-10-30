structure ProofTraceWalk :> ProofTraceWalk = struct

open Lib ProofTraceParser

fun update_at (tab, k, f) =
    Symtab.update (k, f (Symtab.lookup tab k)) tab

fun walk {heap, thyname, const_name, type_name, named_thms, anon_thms,
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
  val cid = cache_id (fn tm_ptr =>
    case shTerm heap tm_ptr of Const (idp,_) => const_name idp
    | _ => raise Fail "get_const_id")
  val tid = cache_id (fn ty_ptr =>
    case shType heap ty_ptr of Tyapp (idp,_) => type_name idp
    | _ => raise Fail "get_type_id")

  (* Implicit HOL rules can retain a retired logical role only in an
     intermediate sequent, without any explicit proof argument naming it. *)
  val check_symbols = let
    val checked = BoolArray.array(heapSize heap, false)
    fun visit p f =
      if not (isPtr p) orelse BoolArray.sub(checked, ptr p) then () else
        (BoolArray.update(checked, ptr p, true); f p)
    fun typ p = visit p (fn p => case shType heap p of
        Tyv _ => ()
      | Tyapp (id,args) =>
          (ignore (type_name id); appList heap typ args))
    fun tm p = visit p (fn p => case shTerm heap p of
        Const (id,ty) => (ignore (const_name id); typ ty)
      | Fv (_,ty) => typ ty
      | Comb (a,b) => (tm a; tm b)
      | Abs (a,b) => (tm a; tm b)
      | Clos (s,t) => (subs s; tm t)
      | Bv _ => ())
    and subs p = case shSubs heap p of
        Id => ()
      | Cons (s,t) => (subs s; tm t)
      | Lift (_,s) => subs s
      | Shift (_,s) => subs s
  in tm end

  fun role_error () =
    raise Fail "ProofTraceWalk: unsupported implicit logical-role shape"

  datatype role_term = Raw of term ptr
                     | Delayed of role_term Subst.subs * role_term
  datatype role_view = RConst of ident ptr
                     | RComb of role_term * role_term
                     | RAbs of role_term | RBv of int | ROther
  fun role_subs p = case shSubs heap p of
      Id => Subst.id
    | Cons (s,t) => Subst.cons (role_subs s, Raw t)
    | Lift (n,s) => Subst.lift (n, role_subs s)
    | Shift (n,s) => Subst.shift (n, role_subs s)
  fun role_view (Raw p) = (case shTerm heap p of
        Const (id,_) => RConst id
      | Comb (f,x) => RComb (Raw f, Raw x)
      | Abs (_,b) => RAbs (Raw b)
      | Bv n => RBv n
      | Clos (s,t) => role_view (Delayed (role_subs s, Raw t))
      | Fv _ => ROther)
    | role_view (Delayed (s,t)) = (case role_view t of
        RBv n => (case Subst.exp_rel (s,n) of
            (n,NONE) => RBv n
          | (0,SOME t) => role_view t
          | (n,SOME t) => role_view (Delayed (Subst.shift (n,Subst.id),t)))
      | RComb (f,x) => RComb (Delayed (s,f), Delayed (s,x))
      | RAbs b => RAbs (Delayed (Subst.lift (1,s),b))
      | atom => atom)
  fun head t = case role_view t of
      RComb (f,_) => head f
    | RConst id => const_name id
    | _ => role_error ()
  fun require_role name p =
    let val (thy,nm) = head p
    in if (thy,nm) = ("bool",name) then () else raise Fail
         ("ProofTraceWalk: noncanonical logical role " ^ thy ^ "$" ^ nm ^
          "; expected bool$" ^ name ^ "; unsupported")
    end
  fun rand t = case role_view t of
      RComb (_,a) => a | _ => role_error ()
  fun body t = case role_view t of
      RAbs b => b | _ => role_error ()
  fun conclusion p = Raw (#2 (shThm heap p))
  fun check_roles thm_ptr proof concl = let val concl = Raw concl in
    case proof of
      CONJ_prf _ => require_role "/\\" concl
    | CONJUNCT1_prf a => require_role "/\\" (conclusion a)
    | CONJUNCT2_prf a => require_role "/\\" (conclusion a)
    | DISJ1_prf _ => require_role "\\/" concl
    | DISJ2_prf _ => require_role "\\/" concl
    | DISJ_CASES_prf (a,_,_) => require_role "\\/" (conclusion a)
    | GEN_prf _ => require_role "!" concl
    | GENL_prf (vs,_) =>
        if null (list heap I vs) then () else require_role "!" concl
    | SPEC_prf (_,a) => require_role "!" (conclusion a)
    | Specialize_prf (_,a) => require_role "!" (conclusion a)
    | EXISTS_prf _ => require_role "?" concl
    | CHOOSE_prf (_,a,_) => require_role "?" (conclusion a)
    | Def_spec_prf (a,cs) =>
        if null (list heap I cs) then ()
        else require_role "?" (conclusion a)
    | Def_tyop_prf (_,a,_) =>
        (require_role "?" (conclusion a); require_role "?" concl;
         require_role "TYPE_DEFINITION" (body (rand concl)))
    | NOT_INTRO_prf a =>
        (require_role "~" concl; require_role "F" (rand (conclusion a)))
    | NOT_ELIM_prf a =>
        (require_role "~" (conclusion a); require_role "F" (rand concl))
    | CCONTR_prf (_,a) => let
        val (source_hyps,_,_) = shThm heap a
        val (target_hyps,_,_) = shThm heap thm_ptr
        val retained = ref []
        val () = appSet heap (fn p => retained := p :: !retained) target_hyps
        fun removed p = if List.exists (fn q => ptr p = ptr q) (!retained) then ()
                        else require_role "~" (Raw p)
      in require_role "F" (conclusion a); appSet heap removed source_hyps end
    | _ => ()
  end

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
  val tm_defs : thm ptr list Symtab.table ref = ref Symtab.empty
  val ty_defs : thm ptr list Symtab.table ref = ref Symtab.empty
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
      val (hyps, concl, proof_ptr) = shThm heap thm_ptr
      val () = check_symbols concl
      val () = appSet heap check_symbols hyps
      val proof = shProof heap proof_ptr
      val () = check_roles thm_ptr proof concl
      fun check_thy defthy =
        if defthy = thyname then () else raise Fail
          ("ProofTraceWalk: foreign definition from " ^ defthy ^ " unsupported")
      fun add_gen tab nm =
        (on_def_thm thm_ptr;
         tab := update_at (!tab, nm, fn NONE => [thm_ptr]
                                      | SOME l => thm_ptr :: l))
      fun add_const x = add_gen tm_defs x
      fun add_type x = add_gen ty_defs x
      fun add_def_const p = let
        val (thy,nm) = cid p
        val () = check_thy thy
      in add_const nm end
    in case proof of
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
          val ids = list heap cid b
        in List.app (fn (thy,nm) => (check_thy thy; add_const nm)) ids
        end
      | Def_const_prf (a, b) => (tm a; add_def_const b)
      | Def_spec_prf (a, b) => let
          val () = th a
          val ids = list heap cid b
        in List.app (fn (thy,nm) => (check_thy thy; add_const nm)) ids
        end
      | Def_tyop_prf (a, b, c) => let
          val () = appList heap ty a
          val () = th b
          val (thy,tyop) = tid c
          val () = check_thy thy
        in add_type tyop end
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
      | Mark_prf (_, a) => th a
      | Exported_prf _ => ()
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
    get_const_id = cid,
    get_type_id = tid }
end

end
