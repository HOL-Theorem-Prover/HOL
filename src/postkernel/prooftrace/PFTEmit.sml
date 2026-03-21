structure PFTEmit :> PFTEmit = struct

open Lib Redblackmap ProofTraceParser

datatype ruleset = HOL4 | Candle

(* ========================================================================= *)
(* Utilities                                                                 *)
(* ========================================================================= *)

fun thyname_of_path path = let
  val file = OS.Path.file path
in
  if String.isSuffix "Theory.tr.gz" file
  then String.substring(file, 0, String.size file - 12)
  else raise Fail ("PFTEmit: expected <thy>Theory.tr.gz, got " ^ file)
end

fun disk_save_name thy (Thm.SavedAnon i) = thy ^ "#" ^ Int.toString i
  | disk_save_name thy (Thm.SavedName s) = thy ^ "$" ^ s

(* ========================================================================= *)
(* Candle name translation                                                   *)
(* ========================================================================= *)

(* Map HOL4 qualified names to Candle names for core types/constants.
   Applied when ruleset = Candle; identity for HOL4. *)
local
  val candle_name_map = [
    ("min$bool", "bool"), ("min$fun", "fun"),
    ("min$=", "="), ("min$==>", "==>"), ("min$@", "@"),
    ("bool$T", "T"), ("bool$F", "F"),
    ("bool$/\\", "/\\"), ("bool$\\/", "\\/"),
    ("bool$~", "~"), ("bool$!", "!"), ("bool$?", "?")
  ]
in
  fun candle_translate_name s =
    case List.find (fn (k,_) => k = s) candle_name_map of
      SOME (_, v) => v
    | NONE => s
end

(* ========================================================================= *)
(* Command buffer                                                            *)
(* ========================================================================= *)

(* Each command records a write closure and its referenced PFT IDs by
   namespace. The DEL insertion pass uses the refs to compute last-use. *)

type cmd_entry = {
  write: PFTWriter.pft_out -> unit,
  ref_ty: int list,
  ref_tm: int list,
  ref_th: int list,
  ref_ci: int list
}

(* Dummy entry for DArray default *)
val dummy_cmd : cmd_entry = {
  write = fn _ => (), ref_ty = [], ref_tm = [], ref_th = [], ref_ci = []
}

(* ========================================================================= *)
(* DEL insertion pass                                                        *)
(* ========================================================================= *)

fun write_with_dels out (cmds: cmd_entry DArray.darray)
      {n_ty, n_tm, n_th, n_ci}
      {def_ty, def_tm, def_th, def_ci} = let
  val num_cmds = DArray.size cmds

  (* last_use arrays: PFT ID -> last command index that references it.
     Initialized from def_idx so unreferenced IDs get DEL'd at their
     definition point. *)
  val last_use_ty = Array.array(n_ty, ~1)
  val last_use_tm = Array.array(n_tm, ~1)
  val last_use_th = Array.array(n_th, ~1)
  val last_use_ci = Array.array(n_ci, ~1)
  val () = Array.appi (fn (id, di) => Array.update(last_use_ty, id, di)) def_ty
  val () = Array.appi (fn (id, di) => Array.update(last_use_tm, id, di)) def_tm
  val () = Array.appi (fn (id, di) => Array.update(last_use_th, id, di)) def_th
  val () = Array.appi (fn (id, di) => Array.update(last_use_ci, id, di)) def_ci

  (* Pass 1: compute last-use from references (only increases values) *)
  fun update arr id i =
    if Array.sub(arr, id) < i then Array.update(arr, id, i) else ()
  fun scan_refs i = if i >= num_cmds then () else let
    val {ref_ty, ref_tm, ref_th, ref_ci, ...} = DArray.sub(cmds, i)
  in
    List.app (fn id => update last_use_ty id i) ref_ty;
    List.app (fn id => update last_use_tm id i) ref_tm;
    List.app (fn id => update last_use_th id i) ref_th;
    List.app (fn id => update last_use_ci id i) ref_ci;
    scan_refs (i + 1)
  end
  val () = scan_refs 0

  (* Pass 2: build dels_at — for each command index, which IDs to DEL *)
  (* Representation: array of (ns * id) lists *)
  val dels_at : (string * int) list array = Array.array(num_cmds, [])
  fun schedule ns last_use_arr =
    Array.appi (fn (id, last) =>
      if last >= 0 andalso last < num_cmds then
        Array.update(dels_at, last,
          (ns, id) :: Array.sub(dels_at, last))
      else ()) last_use_arr
  val () = schedule "ty" last_use_ty
  val () = schedule "tm" last_use_tm
  val () = schedule "th" last_use_th
  val () = schedule "ci" last_use_ci

  (* Range compression: group sorted IDs by namespace, emit ranges *)
  fun emit_del_group _ [] = ()
    | emit_del_group ns (id :: ids) = let
        fun run hi [] = (emit_range ns id hi; [])
          | run hi (next :: rest) =
              if next = hi + 1 then run next rest
              else (emit_range ns id hi; next :: rest)
        val remaining = run id ids
      in emit_del_group ns remaining end
  and emit_range ns lo hi =
    if lo = hi then PFTWriter.del out ns lo
    else PFTWriter.del_range out ns lo hi

  (* Simple merge sort on int lists *)
  fun isort [] = [] | isort [x] = [x:int]
    | isort xs = let
        val n = length xs div 2
        val (l, r) = (List.take(xs, n), List.drop(xs, n))
        fun merge ([], ys) = ys | merge (xs, []) = xs
          | merge (x::xs, y::ys) =
              if x <= y then x :: merge(xs, y::ys)
              else y :: merge(x::xs, ys)
      in merge(isort l, isort r) end

  fun emit_dels_at i = let
    val dels = Array.sub(dels_at, i)
    (* Group by namespace *)
    val ty_dels = List.mapPartial (fn ("ty",id) => SOME id | _ => NONE) dels
    val tm_dels = List.mapPartial (fn ("tm",id) => SOME id | _ => NONE) dels
    val th_dels = List.mapPartial (fn ("th",id) => SOME id | _ => NONE) dels
    val ci_dels = List.mapPartial (fn ("ci",id) => SOME id | _ => NONE) dels
  in
    emit_del_group "ty" (isort ty_dels);
    emit_del_group "tm" (isort tm_dels);
    emit_del_group "th" (isort th_dels);
    emit_del_group "ci" (isort ci_dels)
  end

  (* Pass 3: write commands interleaved with DELs *)
  fun write_cmds i = if i >= num_cmds then () else (
    #write (DArray.sub(cmds, i)) out;
    emit_dels_at i;
    write_cmds (i + 1)
  )
in write_cmds 0 end

(* ========================================================================= *)
(* emit_theory                                                               *)
(* ========================================================================= *)

fun emit_theory {trace, output, binary, ruleset} = let
  val thyname = thyname_of_path trace
  val is_candle = case ruleset of Candle => true | HOL4 => false
  val tr_name = if is_candle then candle_translate_name else (fn s => s)
  val (root_ptr, heap) = parse trace
  val {all_thms, anon_thms, constants, types, ...} = shRoot heap root_ptr

  (* --- Walk pass --------------------------------------------------------- *)

  val {tm_defs, ty_defs, is_closed, get_const_id, get_type_id} =
    ProofTraceWalk.walk
      {heap = heap, thyname = thyname,
       named_thms = all_thms, anon_thms = anon_thms,
       incr = fn _ => (), on_def_thm = fn _ => ()}

  (* --- Emit pass state --------------------------------------------------- *)

  val cmd_buf = DArray.new(65536, dummy_cmd)
  fun cmd_index () = DArray.size cmd_buf

  (* ID counters (no free lists — DELs are inserted in a later pass) *)
  val next_ty = ref 0
  val next_tm = ref 0
  val next_th = ref 0
  val next_ci = ref 0

  (* Definition index: PFT ID i -> command index where ID i was defined.
     Used by the DEL pass to DEL unreferenced IDs at their definition point.
     Stored as PIntMaps (ID -> cmd_index), converted to arrays at the end. *)
  val def_idx_ty : int PIntMap.t ref = ref PIntMap.empty
  val def_idx_tm : int PIntMap.t ref = ref PIntMap.empty
  val def_idx_th : int PIntMap.t ref = ref PIntMap.empty
  val def_idx_ci : int PIntMap.t ref = ref PIntMap.empty

  fun alloc_ty () = let val id = !next_ty in next_ty := id + 1; id end
  fun alloc_tm () = let val id = !next_tm in next_tm := id + 1; id end
  fun alloc_th () = let val id = !next_th in next_th := id + 1; id end
  fun alloc_ci () = let val id = !next_ci in next_ci := id + 1; id end

  (* Record definition index: called when the defining command is emitted *)
  fun def_ty id = def_idx_ty := PIntMap.add id (cmd_index()) (!def_idx_ty)
  fun def_tm id = def_idx_tm := PIntMap.add id (cmd_index()) (!def_idx_tm)
  fun def_th id = def_idx_th := PIntMap.add id (cmd_index()) (!def_idx_th)
  fun def_ci id = def_idx_ci := PIntMap.add id (cmd_index()) (!def_idx_ci)

  fun def_idx_to_array m n =
    Array.tabulate(n, fn i => PIntMap.find i m handle PIntMap.NotFound => ~1)

  (* --- Pointer memos ----------------------------------------------------- *)

  val tm_memo = Array.array(heapSize heap, ~1)
                (* heap ptr -> PFT term ID; hot path, flat array *)
  val ty_memo : int PIntMap.t ref = ref PIntMap.empty
  val th_memo : int PIntMap.t ref = ref PIntMap.empty
  val ci_memo : int PIntMap.t ref = ref PIntMap.empty

  fun ty_memo_get k = PIntMap.find k (!ty_memo)
                      handle PIntMap.NotFound => ~1
  fun ty_memo_set k v = ty_memo := PIntMap.add k v (!ty_memo)
  fun th_memo_get k = PIntMap.find k (!th_memo)
                      handle PIntMap.NotFound => ~1
  fun th_memo_set k v = th_memo := PIntMap.add k v (!th_memo)
  fun ci_memo_get k = PIntMap.find k (!ci_memo)
                      handle PIntMap.NotFound => ~1
  fun ci_memo_set k v = ci_memo := PIntMap.add k v (!ci_memo)

  (* --- Structural hash-cons tables -------------------------------------- *)

  (* Types: small, use Redblackmap *)
  datatype ty_key = TyVarK of string | TyOpK of string * int list
  fun ty_key_cmp (TyVarK a, TyVarK b) = String.compare(a, b)
    | ty_key_cmp (TyVarK _, TyOpK _) = LESS
    | ty_key_cmp (TyOpK _, TyVarK _) = GREATER
    | ty_key_cmp (TyOpK(a1,a2), TyOpK(b1,b2)) =
        case String.compare(a1, b1) of EQUAL =>
          List.collate Int.compare (a2, b2)
        | x => x
  val ty_ht : (ty_key, int) dict ref = ref (mkDict ty_key_cmp)

  fun ty_lookup key = peek(!ty_ht, key)
  fun ty_insert key v = ty_ht := insert(!ty_ht, key, v)

  (* Terms: VAR and CONST use Redblackmap; COMB uses IntPairTable *)
  fun str_int_cmp ((s1,i1): string * int, (s2,i2)) =
    case String.compare(s1, s2) of EQUAL => Int.compare(i1, i2) | x => x
  val var_ht : (string * int, int) dict ref = ref (mkDict str_int_cmp)
  val const_ht : (string * int, int) dict ref = ref (mkDict str_int_cmp)
  val comb_ht = IntPairTable.create 65536

  fun var_lookup key = peek(!var_ht, key)
  fun var_insert key v = var_ht := insert(!var_ht, key, v)
  fun const_lookup key = peek(!const_ht, key)
  fun const_insert key v = const_ht := insert(!const_ht, key, v)

  (* --- Unique binder names for Abs capture avoidance ---------------------- *)

  val binder_ctr = ref 0
  fun fresh_binder_name s = let
    val n = !binder_ctr
  in binder_ctr := n + 1; s ^ " " ^ Int.toString n end

  (* --- NEW_CONST / NEW_TYPE tracking ------------------------------------- *)

  val const_done : (string, unit) dict ref = ref (mkDict String.compare)
  val type_done : (string, unit) dict ref = ref (mkDict String.compare)
  fun mark_const name = const_done := insert(!const_done, name, ())
  fun mark_type name = type_done := insert(!type_done, name, ())
  fun is_const_done name =
    case peek(!const_done, name) of SOME _ => true | NONE => false
  fun is_type_done name =
    case peek(!type_done, name) of SOME _ => true | NONE => false

  (* Axiom names: PFT thm ID -> optional name. Axiom IDs are registered
     with NONE at emit time, resolved to SOME name by scanning named_thms
     after exports. Read by axiom write closures at buffer flush time. *)
  val axiom_names : (int, string option) dict ref = ref (mkDict Int.compare)

  (* --- Emit helpers ------------------------------------------------------ *)

  fun emit entry = DArray.push(cmd_buf, entry)

  (* Emit a type-defining command and record its def index *)
  fun emit_ty_def id entry = (emit entry; def_ty id)
  (* Emit a term-defining command and record its def index *)
  fun emit_tm_def id entry = (emit entry; def_tm id)
  (* Emit a theorem-defining command and record its def index *)
  fun emit_th_def id entry = (emit entry; def_th id)
  (* Emit a ci-defining command and record its def index *)
  fun emit_ci_def id entry = (emit entry; def_ci id)

  (* Emit a command with no refs and no defined ID (e.g., NEW_TYPE) *)
  fun emit0 wfn = emit {write = wfn,
    ref_ty = [], ref_tm = [], ref_th = [], ref_ci = []}

  (* ======================================================================= *)
  (* Candle pro-forma theorem IDs (lazy-loaded on first use)                 *)
  (* ======================================================================= *)

  val candle_pths : (string, int) dict ref = ref (mkDict String.compare)

  fun candle_load_pth name =
    case peek(!candle_pths, name) of
      SOME id => id
    | NONE => let
        val id = alloc_th ()
      in emit_th_def id {write = fn out => PFTWriter.load out id name,
           ref_ty = [], ref_tm = [], ref_th = [], ref_ci = []};
         candle_pths := insert(!candle_pths, name, id);
         id
      end

  (* ======================================================================= *)
  (* Type emission                                                           *)
  (* ======================================================================= *)

  fun emit_type (ty_ptr : Type.hol_type ptr) : int =
    if not (isPtr ty_ptr) then raise Fail "emit_type: not a ptr"
    else let val k = ptr ty_ptr
             val cached = ty_memo_get k
    in if cached >= 0 then cached
       else emit_type_inner k ty_ptr
    end

  and emit_type_inner k (ty_ptr : Type.hol_type ptr) : int =
    case shType heap ty_ptr of
      Tyv s => let
        val key = TyVarK s
      in case ty_lookup key of
           SOME id => (ty_memo_set k id; id)
         | NONE => let
             val id = alloc_ty ()
           in emit_ty_def id {write = fn out => PFTWriter.tyvar out id s,
                    ref_ty = [], ref_tm = [], ref_th = [], ref_ci = []};
              ty_insert key id;
              ty_memo_set k id;
              id
           end
      end
    | Tyapp (idp, args_ptr) => let
        val (Thy, Tyop) = ident heap idp
        val () = check_def ty_defs Thy Tyop
        val arg_ids = list heap emit_type args_ptr
        val name = tr_name (Thy ^ "$" ^ Tyop)
        val key = TyOpK(name, arg_ids)
      in case ty_lookup key of
           SOME id => (ty_memo_set k id; id)
         | NONE => let
             val () = if Thy = thyname andalso not (is_type_done Tyop)
                      then (mark_type Tyop;
                            emit0 (fn out =>
                              PFTWriter.new_type out name (length arg_ids)))
                      else ()
             val id = alloc_ty ()
           in emit_ty_def id {write = fn out => PFTWriter.tyop out id name arg_ids,
                    ref_ty = arg_ids, ref_tm = [], ref_th = [], ref_ci = []};
              ty_insert key id;
              ty_memo_set k id;
              id
           end
      end

  (* ======================================================================= *)
  (* Term emission                                                           *)
  (* ======================================================================= *)

  and emit_term (tm_ptr : Term.term ptr) : int =
    if not (isPtr tm_ptr) then raise Fail "emit_term: not a ptr"
    else let val k = ptr tm_ptr
             val cached = Array.sub(tm_memo, k)
    in if cached >= 0 then cached
       else emit_term_sub Subst.id tm_ptr
    end

  and emit_term_sub env (tm_ptr : Term.term ptr) : int =
    if is_closed tm_ptr then emit_term_closed tm_ptr
    else emit_term_core env tm_ptr

  and emit_term_closed (tm_ptr : Term.term ptr) : int = let
    val k = ptr tm_ptr
    val cached = Array.sub(tm_memo, k)
  in if cached >= 0 then cached
     else let
       val id = emit_term_core Subst.id tm_ptr
     in
       (* Cache the result. For Clos nodes, the returned ID is the
          body's ID after substitution — safe to cache at this pointer
          because the Clos is closed (same result every time). *)
       Array.update(tm_memo, k, id);
       id
     end
  end

  and emit_term_core env (tm_ptr : Term.term ptr) : int =
    case shTerm heap tm_ptr of
      Fv (s, typ) => let
        val ty_id = emit_type typ
        val key = (s, ty_id)
      in case var_lookup key of
           SOME id => id
         | NONE => let
             val id = alloc_tm ()
           in emit_tm_def id {write = fn out => PFTWriter.var out id s ty_id,
                    ref_ty = [ty_id], ref_tm = [], ref_th = [], ref_ci = []};
              var_insert key id;
              id
           end
      end
    | Const (idp, typ) => let
        val (Thy, Name) = ident heap idp
        val () = check_def tm_defs Thy Name
        val ty_id = emit_type typ
        val qname = tr_name (Thy ^ "$" ^ Name)
        val () = if Thy = thyname andalso not (is_const_done Name)
                 then (mark_const Name;
                       emit {write = fn out =>
                               PFTWriter.new_const out qname ty_id,
                             ref_ty = [ty_id], ref_tm = [],
                             ref_th = [], ref_ci = []})
                 else ()
        val key = (qname, ty_id)
      in case const_lookup key of
           SOME id => id
         | NONE => let
             val id = alloc_tm ()
           in emit_tm_def id {write = fn out => PFTWriter.const out id qname ty_id,
                    ref_ty = [ty_id], ref_tm = [], ref_th = [], ref_ci = []};
              const_insert key id;
              id
           end
      end
    | Bv n => (case Subst.exp_rel(env, n) of
                 (0, SOME tm_id) => tm_id
               | _ => raise Fail ("emit_term: unresolved Bv " ^
                                   Int.toString n))
    | Comb (t1, t2) => let
        val id1 = emit_term_sub env t1
        val id2 = emit_term_sub env t2
      in case IntPairTable.lookup comb_ht (id1, id2) of
           SOME id => id
         | NONE => let
             val id = alloc_tm ()
           in emit_tm_def id {write = fn out => PFTWriter.comb out id id1 id2,
                    ref_ty = [], ref_tm = [id1, id2], ref_th = [], ref_ci = []};
              IntPairTable.insert comb_ht (id1, id2) id;
              id
           end
      end
    | Abs (t1, t2) => let
        val (s, typ) = resolve_binder_name t1
        val ty_id = emit_type typ
        val B = alloc_tm ()
        val bname = fresh_binder_name s
        val () = emit_tm_def B {write = fn out =>
                   PFTWriter.var out B bname ty_id,
                 ref_ty = [ty_id], ref_tm = [], ref_th = [], ref_ci = []}
        val body_id = emit_term_sub (Subst.cons(env, B)) t2
      in
        emit_tm_def B {write = fn out => PFTWriter.abs out B B body_id,
              ref_ty = [], ref_tm = [B, body_id],
              ref_th = [], ref_ci = []};
        B
      end
    | Clos (sbp, tmp) => let
        val env' = Subst.comp (fn (_,s) => s) (env, emit_subs env sbp)
      in emit_term_sub env' tmp end

  and resolve_binder_name (tm_ptr : Term.term ptr) : string * Type.hol_type ptr =
    case shTerm heap tm_ptr of
      Fv (s, typ) => (s, typ)
    | Clos (_, tmp) => resolve_binder_name tmp
    | _ => raise Fail "resolve_binder_name: not a variable"

  and emit_subs env (sbp : Term.term Subst.subs ptr) : int Subst.subs =
    case shSubs heap sbp of
      Id => Subst.id
    | Cons (sbp', tmp) =>
        Subst.cons(emit_subs env sbp', emit_term_sub env tmp)
    | Lift (n, sbp') => Subst.lift(n, emit_subs env sbp')
    | Shift (n, sbp') => Subst.shift(n, emit_subs env sbp')

  (* ======================================================================= *)
  (* check_def                                                               *)
  (* ======================================================================= *)

  and check_def map Thy nm =
    if Thy = thyname then case peek(map, nm) of
      SOME thps => List.app (ignore o emit_thm) thps
    | _ => ()
    else ()

  (* ======================================================================= *)
  (* Candle theorem dispatch                                                 *)
  (* Emits Candle-ruleset commands for each HOL4 proof constructor.          *)
  (* For derived rules, uses pro-formas from the preamble via                *)
  (* INST + PROVE_HYP.                                                      *)
  (* ======================================================================= *)

  and emit_thm_candle result_id concl_ptr proof
        (tm : Term.term ptr -> int)
        (th : Thm.thm ptr -> int)
        (ty : Type.hol_type ptr -> int)
        mk_entry emit = let
    (* Emit an intermediate Candle theorem command.
       wfn: pft_out -> int{id} -> unit. Allocates fresh ID, returns it. *)
    fun candle_th wfn ref_tms ref_ths = let
      val iid = alloc_th ()
      val entry = {write = fn out => wfn out iid,
        ref_ty = [], ref_tm = ref_tms, ref_th = ref_ths, ref_ci = []}
    in emit_th_def iid entry; emit entry; iid end
    (* Emit the final result using the pre-allocated result_id *)
    fun emit_final wfn = emit (mk_entry wfn)
  in
    case proof of
    (* === Direct mappings (1:1 to Candle core rules) === *)
      REFL_prf a => let val a = tm a
        in emit_final (fn out => PFTWriter.Candle.refl out result_id a) end
    | TRANS_prf (a, b) => let val a = th a val b = th b
        in emit_final (fn out =>
             PFTWriter.Candle.trans out result_id a b) end
    | MK_COMB_prf (a, b) => let val a = th a val b = th b
        in emit_final (fn out =>
             PFTWriter.Candle.mk_comb out result_id a b) end
    | ABS_prf (a, b) => let val a = tm a val b = th b
        in emit_final (fn out =>
             PFTWriter.Candle.abs out result_id a b) end
    | EQ_MP_prf (a, b) => let val a = th a val b = th b
        in emit_final (fn out =>
             PFTWriter.Candle.eq_mp out result_id a b) end
    | ASSUME_prf a => let val a = tm a
        in emit_final (fn out =>
             PFTWriter.Candle.assume out result_id a) end
    | SYM_prf a => let val a = th a
        in emit_final (fn out =>
             PFTWriter.Candle.sym out result_id a) end
    | INST_prf (a, b) => let
        val pairs = list heap (tuple2 heap (tm, tm)) a
        val b = th b
      in emit_final (fn out =>
           PFTWriter.Candle.inst out result_id b pairs) end
    | INST_TYPE_prf (a, b) => let
        val pairs = list heap (tuple2 heap (ty, ty)) a
        val b = th b
      in emit_final (fn out =>
           PFTWriter.Candle.inst_type out result_id b pairs) end
    | deductAntisym_prf (a, b) => let val a = th a val b = th b
        in emit_final (fn out =>
             PFTWriter.Candle.deduct_antisym_rule out result_id a b) end
    | Axiom_prf => let
        val c = tm concl_ptr
        val () = axiom_names := insert(!axiom_names, result_id, NONE)
      in emit_final (fn out =>
           PFTWriter.axiom out result_id c
             (find(!axiom_names, result_id))) end
    | Disk_prf (dep_thy, b) => let
        val dep_id = thmId heap b
        val save_name = disk_save_name dep_thy dep_id
      in emit_final (fn out =>
           PFTWriter.load out result_id save_name) end

    (* === Simple compositions === *)
    | AP_TERM_prf (a, b) => let
        val a = tm a val b = th b
        val refl_a = candle_th
          (fn out => fn iid => PFTWriter.Candle.refl out iid a) [a] []
      in emit_final (fn out =>
           PFTWriter.Candle.mk_comb out result_id refl_a b) end
    | AP_THM_prf (a, b) => let
        val a = th a val b = tm b
        val refl_b = candle_th
          (fn out => fn iid => PFTWriter.Candle.refl out iid b) [b] []
      in emit_final (fn out =>
           PFTWriter.Candle.mk_comb out result_id a refl_b) end

    (* === TODO: Pro-forma based rules === *)
    | _ => raise Fail ("emit_thm_candle: unimplemented proof type")
  end

  (* ======================================================================= *)
  (* Theorem emission                                                        *)
  (* ======================================================================= *)

  and emit_thm (thm_ptr : Thm.thm ptr) : int =
    if not (isPtr thm_ptr) then raise Fail "emit_thm: not a ptr"
    else let val k = ptr thm_ptr
             val cached = th_memo_get k
    in if cached >= 0 then cached
       else let
         val (_, concl_ptr, proof_ptr) = shThm heap thm_ptr
         val proof = shProof heap proof_ptr
       in
         (* save_dep_prf: transparent wrapper, just return inner thm's ID *)
         case proof of
           save_dep_prf a => let
             val inner_id = emit_thm a
           in th_memo_set k inner_id; inner_id end
         | _ => let
         (* Accumulators for referenced IDs *)
         val rtys : int list ref = ref []
         val rtms : int list ref = ref []
         val rths : int list ref = ref []
         val rcis : int list ref = ref []
         fun tm p = let val r = emit_term p
                    in rtms := r :: !rtms; r end
         fun th p = let val r = emit_thm p
                    in rths := r :: !rths; r end
         fun ty p = let val r = emit_type p
                    in rtys := r :: !rtys; r end
         val id = alloc_th ()
         val () = th_memo_set k id
         fun mk_entry wfn = (def_th id; {write = wfn,
           ref_ty = !rtys, ref_tm = !rtms, ref_th = !rths, ref_ci = !rcis})
       in if is_candle
          then emit_thm_candle id concl_ptr proof tm th ty
                               mk_entry emit
          else
          case proof of
           ABS_prf (a, b) => let val a = tm a val b = th b
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.abs_thm out id a b)) end
         | ALPHA_prf (a, b) => let val a = tm a val b = tm b
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.alpha out id a b)) end
         | AP_TERM_prf (a, b) => let val a = tm a val b = th b
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.ap_term out id a b)) end
         | AP_THM_prf (a, b) => let val a = th a val b = tm b
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.ap_thm out id a b)) end
         | ASSUME_prf a => let val a = tm a
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.assume out id a)) end
         | Axiom_prf => let
             val c = emit_term concl_ptr
             val () = rtms := c :: !rtms
             val () = axiom_names :=
               insert(!axiom_names, id, NONE)
           in emit (mk_entry (fn out =>
                PFTWriter.axiom out id c
                  (find(!axiom_names, id)))) end
         | BETA_CONV_prf a => let val a = tm a
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.beta_conv out id a)) end
         | Beta_prf a => let val a = th a
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.beta_thm out id a)) end
         | CCONTR_prf (a, b) => let val a = tm a val b = th b
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.ccontr out id a b)) end
         | CHOOSE_prf (a, b, c) => let val a = tm a val b = th b val c = th c
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.choose out id a b c)) end
         | CONJUNCT1_prf a => let val a = th a
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.conjunct1 out id a)) end
         | CONJUNCT2_prf a => let val a = th a
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.conjunct2 out id a)) end
         | CONJ_prf (a, b) => let val a = th a val b = th b
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.conj out id a b)) end
         | DISCH_prf (a, b) => let val a = tm a val b = th b
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.disch out id a b)) end
         | DISJ1_prf (a, b) => let val a = th a val b = tm b
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.disj1 out id a b)) end
         | DISJ2_prf (a, b) => let val a = tm a val b = th b
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.disj2 out id a b)) end
         | DISJ_CASES_prf (a, b, c) => let val a = th a val b = th b val c = th c
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.disj_cases out id a b c)) end
         | Def_const_list_prf (a, b) => let
             val a = th a
             val ids = list heap get_const_id b
             val names = List.map (fn (Thy,nm) => tr_name (Thy ^ "$" ^ nm)) ids
             val () = List.app (fn (_,nm) => mark_const nm) ids
           in emit (mk_entry (fn out =>
                PFTWriter.HOL4.def_spec_gen out id a names)) end
         | Def_const_prf (a, b) => emit_def_const id (a, b)
         | Def_spec_prf (a, b) => let
             val a = th a
             val ids = list heap get_const_id b
             val names = List.map (fn (_,nm) => nm) ids
             val () = List.app mark_const names
           in emit (mk_entry (fn out =>
                PFTWriter.HOL4.def_spec out id a names)) end
         | Def_tyop_prf (a, b, c) => let
             val _ = list heap ty a
             val () = if thyname = "bool"
                      then check_def tm_defs thyname "TYPE_DEFINITION"
                      else ()
             val b = th b
             val (Thy, Tyop) = get_type_id c
             val () = mark_type Tyop
           in emit (mk_entry (fn out =>
                PFTWriter.HOL4.def_tyop out id b (tr_name (Thy ^ "$" ^ Tyop)))) end
         | Disk_prf (dep_thy, b) => let
             val dep_id = thmId heap b
             val save_name = disk_save_name dep_thy dep_id
           in emit (mk_entry (fn out =>
                PFTWriter.load out id save_name)) end
         | EQ_IMP_RULE1_prf a => let val a = th a
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.eq_imp_rule1 out id a)) end
         | EQ_IMP_RULE2_prf a => let val a = th a
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.eq_imp_rule2 out id a)) end
         | EQ_MP_prf (a, b) => let val a = th a val b = th b
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.eq_mp out id a b)) end
         | EXISTS_prf (a, b, c) => let val a = tm a val b = tm b val c = th c
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.exists out id a b c)) end
         | GENL_prf (a, b) => let
             val tms = list heap tm a
             val b = th b
           in emit (mk_entry (fn out =>
                PFTWriter.HOL4.genl out id b tms)) end
         | GEN_ABS_prf (a, b, c) => let
             val opt = option heap tm a
             val c_id = case opt of SOME c => c
               | NONE => raise Fail "GEN_ABS: missing constant"
             val tms = list heap tm b
             val c = th c
           in emit (mk_entry (fn out =>
                PFTWriter.HOL4.gen_abs out id c c_id tms)) end
         | GEN_prf (a, b) => let val a = tm a val b = th b
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.gen out id a b)) end
         | INST_TYPE_prf (a, b) => let
             val pairs = list heap (tuple2 heap (ty, ty)) a
             val b = th b
           in emit (mk_entry (fn out =>
                PFTWriter.HOL4.inst_type out id b pairs)) end
         | INST_prf (a, b) => let
             val pairs = list heap (tuple2 heap (tm, tm)) a
             val b = th b
           in emit (mk_entry (fn out =>
                PFTWriter.HOL4.inst out id b pairs)) end
         | MK_COMB_prf (a, b) => let val a = th a val b = th b
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.mk_comb out id a b)) end
         | MP_prf (a, b) => let val a = th a val b = th b
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.mp out id a b)) end
         | Mk_abs_prf (a, _, c) => let
             val a = th a
             (* walk does tm b; PFT Mk_abs doesn't use it, skip *)
             val c = th c
           in emit (mk_entry (fn out =>
                PFTWriter.HOL4.mk_abs_thm out id a c)) end
         | Mk_comb_prf (a, b, c) => let val a = th a val b = th b val c = th c
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.mk_comb_thm out id a b c)) end
         | NOT_ELIM_prf a => let val a = th a
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.not_elim out id a)) end
         | NOT_INTRO_prf a => let val a = th a
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.not_intro out id a)) end
         | REFL_prf a => let val a = tm a
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.refl out id a)) end
         | SPEC_prf (a, b) => let val a = tm a val b = th b
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.spec out id a b)) end
         | SUBST_prf (a, b, c) => let
             val pairs = list heap (tuple2 heap (tm, th)) a
             val b = tm b
             val c = th c
           in emit (mk_entry (fn out =>
                PFTWriter.HOL4.subst out id b c pairs)) end
         | SYM_prf a => let val a = th a
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.sym out id a)) end
         | Specialize_prf (a, b) => let val a = tm a val b = th b
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.specialize out id a b)) end
         | TRANS_prf (a, b) => let val a = th a val b = th b
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.trans out id a b)) end
         | compute_prf (a, b) => emit_compute id (tuple2 heap (I, I) a, b)
         | deductAntisym_prf (a, b) => let val a = th a val b = th b
             in emit (mk_entry (fn out =>
                  PFTWriter.HOL4.deductAntisym out id a b)) end
         | deleted_prf => raise Fail "emit_thm: deleted"
         | save_dep_prf _ => raise Fail "unreachable"
       ; id end end
    end

  (* ======================================================================= *)
  (* Def_const                                                               *)
  (* ======================================================================= *)

  (* Synthesize ASSUME(v = rhs) then DEF_SPEC. All synthesized
     intermediate objects go through hash-cons tables. *)
  and emit_def_const thm_id (rhs_p, const_ptr) = let
    val rhs_id = emit_term rhs_p
    val (Thy, Name) = get_const_id const_ptr
    val ty_ptr = case shTerm heap const_ptr of
        Const (_, tp) => tp
      | _ => raise Fail "Def_const: expected Const"
    val rhs_ty_id = emit_type ty_ptr
    (* Build equality type: ty -> (ty -> bool) *)
    val bool_ty_id = emit_tyop "min$bool" []
    val fun_ty1_id = emit_tyop "min$fun" [rhs_ty_id, bool_ty_id]
    val eq_ty_id = emit_tyop "min$fun" [rhs_ty_id, fun_ty1_id]
    (* VAR for the new constant name *)
    val var_id = emit_var Name rhs_ty_id
    (* CONST for = *)
    val eq_id = emit_const "min$=" eq_ty_id
    (* (= v) *)
    val eq_var_id = emit_comb eq_id var_id
    (* (= v) rhs *)
    val eq_tm_id = emit_comb eq_var_id rhs_id
    (* ASSUME (v = rhs) *)
    val assume_id = alloc_th ()
    val () = emit_th_def assume_id {write = fn out =>
      PFTWriter.HOL4.assume out assume_id eq_tm_id,
      ref_ty = [], ref_tm = [eq_tm_id], ref_th = [], ref_ci = []}
    (* DEF_SPEC_GEN *)
    val () = mark_const Name
    val () = emit_th_def thm_id {write = fn out =>
      PFTWriter.HOL4.def_spec_gen out thm_id assume_id
        [tr_name (thyname ^ "$" ^ Name)],
      ref_ty = [], ref_tm = [], ref_th = [assume_id], ref_ci = []}
  in () end

  (* Hash-consed helpers for synthesized objects *)
  and emit_tyop name args =
    let val key = TyOpK(name, args)
    in case ty_lookup key of
         SOME id => id
       | NONE => let val id = alloc_ty ()
         in emit_ty_def id {write = fn out => PFTWriter.tyop out id name args,
                  ref_ty = args, ref_tm = [], ref_th = [], ref_ci = []};
            ty_insert key id; id
         end
    end

  and emit_var name ty_id =
    let val key = (name, ty_id)
    in case var_lookup key of
         SOME id => id
       | NONE => let val id = alloc_tm ()
         in emit_tm_def id {write = fn out => PFTWriter.var out id name ty_id,
                  ref_ty = [ty_id], ref_tm = [], ref_th = [], ref_ci = []};
            var_insert key id; id
         end
    end

  and emit_const name ty_id =
    let val key = (name, ty_id)
    in case const_lookup key of
         SOME id => id
       | NONE => let val id = alloc_tm ()
         in emit_tm_def id {write = fn out => PFTWriter.const out id name ty_id,
                  ref_ty = [ty_id], ref_tm = [], ref_th = [], ref_ci = []};
            const_insert key id; id
         end
    end

  and emit_comb rator_id rand_id =
    case IntPairTable.lookup comb_ht (rator_id, rand_id) of
      SOME id => id
    | NONE => let val id = alloc_tm ()
      in emit_tm_def id {write = fn out => PFTWriter.comb out id rator_id rand_id,
               ref_ty = [], ref_tm = [rator_id, rand_id], ref_th = [], ref_ci = []};
         IntPairTable.insert comb_ht (rator_id, rand_id) id; id
      end

  (* ======================================================================= *)
  (* compute                                                                 *)
  (* ======================================================================= *)

  and emit_compute thm_id ((compute_args_ptr, ths_ptr), tm_p) = let
    val ci_id = emit_compute_init compute_args_ptr
    val th_id_list = list heap emit_thm ths_ptr
    val tm_id = emit_term tm_p
  in emit_th_def thm_id {write = fn out =>
       PFTWriter.HOL4.compute out thm_id ci_id tm_id th_id_list,
     ref_ty = [], ref_tm = [tm_id], ref_th = th_id_list,
     ref_ci = [ci_id]}
  end

  and emit_compute_init (args_ptr : compute_args ptr) : int = let
    val k = ptr args_ptr
    val cached = ci_memo_get k
  in if cached >= 0 then cached
     else let
       val {num_type, char_eqns, cval_type, cval_terms} = shComputeArgs heap args_ptr
       val num_ty = emit_type num_type
       val cval_ty = emit_type cval_type
       val char_eqns = list heap (tuple2 heap (str heap, emit_thm)) char_eqns
       val cval_terms = list heap (tuple2 heap (str heap, emit_term)) cval_terms
       val eqn_th_ids = List.map #2 char_eqns
       val cval_tm_ids = List.map #2 cval_terms
       val ci_id = alloc_ci ()
       val () = emit_ci_def ci_id {write = fn out =>
         PFTWriter.HOL4.compute_init out ci_id num_ty cval_ty
           char_eqns cval_terms,
         ref_ty = [num_ty, cval_ty], ref_tm = cval_tm_ids,
         ref_th = eqn_th_ids, ref_ci = []}
       val () = ci_memo_set k ci_id
     in ci_id end
  end

  (* ======================================================================= *)
  (* Process exports                                                         *)
  (* ======================================================================= *)

  val () = appList heap (fn p => let
    val (nm, (thp, _)) = tuple3 heap (str heap, I, I) p
    val thm_id = emit_thm thp
    val () = emit {write = fn out =>
      PFTWriter.save out (thyname ^ "$" ^ nm) thm_id,
      ref_ty = [], ref_tm = [], ref_th = [thm_id], ref_ci = []}
  in () end) all_thms

  val anon_idx = ref 0
  val () = appList heap (fn p => let
    val i = !anon_idx
    val () = anon_idx := i + 1
    val thm_id = emit_thm p
    val () = emit {write = fn out =>
      PFTWriter.save out (thyname ^ "#" ^ Int.toString i) thm_id,
      ref_ty = [], ref_tm = [], ref_th = [thm_id], ref_ci = []}
  in () end) anon_thms

  (* Ensure all theory constants/types are introduced *)

  val () = appList heap (fn p => let
    val (Name, ty_ptr) = tuple2 heap (str heap, I) p
    val () = check_def tm_defs thyname Name
  in if is_const_done Name then ()
     else let
       val ty_id = emit_type ty_ptr
       val () = mark_const Name
     in emit {write = fn out =>
               PFTWriter.new_const out (tr_name (thyname ^ "$" ^ Name)) ty_id,
             ref_ty = [ty_id], ref_tm = [], ref_th = [], ref_ci = []} end
  end) constants

  val () = appList heap (fn p => let
    val (Tyop, arity) = tuple2 heap (str heap, int) p
    val () = check_def ty_defs thyname Tyop
  in if is_type_done Tyop then ()
     else (mark_type Tyop;
           emit0 (fn out =>
             PFTWriter.new_type out (tr_name (thyname ^ "$" ^ Tyop)) arity))
  end) types

  (* ======================================================================= *)
  (* Axiom name fixup                                                        *)
  (* ======================================================================= *)

  (* Resolve axiom names: for each named thm whose PFT ID is in the
     axiom_names map, set its name. *)
  val () = appList heap (fn p => let
    val (nm, (thp, _)) = tuple3 heap (str heap, I, I) p
    val pft_id = th_memo_get (ptr thp)
  in if pft_id >= 0 andalso inDomain(!axiom_names, pft_id) then
       axiom_names := insert(!axiom_names, pft_id, SOME nm)
     else ()
  end) all_thms

  (* ======================================================================= *)
  (* DEL insertion and output                                                *)
  (* ======================================================================= *)

  val n_ty = !next_ty
  val n_tm = !next_tm
  val n_th = !next_th
  val n_ci = !next_ci

  val ruleset_str = case ruleset of HOL4 => "hol4" | Candle => "candle"
  val out = PFTWriter.openOut
    {file = output, binary = binary, version = 1, ruleset = ruleset_str}

  val () = write_with_dels out cmd_buf
    {n_ty = n_ty, n_tm = n_tm, n_th = n_th, n_ci = n_ci}
    {def_ty = def_idx_to_array (!def_idx_ty) n_ty,
     def_tm = def_idx_to_array (!def_idx_tm) n_tm,
     def_th = def_idx_to_array (!def_idx_th) n_th,
     def_ci = def_idx_to_array (!def_idx_ci) n_ci}

in
  PFTWriter.closeOut out
    {n_ty = n_ty, n_tm = n_tm, n_th = n_th, n_ci = n_ci}
end

end
