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
  val abs_ht  = IntPairTable.create 4096

  (* Reverse lookup: PFT term ID → subterm IDs.
     Populated by emit_comb/emit_abs. Enables Clos-safe destructuring
     of PFT terms by ID, without traversing the heap.
     Two parallel arrays (rator/var and rand/body), grown as needed.
     Entries for non-COMB/ABS terms are (~1, ~1). *)
  val tm_part1 = ref (Array.array(65536, ~1))  (* rator or var *)
  val tm_part2 = ref (Array.array(65536, ~1))  (* rand or body *)

  fun tm_parts_ensure id = let
    val a1 = !tm_part1
    val len = Array.length a1
  in if id < len then ()
     else let
       val newlen = Int.max(id + 1, len * 2)
       val b1 = Array.array(newlen, ~1)
       val b2 = Array.array(newlen, ~1)
       val () = Array.copy{src = a1, dst = b1, di = 0}
       val () = Array.copy{src = !tm_part2, dst = b2, di = 0}
     in tm_part1 := b1; tm_part2 := b2 end
  end

  fun tm_parts_set id (x, y) =
    (tm_parts_ensure id;
     Array.update(!tm_part1, id, x);
     Array.update(!tm_part2, id, y))

  fun pft_dest_comb id =
    let val f = Array.sub(!tm_part1, id)
        val x = Array.sub(!tm_part2, id)
    in if f >= 0 then (f, x)
       else raise Fail ("pft_dest_comb: term " ^ Int.toString id ^
                         " is not a COMB/ABS")
    end

  fun pft_dest_abs id = pft_dest_comb id  (* same layout: (var, body) *)

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
        tm_parts_set B (B, body_id);
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
  (* Candle: heap destructuring helpers                                      *)
  (* ======================================================================= *)

  (* Destructure a Comb from the heap *)
  and heap_dest_comb (tm_ptr : Term.term ptr) =
    case shTerm heap tm_ptr of
      Comb (f, x) => (f, x)
    | _ => raise Fail "heap_dest_comb: not a Comb"

  (* Get the conclusion of a theorem from the heap *)
  and heap_concl (thm_ptr : Thm.thm ptr) =
    let val (_, concl, _) = shThm heap thm_ptr in concl end

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
    (* Emit a candle_th that uses result_id (for the last step of a derivation) *)
    fun candle_th_result wfn = emit (mk_entry (fn out => wfn out result_id))

    (* Preamble variable term IDs — memoized via emit_var hash-cons *)
    val bool_tyid = emit_tyop "bool" []
    fun pvar_p () = emit_var "p" bool_tyid
    fun pvar_q () = emit_var "q" bool_tyid
    fun pvar_t () = emit_var "t" bool_tyid
    fun pvar_r () = emit_var "r" bool_tyid
    fun pvar_Q () = emit_var "Q" bool_tyid

    (* Candle equality constant at bool type — for building eq terms *)
    val bbb_tyid = emit_tyop "fun" [bool_tyid, emit_tyop "fun" [bool_tyid, bool_tyid]]
    fun eq_bool_const () = emit_const "=" bbb_tyid

    (* Candle /\ constant *)
    fun and_const () = emit_const "/\\" bbb_tyid

    (* Candle ==> constant *)
    fun imp_const () = emit_const "==>" bbb_tyid

    (* TYVAR "A" for INST_TYPE on polymorphic pro-formas — memoized *)
    fun tyvar_A () = let val key = TyVarK "A"
      in case ty_lookup key of SOME id => id
       | NONE => let val id = alloc_ty ()
         in emit_ty_def id {write = fn out => PFTWriter.tyvar out id "A",
                  ref_ty = [], ref_tm = [], ref_th = [], ref_ci = []};
            ty_insert key id; id end end

    (* === Candle derived-rule helpers ===
       These emit sequences of Candle commands and return theorem IDs. *)

    (* do_MP: from ith: ⊢ a ==> b and th: ⊢ a, derive ⊢ b.
       Uses MP_rth = {p} ⊢ (p ==> q) = q.
       final_id: if SOME id, the last step uses that id; if NONE, allocates fresh. *)
    fun do_MP_gen final_id ith a_tm b_tm ant_th =
      let val rth = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst out iid (candle_load_pth "candle$MP")
              [(pvar_p(), a_tm), (pvar_q(), b_tm)]) [a_tm, b_tm] []
          val da = candle_th (fn out => fn iid =>
            PFTWriter.Candle.deduct_antisym_rule out iid ant_th rth)
              [] [ant_th, rth]
          val eq1 = candle_th (fn out => fn iid =>
            PFTWriter.Candle.eq_mp out iid da ant_th) [] [da, ant_th]
      in case final_id of
           NONE => candle_th (fn out => fn iid =>
             PFTWriter.Candle.eq_mp out iid eq1 ith) [] [eq1, ith]
         | SOME fid => (emit (mk_entry (fn out =>
             PFTWriter.Candle.eq_mp out fid eq1 ith)); fid)
      end
    fun do_MP ith a b th = do_MP_gen NONE ith a b th

    (* do_CONJ: from th1: A ⊢ a and th2: B ⊢ b, derive A ∪ B ⊢ a ∧ b *)
    fun do_CONJ a_tm b_tm th1 th2 =
      let val ci = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst out iid (candle_load_pth "candle$CONJ")
              [(pvar_p(), a_tm), (pvar_q(), b_tm)]) [a_tm, b_tm] []
          val c1 = candle_th (fn out => fn iid =>
            PFTWriter.Candle.prove_hyp out iid ci th1) [] [ci, th1]
      in candle_th (fn out => fn iid =>
           PFTWriter.Candle.prove_hyp out iid c1 th2) [] [c1, th2] end

    (* do_CONJUNCT1: from th: A ⊢ a ∧ b, derive A ⊢ a *)
    fun do_CONJUNCT1 a_tm b_tm th =
      let val ci = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst out iid (candle_load_pth "candle$CONJUNCT1")
              [(pvar_p(), a_tm), (pvar_q(), b_tm)]) [a_tm, b_tm] []
      in candle_th (fn out => fn iid =>
           PFTWriter.Candle.prove_hyp out iid ci th) [] [ci, th] end

    (* do_CONJUNCT2: from th: A ⊢ a ∧ b, derive A ⊢ b *)
    fun do_CONJUNCT2 a_tm b_tm th =
      let val ci = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst out iid (candle_load_pth "candle$CONJUNCT2")
              [(pvar_p(), a_tm), (pvar_q(), b_tm)]) [a_tm, b_tm] []
      in candle_th (fn out => fn iid =>
           PFTWriter.Candle.prove_hyp out iid ci th) [] [ci, th] end

    (* do_DISCH: from a_tm and th: A ⊢ c, derive A\{a} ⊢ a ==> c. *)
    fun do_DISCH a_tm c_tm th_c =
      let val a_and_c = emit_comb (emit_comb (and_const()) a_tm) c_tm
          val assume_a = candle_th (fn out => fn iid =>
            PFTWriter.Candle.assume out iid a_tm) [a_tm] []
          val ci = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst out iid (candle_load_pth "candle$CONJ")
              [(pvar_p(), a_tm), (pvar_q(), c_tm)]) [a_tm, c_tm] []
          val c1 = candle_th (fn out => fn iid =>
            PFTWriter.Candle.prove_hyp out iid ci assume_a) [] [ci, assume_a]
          val cj = candle_th (fn out => fn iid =>
            PFTWriter.Candle.prove_hyp out iid c1 th_c) [] [c1, th_c]
          val aac = candle_th (fn out => fn iid =>
            PFTWriter.Candle.assume out iid a_and_c) [a_and_c] []
          val c1i = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst out iid (candle_load_pth "candle$CONJUNCT1")
              [(pvar_p(), a_tm), (pvar_q(), c_tm)]) [a_tm, c_tm] []
          val c1t = candle_th (fn out => fn iid =>
            PFTWriter.Candle.prove_hyp out iid c1i aac) [] [c1i, aac]
          val da = candle_th (fn out => fn iid =>
            PFTWriter.Candle.deduct_antisym_rule out iid cj c1t) [] [cj, c1t]
          val di = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst out iid (candle_load_pth "candle$DISCH")
              [(pvar_p(), a_tm), (pvar_q(), c_tm)]) [a_tm, c_tm] []
      in candle_th (fn out => fn iid =>
           PFTWriter.Candle.eq_mp out iid di da) [] [di, da] end

    (* do_GEN: from v_tm and th: A ⊢ s, derive A ⊢ ∀v. s.
       v_ty = type of v, s_tm = conclusion term. *)
    fun do_GEN v_tm v_ty s_tm th_s =
      let val const_T_tm = emit_const "T" bool_tyid
          val eqt_pth = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst out iid (candle_load_pth "candle$EQT_INTRO")
              [(pvar_t(), s_tm)]) [s_tm] []
          val eqt = candle_th (fn out => fn iid =>
            PFTWriter.Candle.eq_mp out iid eqt_pth th_s) [] [eqt_pth, th_s]
          val abs_eq = candle_th (fn out => fn iid =>
            PFTWriter.Candle.abs out iid v_tm eqt) [v_tm] [eqt]
          val lam_v_s = emit_abs v_tm s_tm
          val gen_pth = candle_load_pth "candle$GEN"
          val gen_ty = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst_type out iid gen_pth
              [(tyvar_A(), v_ty)]) [] [gen_pth]
          val Ab = emit_tyop "fun" [v_ty, bool_tyid]
          val var_P_inst = emit_var "P" Ab
          val var_x_inst = emit_var "x" v_ty
          val gen_inst = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst out iid gen_ty
              [(var_P_inst, lam_v_s), (var_x_inst, v_tm)])
              [var_P_inst, lam_v_s, var_x_inst, v_tm] [gen_ty]
      in candle_th (fn out => fn iid =>
           PFTWriter.Candle.eq_mp out iid gen_inst abs_eq)
           [] [gen_inst, abs_eq] end

    (* do_SPEC: from t_tm and th: A ⊢ ∀v.s, derive A ⊢ s[t/v].
       pred_tm = the predicate λv.s, var_tm = the bound variable,
       forall_tm = the ∀ term, v_ty = type of the variable. *)
    fun do_SPEC t_tm pred_tm var_tm forall_tm v_ty th_forall =
      let val spec_pth = candle_load_pth "candle$SPEC"
          val spec_ty = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst_type out iid spec_pth
              [(tyvar_A(), v_ty)]) [] [spec_pth]
          val Ab = emit_tyop "fun" [v_ty, bool_tyid]
          val var_P_inst = emit_var "P" Ab
          val var_x_inst = emit_var "x" v_ty
          val spec_inst = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst out iid spec_ty
              [(var_P_inst, pred_tm), (var_x_inst, t_tm)])
              [var_P_inst, pred_tm, var_x_inst, t_tm] [spec_ty]
          val pred_t = emit_comb pred_tm t_tm
          val mp_result = do_MP spec_inst forall_tm pred_t th_forall
          (* Beta-reduce pred(t) = (λv.s)(t) to s[t/v] *)
          val app_var = emit_comb pred_tm var_tm
          val beta_th = candle_th (fn out => fn iid =>
            PFTWriter.Candle.beta out iid app_var) [app_var] []
          val beta_inst = if var_tm = t_tm then beta_th
            else candle_th (fn out => fn iid =>
              PFTWriter.Candle.inst out iid beta_th
                [(var_tm, t_tm)]) [var_tm, t_tm] [beta_th]
      in candle_th (fn out => fn iid =>
           PFTWriter.Candle.eq_mp out iid beta_inst mp_result)
           [] [beta_inst, mp_result] end

    (* do_beta_reduce: from lam_tm (= abs var_tm body) and arg_tm,
       derive ⊢ lam_tm arg_tm = body[arg/var]. *)
    fun do_beta_reduce lam_tm var_tm arg_tm =
      let val app_var = emit_comb lam_tm var_tm
          val beta_th = candle_th (fn out => fn iid =>
            PFTWriter.Candle.beta out iid app_var) [app_var] []
      in if var_tm = arg_tm then beta_th
         else candle_th (fn out => fn iid =>
           PFTWriter.Candle.inst out iid beta_th
             [(var_tm, arg_tm)]) [var_tm, arg_tm] [beta_th] end

    (* do_EXISTS: from th: A ⊢ P(witness), pred = λv.body, derive A ⊢ ∃v. body
       Needs: pred_tm, var_tm (bound var of pred), witness_tm, v_ty *)
    fun do_EXISTS pred_tm var_tm witness_tm v_ty th =
      let val exists_pth = candle_load_pth "candle$EXISTS"
          val exists_ty = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst_type out iid exists_pth
              [(tyvar_A(), v_ty)]) [] [exists_pth]
          val Ab_v = emit_tyop "fun" [v_ty, bool_tyid]
          val var_P_v = emit_var "P" Ab_v
          val var_x_v = emit_var "x" v_ty
          val exists_inst = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst out iid exists_ty
              [(var_P_v, pred_tm), (var_x_v, witness_tm)])
              [var_P_v, pred_tm, var_x_v, witness_tm] [exists_ty]
          val beta_e = do_beta_reduce pred_tm var_tm witness_tm
          val sym_beta = candle_th (fn out => fn iid =>
            PFTWriter.Candle.sym out iid beta_e) [] [beta_e]
          val witness_hyp = candle_th (fn out => fn iid =>
            PFTWriter.Candle.eq_mp out iid sym_beta th) [] [sym_beta, th]
      in candle_th (fn out => fn iid =>
           PFTWriter.Candle.prove_hyp out iid exists_inst witness_hyp)
           [] [exists_inst, witness_hyp] end

    (* do_AP_TERM: from f and th: ⊢ x = y, derive ⊢ f x = f y *)
    fun do_AP_TERM f th =
      candle_th (fn out => fn iid =>
        PFTWriter.Candle.mk_comb out iid
          (candle_th (fn out2 => fn iid2 =>
            PFTWriter.Candle.refl out2 iid2 f) [f] [])
          th) [] [th]

    (* mk_tyvar_cached: get or create a type variable by name *)
    fun mk_tyvar_cached name = let val key = TyVarK name
      in case ty_lookup key of SOME id => id
       | NONE => let val id = alloc_ty ()
         in emit_ty_def id {write = fn out => PFTWriter.tyvar out id name,
                  ref_ty = [], ref_tm = [], ref_th = [], ref_ci = []};
            ty_insert key id; id end end

    (* Helper to get type of a heap variable *)
    fun heap_var_type (v_ptr : Term.term ptr) =
      case shTerm heap v_ptr of
        Fv (_, t) => t
      | _ => raise Fail "heap_var_type: not a variable"

    (* exist_to_witness: from th: ⊢ ∃v. body, derive ⊢ (λv. body)(@(λv. body))
       using CHOOSE_pth + SELECT_AX. Returns (result_th, pred_id, witness_id, v_ty).
       Caller must emit the input theorem and conclusion first. *)
    fun exist_to_witness exists_th exists_concl_id exists_concl_ptr = let
      val (_, pred_id) = pft_dest_comb exists_concl_id
      val (_, pred_ptr) = heap_dest_comb exists_concl_ptr
      val (bv_ptr, _) = case shTerm heap pred_ptr of
          Abs (v, _) => (v, ()) | _ => raise Fail "exist_to_witness: not abs"
      val v_ty = ty (heap_var_type bv_ptr)
      val Ab = emit_tyop "fun" [v_ty, bool_tyid]
      val select_c = emit_const "@" (emit_tyop "fun" [Ab, v_ty])
      val witness = emit_comb select_c pred_id
      val pred_witness = emit_comb pred_id witness
      val sel_ax = candle_load_pth "candle$SELECT_AX"
      val sel_inst = candle_th (fn out => fn iid =>
        PFTWriter.Candle.inst out iid
          (candle_th (fn out2 => fn iid2 =>
            PFTWriter.Candle.inst_type out2 iid2 sel_ax
              [(tyvar_A(), v_ty)]) [] [sel_ax])
          [(emit_var "P" Ab, pred_id)]) [pred_id] [sel_ax]
      val choose = candle_load_pth "candle$CHOOSE"
      val choose_inst = candle_th (fn out => fn iid =>
        PFTWriter.Candle.inst out iid
          (candle_th (fn out2 => fn iid2 =>
            PFTWriter.Candle.inst_type out2 iid2 choose
              [(tyvar_A(), v_ty)]) [] [choose])
          [(emit_var "P" Ab, pred_id), (pvar_Q(), pred_witness)])
          [pred_id, pred_witness] [choose]
      val var_x_v = emit_var "x" v_ty
      val forall_inner = emit_comb (emit_const "!" (emit_tyop "fun" [Ab, bool_tyid]))
        (emit_abs var_x_v (emit_comb (emit_comb (imp_const()) (emit_comb pred_id var_x_v)) pred_witness))
      val imp_forall_pw = emit_comb (emit_comb (imp_const()) forall_inner) pred_witness
      val mp1 = do_MP choose_inst exists_concl_id imp_forall_pw exists_th
      val result = do_MP mp1 forall_inner pred_witness sel_inst
    in (result, pred_id, witness, v_ty, bv_ptr, pred_ptr) end

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

    (* === Pro-forma based: conjunction === *)
    | CONJ_prf (a, b) => let
        val a_th = th a val b_th = th b
        val a_tm = tm (heap_concl a) val b_tm = tm (heap_concl b)
        val r = do_CONJ a_tm b_tm a_th b_th
      in candle_th_result (fn out => fn fid =>
           PFTWriter.Candle.prove_hyp out fid r
             (candle_load_pth "candle$TRUTH")) end

    | CONJUNCT1_prf a => let
        val a_th = th a
        val concl_id = tm (heap_concl a)
        val (and_l_id, r_tm) = pft_dest_comb concl_id
        val (_, l_tm) = pft_dest_comb and_l_id
        val r = do_CONJUNCT1 l_tm r_tm a_th
      in candle_th_result (fn out => fn fid =>
           PFTWriter.Candle.prove_hyp out fid r
             (candle_load_pth "candle$TRUTH")) end

    | CONJUNCT2_prf a => let
        val a_th = th a
        val concl = heap_concl a
        val (and_l, r_ptr) = heap_dest_comb concl
        val (_, l_ptr) = heap_dest_comb and_l
        val l_tm = tm l_ptr val r_tm = tm r_ptr
        val pth = candle_th (fn out => fn iid =>
          PFTWriter.Candle.inst out iid (candle_load_pth "candle$CONJUNCT2")
            [(pvar_p(), l_tm), (pvar_q(), r_tm)]) [l_tm, r_tm] []
      in emit_final (fn out =>
           PFTWriter.Candle.prove_hyp out result_id pth a_th) end

    (* === Pro-forma based: implication === *)
    | MP_prf (a, b) => let
        (* a: A ⊢ p ==> q,  b: B ⊢ p.  Result: A ∪ B ⊢ q *)
        val a_th = th a val b_th = th b
        val concl_a_id = tm (heap_concl a)
        val (imp_p_id, q_tm) = pft_dest_comb concl_a_id
        val (_, p_tm) = pft_dest_comb imp_p_id
        (* MP_rth: {p} ⊢ (p ==> q) = q *)
        val rth = candle_th (fn out => fn iid =>
          PFTWriter.Candle.inst out iid (candle_load_pth "candle$MP")
            [(pvar_p(), p_tm), (pvar_q(), q_tm)]) [p_tm, q_tm] []
        (* DEDUCT_ANTISYM b_th rth: B ⊢ p = ((p==>q)=q) *)
        val da = candle_th (fn out => fn iid =>
          PFTWriter.Candle.deduct_antisym_rule out iid b_th rth) [] [b_th, rth]
        (* EQ_MP da b_th: B ⊢ (p ==> q) = q *)
        val eq1 = candle_th (fn out => fn iid =>
          PFTWriter.Candle.eq_mp out iid da b_th) [] [da, b_th]
      in emit_final (fn out =>
           (* EQ_MP eq1 a_th: A ∪ B ⊢ q *)
           PFTWriter.Candle.eq_mp out result_id eq1 a_th) end

    | EQ_IMP_RULE1_prf a => let
        val a_th = th a
        val concl_id = tm (heap_concl a)
        val (eq_l_id, q_tm) = pft_dest_comb concl_id
        val (_, p_tm) = pft_dest_comb eq_l_id
        val pth = candle_th (fn out => fn iid =>
          PFTWriter.Candle.inst out iid (candle_load_pth "candle$EQ_IMP_RULE1")
            [(pvar_p(), p_tm), (pvar_q(), q_tm)]) [p_tm, q_tm] []
      in emit_final (fn out =>
           PFTWriter.Candle.prove_hyp out result_id pth a_th) end

    | EQ_IMP_RULE2_prf a => let
        val a_th = th a
        val concl_id = tm (heap_concl a)
        val (eq_l_id, q_tm) = pft_dest_comb concl_id
        val (_, p_tm) = pft_dest_comb eq_l_id
        val pth = candle_th (fn out => fn iid =>
          PFTWriter.Candle.inst out iid (candle_load_pth "candle$EQ_IMP_RULE2")
            [(pvar_p(), p_tm), (pvar_q(), q_tm)]) [p_tm, q_tm] []
      in emit_final (fn out =>
           PFTWriter.Candle.prove_hyp out result_id pth a_th) end

    | NOT_ELIM_prf a => let
        val a_th = th a
        val concl_id = tm (heap_concl a)
        val (_, p_tm) = pft_dest_comb concl_id
        val pth = candle_th (fn out => fn iid =>
          PFTWriter.Candle.inst out iid (candle_load_pth "candle$NOT_ELIM")
            [(pvar_p(), p_tm)]) [p_tm] []
      in emit_final (fn out =>
           PFTWriter.Candle.prove_hyp out result_id pth a_th) end

    | NOT_INTRO_prf a => let
        val a_th = th a
        (* conclusion is p ==> F, extract p *)
        val concl_id = tm (heap_concl a)
        val (imp_p_id, _) = pft_dest_comb concl_id
        val (_, p_tm) = pft_dest_comb imp_p_id
        val pth = candle_th (fn out => fn iid =>
          PFTWriter.Candle.inst out iid (candle_load_pth "candle$NOT_INTRO")
            [(pvar_p(), p_tm)]) [p_tm] []
      in emit_final (fn out =>
           PFTWriter.Candle.prove_hyp out result_id pth a_th) end

    (* === Pro-forma based: disjunction === *)
    | DISJ1_prf (a, b) => let
        (* a: A ⊢ p, b: term q. Result: A ⊢ p \/ q *)
        val a_th = th a val q_tm = tm b
        val p_tm = tm (heap_concl a)
        val pth = candle_th (fn out => fn iid =>
          PFTWriter.Candle.inst out iid (candle_load_pth "candle$DISJ1")
            [(pvar_p(), p_tm), (pvar_q(), q_tm)]) [p_tm, q_tm] []
      in emit_final (fn out =>
           PFTWriter.Candle.eq_mp out result_id
             (candle_th (fn out => fn iid =>
               PFTWriter.Candle.deduct_antisym_rule out iid a_th pth) [] [a_th, pth])
             a_th) end

    | DISJ2_prf (a, b) => let
        (* a: term p, b: A ⊢ q. Result: A ⊢ p \/ q *)
        val p_tm = tm a val b_th = th b
        val q_tm = tm (heap_concl b)
        val pth = candle_th (fn out => fn iid =>
          PFTWriter.Candle.inst out iid (candle_load_pth "candle$DISJ2")
            [(pvar_p(), p_tm), (pvar_q(), q_tm)]) [p_tm, q_tm] []
      in emit_final (fn out =>
           PFTWriter.Candle.eq_mp out result_id
             (candle_th (fn out => fn iid =>
               PFTWriter.Candle.deduct_antisym_rule out iid b_th pth) [] [b_th, pth])
             b_th) end

    (* === Multi-step: congruence === *)
    | Mk_comb_prf (a, b, c) => let
        (* a: ⊢ t = f x, b: ⊢ f = f', c: ⊢ x = x'
           Result: TRANS a (MK_COMB b c) = ⊢ t = f' x' *)
        val a_th = th a val b_th = th b val c_th = th c
        val mkcomb = candle_th (fn out => fn iid =>
          PFTWriter.Candle.mk_comb out iid b_th c_th) [] [b_th, c_th]
      in emit_final (fn out =>
           PFTWriter.Candle.trans out result_id a_th mkcomb) end

    | Mk_abs_prf (a, _, c) => let
        (* a: ⊢ t = λv. b, c: ⊢ b = b'
           Result: TRANS a (ABS v c) *)
        val a_th = th a val c_th = th c
        (* Get v from the RHS of a's conclusion: t = λv. b *)
        val concl_a = heap_concl a
        (* concl = (= t) (λv. b); heap_dest_comb gives ((= t), λv.b) *)
        val (_, lam_ptr) = heap_dest_comb concl_a
      in case shTerm heap lam_ptr of
           Abs (v_ptr, _) => let
             val v_tm = tm v_ptr
             val abs_th = candle_th (fn out => fn iid =>
               PFTWriter.Candle.abs out iid v_tm c_th) [v_tm] [c_th]
           in emit_final (fn out =>
                PFTWriter.Candle.trans out result_id a_th abs_th) end
         | _ => raise Fail "Mk_abs: RHS not an abstraction"
      end

    | Beta_prf a => let
        (* a: A ⊢ t = (λx. body) arg. Result: A ⊢ t = body[arg/x] *)
        (* TRANS a (beta_reduce ...) *)
        val a_th = th a
        val concl_a = heap_concl a
        val (_, rhs_ptr) = heap_dest_comb concl_a  (* rhs = (λx. body) arg *)
        val rhs_tm = tm rhs_ptr
        (* Candle BETA only works on (λx. body) x where arg = bound var.
           For the general case: construct (λx. body) x, BETA, INST x→arg.
           But we don't easily have the lambda and arg separately from PFT IDs.
           However, we CAN destructure from the heap. *)
        val (lam_ptr, arg_ptr) = heap_dest_comb rhs_ptr
      in case shTerm heap lam_ptr of
           Abs (var_ptr, _) => let
             val var_tm = tm var_ptr
             val lam_tm = tm lam_ptr
             val arg_tm = tm arg_ptr
             (* (λx. body) x *)
             val app_var = emit_comb lam_tm var_tm
             val beta_th = candle_th (fn out => fn iid =>
               PFTWriter.Candle.beta out iid app_var) [app_var] []
             val beta_inst = if var_tm = arg_tm then beta_th
               else candle_th (fn out => fn iid =>
                 PFTWriter.Candle.inst out iid beta_th
                   [(var_tm, arg_tm)]) [var_tm, arg_tm] [beta_th]
           in emit_final (fn out =>
                PFTWriter.Candle.trans out result_id a_th beta_inst) end
         | _ => raise Fail "Beta: RHS not an application of abstraction"
      end

    | BETA_CONV_prf a => let
        (* a: term (λx. body) arg. Result: ⊢ (λx. body) arg = body[arg/x] *)
        val (lam_ptr, arg_ptr) = heap_dest_comb a
      in case shTerm heap lam_ptr of
           Abs (var_ptr, _) => let
             val var_tm = tm var_ptr
             val lam_tm = tm lam_ptr
             val arg_tm = tm arg_ptr
             val app_var = emit_comb lam_tm var_tm
             val beta_th = candle_th (fn out => fn iid =>
               PFTWriter.Candle.beta out iid app_var) [app_var] []
           in if var_tm = arg_tm
              then emit_final (fn out =>
                PFTWriter.Candle.beta out result_id app_var)
              else emit_final (fn out =>
                PFTWriter.Candle.inst out result_id beta_th
                  [(var_tm, arg_tm)]) end
         | _ => raise Fail "BETA_CONV: not an application of abstraction"
      end

    | ALPHA_prf (t1, t2) => let
        val a = tm t1
        val concl_tm = tm concl_ptr  (* t1 = t2 *)
        val refl_a = candle_th (fn out => fn iid =>
          PFTWriter.Candle.refl out iid a) [a] []
      in emit_final (fn out =>
           PFTWriter.Candle.alpha_thm out result_id refl_a [] concl_tm) end

    (* === Remaining direct/simple === *)
    | DISCH_prf (a, b) => let
        (* a: term p, b: A ⊢ q. Result: A\{p} ⊢ p ==> q *)
        val p_tm = tm a val b_th = th b val q_tm = tm (heap_concl b)
        val r = do_DISCH p_tm q_tm b_th
      in candle_th_result (fn out => fn fid =>
           PFTWriter.Candle.prove_hyp out fid r
             (candle_load_pth "candle$TRUTH")) end

    | GEN_prf (a, b) => let
        (* a: term v, b: A ⊢ s. Result: A ⊢ ∀v. s *)
        val v_tm = tm a
        val b_th = th b
        val s_tm = tm (heap_concl b)
        val v_ty = ty (case shTerm heap a of
                          Fv (_, t) => t
                        | _ => raise Fail "GEN: variable expected")
        val r = do_GEN v_tm v_ty s_tm b_th
      in candle_th_result (fn out => fn fid =>
           PFTWriter.Candle.prove_hyp out fid r
             (candle_load_pth "candle$TRUTH")) end

    | GENL_prf (a, b) => let
        (* Iterated GEN. The conclusion is ∀v1...vn. s.
           Peel foralls from concl_ptr to get each intermediate conclusion,
           then fold GEN from innermost to outermost. *)
        val var_ptrs = list heap (fn p => p) a
        val inner_th = th b
        fun get_abs_body p = let
          val (_, lam) = heap_dest_comb p
        in case shTerm heap lam of
             Abs (_, body) => body
           | _ => raise Fail "GENL: expected abstraction under forall"
        end
        val n = length var_ptrs
        fun build_concls 0 _ = []
          | build_concls k c = c :: build_concls (k-1) (get_abs_body c)
        val outer_concls = build_concls n concl_ptr
        val inner_concl = heap_concl b
        val rev_vars = List.rev var_ptrs
        (* outer_concls = [∀v1...vn.s, ∀v2...vn.s, ..., ∀vn.s]
           rev_s_ptrs  = [s, ∀vn.s, ..., ∀v2...vn.s] (length n) *)
        val rev_s_ptrs = inner_concl :: List.rev outer_concls
        val gen_pairs = ListPair.zip (rev_vars, List.take (rev_s_ptrs, n))

        fun fold_gens [] th_acc = th_acc
          | fold_gens ((v_ptr, s_ptr) :: rest) th_acc = let
              val v_tm = tm v_ptr
              val s_tm = tm s_ptr
              val v_ty = ty (case shTerm heap v_ptr of
                              Fv (_, t) => t | _ => raise Fail "GENL: var expected")
            in fold_gens rest (do_GEN v_tm v_ty s_tm th_acc) end
        val r = fold_gens gen_pairs inner_th
      in candle_th_result (fn out => fn fid =>
           PFTWriter.Candle.prove_hyp out fid r
             (candle_load_pth "candle$TRUTH")) end

    | SPEC_prf (a, b) =>
        (* Same as Specialize — treat identically *)
        emit_thm_candle result_id concl_ptr (Specialize_prf (a, b))
          tm th ty mk_entry emit

    | Specialize_prf (a, b) => let
        (* a: term t, b: A ⊢ ∀v. s. Result: A ⊢ s[t/v] *)
        val t_tm = tm a
        val b_th = th b
        val concl_b = heap_concl b  (* ! (λv. s) *)
        val (_, pred_ptr) = heap_dest_comb concl_b
        val pred_tm = tm pred_ptr
        val forall_P_tm = tm concl_b
        val (var_ptr, _) = case shTerm heap pred_ptr of
            Abs (v, body) => (v, body)
          | _ => raise Fail "SPEC: predicate not an abstraction"
        val v_ty = ty (case shTerm heap var_ptr of
            Fv (_, t) => t | _ => raise Fail "SPEC: not a variable")
        val var_tm = tm var_ptr
        val r = do_SPEC t_tm pred_tm var_tm forall_P_tm v_ty b_th
      in candle_th_result (fn out => fn fid =>
           PFTWriter.Candle.prove_hyp out fid r
             (candle_load_pth "candle$TRUTH")) end

    | DISJ_CASES_prf (a, b, c) => let
        (* a: A ⊢ p ∨ q, b: B∪{p} ⊢ r, c: C∪{q} ⊢ r *)
        (* a: A ⊢ p ∨ q, b: B∪{p} ⊢ r, c: C∪{q} ⊢ r.
           DISJ_CASES_pth: {p ∨ q, p ==> r, q ==> r} ⊢ r. *)
        val a_th = th a val b_th = th b val c_th = th c
        val concl_a_id = tm (heap_concl a)
        val (or_p_id, q_tm) = pft_dest_comb concl_a_id
        val (_, p_tm) = pft_dest_comb or_p_id
        val r_tm = tm (heap_concl b)
        val pth = candle_th (fn out => fn iid =>
          PFTWriter.Candle.inst out iid (candle_load_pth "candle$DISJ_CASES")
            [(pvar_p(), p_tm), (pvar_q(), q_tm), (pvar_r(), r_tm)])
            [p_tm, q_tm, r_tm] []
        val th3 = candle_th (fn out => fn iid =>
          PFTWriter.Candle.eq_mp out iid
            (candle_th (fn out2 => fn iid2 =>
              PFTWriter.Candle.deduct_antisym_rule out2 iid2 a_th pth)
              [] [a_th, pth])
            a_th) [] [a_th, pth]
        val disch_l = do_DISCH p_tm r_tm b_th
        val disch_r = do_DISCH q_tm r_tm c_th
        val th4 = candle_th (fn out => fn iid =>
          PFTWriter.Candle.prove_hyp out iid th3 disch_l) [] [th3, disch_l]
      in emit_final (fn out =>
           PFTWriter.Candle.prove_hyp out result_id th4 disch_r) end

    | CCONTR_prf (a, b) => let
        (* a: term p, b: A ⊢ F. Result: A\{¬p} ⊢ p *)
        (* a: term p, b: A ⊢ F (with ¬p in A). Result: A\{¬p} ⊢ p.
           DISCH ¬p from b, then MP with CCONTR_pth. *)
        val p_tm = tm a val b_th = th b
        val neg_tm = emit_const "~" (emit_tyop "fun" [bool_tyid, bool_tyid])
        val neg_p = emit_comb neg_tm p_tm
        val const_F_tm = emit_const "F" bool_tyid
        val disch_th = do_DISCH neg_p const_F_tm b_th
        val ccontr_inst = candle_th (fn out => fn iid =>
          PFTWriter.Candle.inst out iid (candle_load_pth "candle$CCONTR")
            [(pvar_p(), p_tm)]) [p_tm] []
        val neg_p_imp_F = emit_comb (emit_comb (imp_const()) neg_p) const_F_tm
        val r = do_MP ccontr_inst neg_p_imp_F p_tm disch_th
      in candle_th_result (fn out => fn fid =>
           PFTWriter.Candle.prove_hyp out fid r
             (candle_load_pth "candle$TRUTH")) end

    | EXISTS_prf (a, b, c) => let
        (* a: ∃x. P x (the goal), b: witness term, c: A ⊢ P(witness).
           Result: A ⊢ ∃x. P x *)
        val c_th = th c
        val witness_tm = tm b
        val (_, pred_ptr) = heap_dest_comb a  (* ? applied to pred *)
        val pred_tm = tm pred_ptr
        val (var_ptr, _) = case shTerm heap pred_ptr of
            Abs (v, body) => (v, body)
          | _ => raise Fail "EXISTS: predicate not abstraction"
        val var_tm = tm var_ptr
        val v_ty = ty (heap_var_type var_ptr)
        (* Beta-reduce pred(witness) to match c_th's conclusion,
           then use do_EXISTS *)
        val beta_eq = do_beta_reduce pred_tm var_tm witness_tm
        val sym_beta = candle_th (fn out => fn iid =>
          PFTWriter.Candle.sym out iid beta_eq) [] [beta_eq]
        val th_pred_w = candle_th (fn out => fn iid =>
          PFTWriter.Candle.eq_mp out iid sym_beta c_th) [] [sym_beta, c_th]
        val r = do_EXISTS pred_tm var_tm witness_tm v_ty th_pred_w
      in candle_th_result (fn out => fn fid =>
           PFTWriter.Candle.prove_hyp out fid r
             (candle_load_pth "candle$TRUTH")) end

    | CHOOSE_prf (a, b, c) => let
        (* a: variable v, b: A ⊢ ∃x. P x, c: B∪{P v} ⊢ q.
           Result: A ∪ (B\{P v}) ⊢ q.
           CHOOSE_pth: ⊢ (?P) ==> (!x. Px ==> Q) ==> Q. *)
        val v_tm = tm a val b_th = th b val c_th = th c
        val q_tm = tm (heap_concl c)
        val concl_b = heap_concl b
        val (_, pred_ptr) = heap_dest_comb concl_b  (* pred from ?pred *)
        val pred_tm = tm pred_ptr
        val exists_P_tm = tm concl_b

        (* Get bound var of predicate *)
        val bv_ptr = case shTerm heap pred_ptr of
            Abs (v, _) => v | _ => raise Fail "CHOOSE: not abs"
        val bv_tm = tm bv_ptr
        val v_ty_ptr = heap_var_type bv_ptr
        val v_ty = ty v_ty_ptr

        (* cmb = pred(v), the beta-redex form of P(v).
           beta_v: ⊢ cmb = Pv (where Pv is the beta-normal form).
           Use PROVE_HYP to replace the Pv hypothesis in c_th with cmb,
           avoiding the need to construct Pv as a PFT term (which would
           require substitution into a de Bruijn body). *)
        val cmb = emit_comb pred_tm v_tm
        val beta_v = do_beta_reduce pred_tm bv_tm v_tm
        val assume_cmb = candle_th (fn out => fn iid =>
          PFTWriter.Candle.assume out iid cmb) [cmb] []
        (* th3: {cmb} ⊢ Pv *)
        val th3 = candle_th (fn out => fn iid =>
          PFTWriter.Candle.eq_mp out iid beta_v assume_cmb) [] [beta_v, assume_cmb]
        (* PROVE_HYP c_th th3: B ∪ {cmb} ⊢ q  (replaces Pv hyp with cmb) *)
        val c_with_cmb = candle_th (fn out => fn iid =>
          PFTWriter.Candle.prove_hyp out iid c_th th3) [] [c_th, th3]
        val disch_cmb = do_DISCH cmb q_tm c_with_cmb
        val imp_cmb_q = emit_comb (emit_comb (imp_const()) cmb) q_tm
        val gen_v = do_GEN v_tm v_ty imp_cmb_q disch_cmb

        (* INST CHOOSE_pth *)
        val choose_pth = candle_load_pth "candle$CHOOSE"
        val choose_ty = candle_th (fn out => fn iid =>
          PFTWriter.Candle.inst_type out iid choose_pth
            [(tyvar_A(), v_ty)]) [] [choose_pth]
        val Ab_v = emit_tyop "fun" [v_ty, bool_tyid]
        val var_P_v = emit_var "P" Ab_v
        val choose_inst = candle_th (fn out => fn iid =>
          PFTWriter.Candle.inst out iid choose_ty
            [(var_P_v, pred_tm), (pvar_Q(), q_tm)])
            [var_P_v, pred_tm, q_tm] [choose_ty]

        val lam_v_imp = emit_abs v_tm imp_cmb_q
        val forall_v_imp = emit_comb
          (emit_const "!" (emit_tyop "fun" [Ab_v, bool_tyid])) lam_v_imp
        val imp_forall_q = emit_comb (emit_comb (imp_const()) forall_v_imp) q_tm
        val mp_choose1 = do_MP choose_inst exists_P_tm imp_forall_q b_th
        val r = do_MP mp_choose1 forall_v_imp q_tm gen_v
      in candle_th_result (fn out => fn fid =>
           PFTWriter.Candle.prove_hyp out fid r
             (candle_load_pth "candle$TRUTH")) end

    | SUBST_prf (a, b, c) => let
        (* a: list of (var, thm) pairs where thm: Ai ⊢ si = si'
           b: template term (with vars marking substitution points)
           c: source theorem A ⊢ p where p = template[si/var_i]
           Result: A ∪ A1 ∪ ... ∪ An ⊢ p' where p' = template[si'/var_i]

           Strategy: build ⊢ p = p' by parallel traversal of p (source
           conclusion) and template, then EQ_MP with source theorem.
           Uses pft_dest_comb for Clos-safe structural traversal. *)
        val pairs = list heap (tuple2 heap (fn p => p, fn p => p)) a
        val template_ptr = b
        val c_th = th c

        (* Build substitution map: emit vars and thms, map var PFT ID → thm ID *)
        val subst_map : (int * int) list =
          List.map (fn (var_ptr, thm_ptr) =>
            (tm var_ptr, th thm_ptr)) pairs

        fun lookup_subst var_id =
          case List.find (fn (v, _) => v = var_id) subst_map of
            SOME (_, th_id) => SOME th_id
          | NONE => NONE

        (* Emit source conclusion and template, populating PFT structure *)
        val source_id = tm (heap_concl c)
        val template_id = tm template_ptr

        (* Recursive traversal: given PFT IDs for a source subterm and
           the corresponding template subterm, produce a theorem ID for
           ⊢ source_sub = result_sub.
           - If source = template (same PFT ID): REFL
           - If template is a substitution variable: use the equation thm
           - If both are COMBs: recurse on rator and rand, MK_COMB
           - If both are ABSs: recurse on body, ABS *)
        fun rconv src_id tmpl_id =
          if src_id = tmpl_id then
            (* Identical terms — REFL *)
            candle_th (fn out => fn iid =>
              PFTWriter.Candle.refl out iid src_id) [src_id] []
          else
            case lookup_subst tmpl_id of
              SOME th_id => th_id  (* substitution variable — use equation *)
            | NONE =>
              (* Try COMB *)
              let val (sf, sx) = pft_dest_comb src_id
                  val (tf, tx) = pft_dest_comb tmpl_id
                  val f_eq = rconv sf tf
                  val x_eq = rconv sx tx
              in candle_th (fn out => fn iid =>
                   PFTWriter.Candle.mk_comb out iid f_eq x_eq) [] [f_eq, x_eq]
              end
              handle Fail _ =>
              (* Try ABS *)
              let val (sv, sb) = pft_dest_abs src_id
                  val (tv, tb) = pft_dest_abs tmpl_id
                  (* The bound variables should match (same type).
                     Use the source's bound variable for ABS. *)
                  val body_eq = rconv sb tb
              in candle_th (fn out => fn iid =>
                   PFTWriter.Candle.abs out iid sv body_eq) [sv] [body_eq]
              end

        val eq_th = rconv source_id template_id
      in emit_final (fn out =>
           PFTWriter.Candle.eq_mp out result_id eq_th c_th) end

    | GEN_ABS_prf (a, b, c) => let
        (* a: optional constant, b: variable list, c: A ⊢ t1 = t2.
           Iterated ABS + optional AP_TERM for each variable. *)
        val opt_c = option heap tm a
        val vars = list heap tm b
        val c_th = th c
        fun fold_one (v_tm, th_acc, is_last) =
          let val abs_th =
                if is_last andalso opt_c = NONE
                then (emit_final (fn out =>
                        PFTWriter.Candle.abs out result_id v_tm th_acc);
                      result_id)
                else candle_th (fn out => fn iid =>
                       PFTWriter.Candle.abs out iid v_tm th_acc) [v_tm] [th_acc]
          in case opt_c of
               NONE => abs_th
             | SOME c_tm =>
                 if is_last
                 then let val refl_c = candle_th (fn out => fn iid =>
                            PFTWriter.Candle.refl out iid c_tm) [c_tm] []
                      in emit_final (fn out =>
                           PFTWriter.Candle.mk_comb out result_id refl_c abs_th);
                         result_id end
                 else let val refl_c = candle_th (fn out => fn iid =>
                            PFTWriter.Candle.refl out iid c_tm) [c_tm] []
                      in candle_th (fn out => fn iid =>
                           PFTWriter.Candle.mk_comb out iid refl_c abs_th)
                           [] [refl_c, abs_th] end
          end
        val rev_vars = List.rev vars
        fun loop [] acc = acc
          | loop [v] acc = fold_one (v, acc, true)
          | loop (v :: rest) acc = loop rest (fold_one (v, acc, false))
      in loop rev_vars c_th; () end

    (* === Definition commands === *)
    | Def_const_prf (a, b) => let
        (* a: rhs term, b: const ptr. Synthesize ASSUME(v = rhs) then
           new_specification. Same as emit_def_const but with Candle command. *)
        val rhs_id = emit_term a
        val (Thy, Name) = get_const_id b
        val ty_ptr = case shTerm heap b of
            Const (_, tp) => tp
          | _ => raise Fail "Def_const: expected Const"
        val rhs_ty_id = emit_type ty_ptr
        val bool_ty_c = emit_tyop "bool" []
        val fun_ty1 = emit_tyop "fun" [rhs_ty_id, bool_ty_c]
        val eq_ty = emit_tyop "fun" [rhs_ty_id, fun_ty1]
        val cname = tr_name (thyname ^ "$" ^ Name)
        val var_id = emit_var cname rhs_ty_id
        val eq_id = emit_const "=" eq_ty
        val eq_var = emit_comb eq_id var_id
        val eq_tm = emit_comb eq_var rhs_id
        val assume_id = candle_th (fn out => fn iid =>
          PFTWriter.Candle.assume out iid eq_tm) [eq_tm] []
        val () = mark_const Name
      in emit_final (fn out =>
           PFTWriter.Candle.new_specification out result_id assume_id
             [cname]) end

    | Def_const_list_prf (a, b) => let
        (* a: input theorem (with hypotheses v1=t1,...,vn=tn)
           b: list of constant ptrs giving the names.
           Map directly to new_specification. *)
        val a_th = th a
        val ids = list heap get_const_id b
        val names = List.map (fn (Thy,nm) => tr_name (Thy ^ "$" ^ nm)) ids
        val () = List.app (fn (_,nm) => mark_const nm) ids
      in emit_final (fn out =>
           PFTWriter.Candle.new_specification out result_id a_th names) end

    | Def_spec_prf (a, b) => let
        (* a: ⊢ ∃v1...vn. P, b: list of constant ptrs.
           Iteratively peel existentials using CHOOSE_pth + SELECT_AX,
           defining each constant via new_specification. *)
        (* Existential form: peel via @ then new_specification *)
        val const_ptrs = list heap (fn p => p) b

        val input_th = th a

        (* Get the PFT ID of the input conclusion, and the heap ptr for
           extracting bound variable info *)
        val input_concl_id = tm (heap_concl a)
        val input_concl_ptr = heap_concl a

        (* Peel one existential: from th_id: ⊢ ∃v. body, define constant c.
           exists_tm: PFT term ID of the ∃ conclusion.
           exists_ptr: heap ptr for shTerm access to the predicate.
           Returns (new_th_id, new_exists_tm) for the remaining theorem.
           new_exists_tm is the PFT ID of the new conclusion. *)
        fun peel_one th_id exists_tm exists_ptr const_ptr = let
          val (_, pred_id) = pft_dest_comb exists_tm

          (* Get heap pointer for pred to extract bound var info *)
          val (_, pred_ptr) = heap_dest_comb exists_ptr
          val (bv_ptr, _) = case shTerm heap pred_ptr of
              Abs (v, body) => (v, body)
            | _ => raise Fail "Def_spec: predicate not abstraction"
          val bv_ty_ptr = case shTerm heap bv_ptr of
              Fv (_, t) => t | _ => raise Fail "Def_spec: var expected"
          val v_ty = ty bv_ty_ptr

          (* Construct @ at the right type: (v_ty → bool) → v_ty *)
          val Ab = emit_tyop "fun" [v_ty, bool_tyid]
          val select_ty = emit_tyop "fun" [Ab, v_ty]
          val select_const = emit_const "@" select_ty
          val witness = emit_comb select_const pred_id  (* @pred *)

          (* Derive ⊢ pred(@pred) using CHOOSE_pth + SELECT_AX.
             CHOOSE_pth: ⊢ (?P) ⟹ (∀x. Px ⟹ Q) ⟹ Q
             SELECT_AX: ⊢ ∀P. ∀x. Px ⟹ P(@P)
             Strategy:
               INST_TYPE + INST SELECT_AX → ⊢ ∀x. pred(x) ⟹ pred(@pred)
               INST_TYPE + INST CHOOSE_pth with Q = pred(@pred)
               → ⊢ (?pred) ⟹ (∀x. pred(x) ⟹ pred(@pred)) ⟹ pred(@pred)
               MP with SELECT_AX result: ⊢ (?pred) ⟹ pred(@pred)
               MP with th_id: ⊢ pred(@pred) *)

          val pred_witness = emit_comb pred_id witness  (* pred(@pred) *)

          val sel_ax = candle_load_pth "candle$SELECT_AX"
          val sel_ty = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst_type out iid sel_ax
              [(tyvar_A(), v_ty)]) [] [sel_ax]
          val var_P_Ab = emit_var "P" Ab
          val sel_inst = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst out iid sel_ty
              [(var_P_Ab, pred_id)]) [var_P_Ab, pred_id] [sel_ty]

          val choose = candle_load_pth "candle$CHOOSE"
          val choose_ty = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst_type out iid choose
              [(tyvar_A(), v_ty)]) [] [choose]
          val choose_inst = candle_th (fn out => fn iid =>
            PFTWriter.Candle.inst out iid choose_ty
              [(var_P_Ab, pred_id), (pvar_Q(), pred_witness)])
              [var_P_Ab, pred_id, pred_witness] [choose_ty]

          (* Build ∀x.pred(x)⟹pred(@pred) as a term for MP *)
          val var_x_v = emit_var "x" v_ty
          val pred_x = emit_comb pred_id var_x_v
          val px_imp_pw = emit_comb (emit_comb (imp_const()) pred_x) pred_witness
          val lam_x_imp = emit_abs var_x_v px_imp_pw
          val forall_inner = emit_comb (emit_const "!" (emit_tyop "fun" [Ab, bool_tyid])) lam_x_imp

          (* MP choose_inst with th_id: need two MPs.
             First: MP choose_inst th_id → ⊢ (∀x...) ⟹ pred(@pred)
             Second: MP result sel_inst → ⊢ pred(@pred) *)
          val imp_forall_pw = emit_comb (emit_comb (imp_const()) forall_inner) pred_witness
          val mp1 = do_MP choose_inst exists_tm imp_forall_pw th_id
          val th_pred_witness = do_MP mp1 forall_inner pred_witness sel_inst

          (* Define constant: new_specification *)
          val (Thy, Name) = get_const_id const_ptr
          val cname = tr_name (Thy ^ "$" ^ Name)
          val c_var = emit_var cname v_ty
          val eq_ty = emit_tyop "fun" [v_ty, emit_tyop "fun" [v_ty, bool_tyid]]
          val eq_c = emit_const "=" eq_ty
          val c_eq_w = emit_comb (emit_comb eq_c c_var) witness
          val assume_ceq = candle_th (fn out => fn iid =>
            PFTWriter.Candle.assume out iid c_eq_w) [c_eq_w] []
          val () = mark_const Name
          val def_th = candle_th (fn out => fn iid =>
            PFTWriter.Candle.new_specification out iid assume_ceq [cname])
              [] [assume_ceq]

          (* Substitute c for @pred in the body:
             AP_TERM pred (SYM def_th): ⊢ pred(@pred) = pred(c)
             EQ_MP: ⊢ pred(c)
             Beta-reduce: ⊢ body[c/v] *)
          val sym_def = candle_th (fn out => fn iid =>
            PFTWriter.Candle.sym out iid def_th) [] [def_th]
          val ap_pred = candle_th (fn out => fn iid =>
            PFTWriter.Candle.mk_comb out iid
              (candle_th (fn out2 => fn iid2 =>
                PFTWriter.Candle.refl out2 iid2 pred_id) [pred_id] [])
              sym_def) [] [sym_def]
          val th_pred_c = candle_th (fn out => fn iid =>
            PFTWriter.Candle.eq_mp out iid ap_pred th_pred_witness)
              [] [ap_pred, th_pred_witness]

          val bv_tm = tm bv_ptr
          val beta_th = do_beta_reduce pred_id bv_tm (emit_const cname v_ty)
          val result = candle_th (fn out => fn iid =>
            PFTWriter.Candle.eq_mp out iid beta_th th_pred_c)
              [] [beta_th, th_pred_c]
          (* result: ⊢ body[c/v]
             The next exists_ptr for iteration is the body of pred *)
          val (_, body_ptr) = case shTerm heap pred_ptr of
              Abs (_, b) => (bv_ptr, b)
            | _ => raise Fail "Def_spec: pred not abs"
        in (result, body_ptr) end

        (* Iterate over all constants *)
        fun peel_all [] (th_acc, _) = th_acc
          | peel_all [last_c] (th_acc, ep) = let
              val (r, _) = peel_one th_acc (tm ep) ep last_c
            in r end
          | peel_all (c :: rest) (th_acc, ep) = let
              val (new_th, new_ep) = peel_one th_acc (tm ep) ep c
            in peel_all rest (new_th, new_ep) end
        val r = peel_all const_ptrs (input_th, input_concl_ptr)
      in candle_th_result (fn out => fn fid =>
           PFTWriter.Candle.prove_hyp out fid r
             (candle_load_pth "candle$TRUTH")) end
    | Def_tyop_prf (a, b, c) => let
        val _ = list heap ty a
        val () = if thyname = "bool"
                 then check_def tm_defs thyname "TYPE_DEFINITION" else ()
        val b_th = th b
        val (Thy, Tyop) = get_type_id c
        val () = mark_type Tyop
        val tyname = tr_name (Thy ^ "$" ^ Tyop)

        (* Step 1: exist-to-witness *)
        val (th_pw, pred_id, _, rep_ty, _, _) =
          exist_to_witness b_th (tm (heap_concl b)) (heap_concl b)
        val Ab = emit_tyop "fun" [rep_ty, bool_tyid]

        (* Step 2: new_type_definition *)
        val absname = tyname ^ "_abs"
        val repname = tyname ^ "_rep"
        val tydef_id = alloc_th ()
        val tydef_id2 = alloc_th ()
        val () = emit_th_def tydef_id {write = fn out =>
          PFTWriter.Candle.new_type_definition out tydef_id th_pw
            tyname absname repname,
          ref_ty = [], ref_tm = [], ref_th = [th_pw], ref_ci = []}
        val () = emit_th_def tydef_id2 {write = fn _ => (),
          ref_ty = [], ref_tm = [], ref_th = [], ref_ci = []}
        (* tydef_id: |- abs(rep a) = a, tydef_id2: |- phi r = (rep(abs r) = r) *)

        (* Step 3: bridge derivation *)
        val tyvars_ptrs = list heap (fn p => p) a
        val new_ty = emit_tyop tyname (List.map ty tyvars_ptrs)
        val abs_ty = emit_tyop "fun" [rep_ty, new_ty]
        val rep_fn_ty = emit_tyop "fun" [new_ty, rep_ty]
        val abs_c = emit_const absname abs_ty
        val rep_c = emit_const repname rep_fn_ty
        val Ab_new = emit_tyop "fun" [new_ty, bool_tyid]
        val eq_new = emit_const "=" (emit_tyop "fun" [new_ty, emit_tyop "fun" [new_ty, bool_tyid]])
        val eq_rep = emit_const "=" (emit_tyop "fun" [rep_ty, emit_tyop "fun" [rep_ty, bool_tyid]])

        val var_a = emit_var "a" new_ty
        val var_r_rep = emit_var "r" rep_ty
        val var_x_rep = emit_var "x" rep_ty
        val var_x' = emit_var "x'" new_ty
        val var_x'' = emit_var "x''" new_ty
        val rep_x' = emit_comb rep_c var_x'
        val rep_x'' = emit_comb rep_c var_x''
        val abs_x = emit_comb abs_c var_x_rep
        val phi_x = emit_comb pred_id var_x_rep

        (* Conjunct 1: injectivity. From |- abs(rep a) = a, derive
           |- !x' x''. rep x' = rep x'' ==> x' = x'' *)
        val ar_x' = candle_th (fn out => fn iid =>
          PFTWriter.Candle.inst out iid tydef_id
            [(var_a, var_x')]) [var_a, var_x'] [tydef_id]
        val ar_x'' = candle_th (fn out => fn iid =>
          PFTWriter.Candle.inst out iid tydef_id
            [(var_a, var_x'')]) [var_a, var_x''] [tydef_id]
        val rr = emit_comb (emit_comb eq_rep rep_x') rep_x''
        val assume_rr = candle_th (fn out => fn iid =>
          PFTWriter.Candle.assume out iid rr) [rr] []
        (* x' = abs(rep x') = abs(rep x'') = x'' via SYM, AP_TERM abs, TRANS *)
        val sym_ar_x' = candle_th (fn out => fn iid =>
          PFTWriter.Candle.sym out iid ar_x') [] [ar_x']
        val th_inj = candle_th (fn out => fn iid =>
          PFTWriter.Candle.trans out iid
            (candle_th (fn out2 => fn iid2 =>
              PFTWriter.Candle.trans out2 iid2 sym_ar_x'
                (do_AP_TERM abs_c assume_rr)) [] [sym_ar_x', assume_rr])
            ar_x'') [] [ar_x'']
        val x'_eq_x'' = emit_comb (emit_comb eq_new var_x') var_x''
        val inj_body = emit_comb (emit_comb (imp_const()) rr) x'_eq_x''
        val forall_new = emit_const "!" (emit_tyop "fun" [Ab_new, bool_tyid])
        val th_conj1 = do_GEN var_x' new_ty
          (emit_comb forall_new (emit_abs var_x'' inj_body))
          (do_GEN var_x'' new_ty inj_body (do_DISCH rr x'_eq_x'' th_inj))

        (* Conjunct 2: characterization. From |- phi r = (rep(abs r) = r), derive
           |- !x. phi x = ?x'. x = rep x' *)

        (* ra_x: |- phi x = (rep(abs x) = x) *)
        val ra_x = candle_th (fn out => fn iid =>
          PFTWriter.Candle.inst out iid tydef_id2
            [(var_r_rep, var_x_rep)]) [var_r_rep, var_x_rep] [tydef_id2]
        val sym_ra_x = candle_th (fn out => fn iid =>
          PFTWriter.Candle.sym out iid ra_x) [] [ra_x]
        val x_eq_rep_x' = emit_comb (emit_comb eq_rep var_x_rep) rep_x'
        val pred_exists = emit_abs var_x' x_eq_rep_x'
        val exist_x_eq = emit_comb
          (emit_const "?" (emit_tyop "fun" [Ab_new, bool_tyid]))
          pred_exists

        (* Forward: {phi x} |- ?x'. x = rep x' *)
        val th_rep_abs_x = candle_th (fn out => fn iid =>
          PFTWriter.Candle.eq_mp out iid sym_ra_x
            (candle_th (fn out2 => fn iid2 =>
              PFTWriter.Candle.assume out2 iid2 phi_x) [phi_x] []))
            [] [sym_ra_x]
        val sym_repabs = candle_th (fn out => fn iid =>
          PFTWriter.Candle.sym out iid th_rep_abs_x) [] [th_rep_abs_x]
        val beta_fwd = do_beta_reduce pred_exists var_x' abs_x
        val sym_beta_fwd = candle_th (fn out => fn iid =>
          PFTWriter.Candle.sym out iid beta_fwd) [] [beta_fwd]
        val witness_fwd = candle_th (fn out => fn iid =>
          PFTWriter.Candle.eq_mp out iid sym_beta_fwd sym_repabs)
            [] [sym_beta_fwd, sym_repabs]
        val th_fwd = do_EXISTS pred_exists var_x' abs_x new_ty witness_fwd
        val th_fwd_disch = do_DISCH phi_x exist_x_eq th_fwd

        (* Backward: {?x'. x = rep x'} |- phi x *)
        val assume_xeq = candle_th (fn out => fn iid =>
          PFTWriter.Candle.assume out iid x_eq_rep_x') [x_eq_rep_x'] []
        (* abs x = abs(rep x') = x' *)
        val abs_x_eq_x' = candle_th (fn out => fn iid =>
          PFTWriter.Candle.trans out iid (do_AP_TERM abs_c assume_xeq) ar_x')
            [] [assume_xeq, ar_x']
        (* rep(abs x) = rep x' then rep x' = x, so rep(abs x) = x *)
        val sym_xeq = candle_th (fn out => fn iid =>
          PFTWriter.Candle.sym out iid assume_xeq) [] [assume_xeq]
        val th_repabsx = candle_th (fn out => fn iid =>
          PFTWriter.Candle.trans out iid (do_AP_TERM rep_c abs_x_eq_x') sym_xeq)
            [] [abs_x_eq_x', sym_xeq]
        val th_phi_from_xeq = candle_th (fn out => fn iid =>
          PFTWriter.Candle.eq_mp out iid ra_x th_repabsx) [] [ra_x, th_repabsx]
        (* CHOOSE to discharge ?x'. x = rep x' *)
        val x_eq_imp_phi = emit_comb (emit_comb (imp_const()) x_eq_rep_x') phi_x
        val th_bwd = do_MP
          (do_MP
            (candle_th (fn out => fn iid =>
              PFTWriter.Candle.inst out iid
                (candle_th (fn out2 => fn iid2 =>
                  PFTWriter.Candle.inst_type out2 iid2 (candle_load_pth "candle$CHOOSE")
                    [(tyvar_A(), new_ty)]) [] [])
                [(emit_var "P" Ab_new, pred_exists), (pvar_Q(), phi_x)])
                [phi_x] [])
            exist_x_eq
            (emit_comb (emit_comb (imp_const())
              (emit_comb (emit_const "!" (emit_tyop "fun" [Ab_new, bool_tyid]))
                (emit_abs var_x' x_eq_imp_phi))) phi_x)
            (candle_th (fn out => fn iid =>
              PFTWriter.Candle.assume out iid exist_x_eq) [exist_x_eq] []))
          (emit_comb (emit_const "!" (emit_tyop "fun" [Ab_new, bool_tyid]))
            (emit_abs var_x' x_eq_imp_phi))
          phi_x
          (do_GEN var_x' new_ty x_eq_imp_phi
            (do_DISCH x_eq_rep_x' phi_x th_phi_from_xeq))

        (* Combine: |- phi x = ?x'. x = rep x' *)
        val th_fwd_u = do_MP th_fwd_disch phi_x exist_x_eq
          (candle_th (fn out => fn iid =>
            PFTWriter.Candle.assume out iid phi_x) [phi_x] [])
        val th_bwd_disch = do_DISCH exist_x_eq phi_x th_bwd
        val th_bwd_u = do_MP th_bwd_disch exist_x_eq phi_x
          (candle_th (fn out => fn iid =>
            PFTWriter.Candle.assume out iid exist_x_eq) [exist_x_eq] [])
        val th_char_x = candle_th (fn out => fn iid =>
          PFTWriter.Candle.deduct_antisym_rule out iid th_fwd_u th_bwd_u)
            [] [th_fwd_u, th_bwd_u]
        val phi_eq_exists = emit_comb (emit_comb (eq_bool_const()) phi_x) exist_x_eq
        val th_conj2 = do_GEN var_x_rep rep_ty phi_eq_exists th_char_x

        (* Assemble: CONJ, then use TYPE_DEFINITION_THM to get the result *)
        val forall_rep = emit_const "!" (emit_tyop "fun" [Ab, bool_tyid])
        val conj1_body = emit_comb forall_new
          (emit_abs var_x' (emit_comb forall_new (emit_abs var_x'' inj_body)))
        val conj2_body = emit_comb forall_rep (emit_abs var_x_rep phi_eq_exists)
        val conj_th = do_CONJ conj1_body conj2_body th_conj1 th_conj2

        (* SPEC TYPE_DEFINITION_THM at phi and rep_c *)
        val tydef_thm = candle_load_pth "bool$TYPE_DEFINITION_THM"
        val tydef_inst = candle_th (fn out => fn iid =>
          PFTWriter.Candle.inst_type out iid tydef_thm
            [(mk_tyvar_cached "'a", rep_ty),
             (mk_tyvar_cached "'b", new_ty)]) [] [tydef_thm]
        (* Build the body with generic P_v, rep_v for SPEC *)
        val var_P_v = emit_var "P" Ab
        val var_rep_v = emit_var "rep" rep_fn_ty
        val tydef_ty = emit_tyop "fun" [Ab, emit_tyop "fun" [rep_fn_ty, bool_tyid]]
        val tydef_c = emit_const "TYPE_DEFINITION" tydef_ty
        val rep_v_x' = emit_comb var_rep_v var_x'
        val rep_v_x'' = emit_comb var_rep_v var_x''
        val rr_v = emit_comb (emit_comb eq_rep rep_v_x') rep_v_x''
        val inj_inner_v = emit_abs var_x''
          (emit_comb (emit_comb (imp_const()) rr_v)
            (emit_comb (emit_comb eq_new var_x') var_x''))
        val inj_body_v = emit_comb forall_new
          (emit_abs var_x' (emit_comb forall_new inj_inner_v))
        val P_v_x = emit_comb var_P_v var_x_rep
        val exist_v = emit_comb (emit_const "?" (emit_tyop "fun" [Ab_new, bool_tyid]))
          (emit_abs var_x' (emit_comb (emit_comb eq_rep var_x_rep) rep_v_x'))
        val char_body_v = emit_comb forall_rep
          (emit_abs var_x_rep (emit_comb (emit_comb (eq_bool_const()) P_v_x) exist_v))
        val tydef_body_v = emit_comb (emit_comb (and_const()) inj_body_v) char_body_v
        val tydef_eq_v = emit_comb (emit_comb (eq_bool_const())
          (emit_comb (emit_comb tydef_c var_P_v) var_rep_v)) tydef_body_v
        val inner_lam = emit_abs var_rep_v tydef_eq_v
        val forall_rep_fn = emit_const "!"
          (emit_tyop "fun" [emit_tyop "fun" [rep_fn_ty, bool_tyid], bool_tyid])
        val inner_forall = emit_comb forall_rep_fn inner_lam
        val outer_lam = emit_abs var_P_v inner_forall
        val forall_Ab = emit_const "!"
          (emit_tyop "fun" [emit_tyop "fun" [Ab, bool_tyid], bool_tyid])
        val outer_forall = emit_comb forall_Ab outer_lam
        (* SPEC at phi, then at rep_c *)
        val spec1 = do_SPEC pred_id outer_lam var_P_v outer_forall Ab tydef_inst
        (* Build the inner pred after substituting phi for P_v *)
        val tydef_phi_rep = emit_comb (emit_comb tydef_c pred_id) var_rep_v
        val phi_x_v = emit_comb pred_id var_x_rep
        val exist_v2 = emit_comb (emit_const "?" (emit_tyop "fun" [Ab_new, bool_tyid]))
          (emit_abs var_x' (emit_comb (emit_comb eq_rep var_x_rep) rep_v_x'))
        val char_body_v2 = emit_comb forall_rep
          (emit_abs var_x_rep (emit_comb (emit_comb (eq_bool_const()) phi_x_v) exist_v2))
        val body_v2 = emit_comb (emit_comb (and_const()) inj_body_v) char_body_v2
        val eq_v2 = emit_comb (emit_comb (eq_bool_const()) tydef_phi_rep) body_v2
        val inner_lam2 = emit_abs var_rep_v eq_v2
        val inner_forall2 = emit_comb forall_rep_fn inner_lam2
        val spec2 = do_SPEC rep_c inner_lam2 var_rep_v inner_forall2 rep_fn_ty spec1

        (* EQ_MP (SYM spec2) conj_th: |- TYPE_DEFINITION phi rep_c *)
        val sym_spec2 = candle_th (fn out => fn iid =>
          PFTWriter.Candle.sym out iid spec2) [] [spec2]
        val tydef_proved = candle_th (fn out => fn iid =>
          PFTWriter.Candle.eq_mp out iid sym_spec2 conj_th) [] [sym_spec2, conj_th]

        (* EXISTS: |- ?rep. TYPE_DEFINITION phi rep *)
        val exist_pred_rep = emit_abs var_rep_v
          (emit_comb (emit_comb tydef_c pred_id) var_rep_v)
        val r = do_EXISTS exist_pred_rep var_rep_v rep_c rep_fn_ty tydef_proved
      in candle_th_result (fn out => fn fid =>
           PFTWriter.Candle.prove_hyp out fid r
             (candle_load_pth "candle$TRUTH")) end

    | compute_prf (a, b) => raise Fail "emit_thm_candle: compute not yet implemented"

    | save_dep_prf _ => raise Fail "unreachable"
    | deleted_prf => raise Fail "emit_thm_candle: deleted"
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
             val names = List.map (fn (Thy,nm) => tr_name (Thy ^ "$" ^ nm)) ids
             val () = List.app (fn (_,nm) => mark_const nm) ids
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
             val tms = list heap tm b
             val c = th c
           in case opt of
                SOME c_id => emit (mk_entry (fn out =>
                  PFTWriter.HOL4.gen_abs out id c c_id tms))
              | NONE => emit (mk_entry (fn out =>
                  PFTWriter.HOL4.absl out id c tms))
           end
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

  and emit_abs var_id body_id =
    case IntPairTable.lookup abs_ht (var_id, body_id) of
      SOME id => id
    | NONE => let val id = alloc_tm ()
      in emit_tm_def id {write = fn out => PFTWriter.abs out id var_id body_id,
               ref_ty = [], ref_tm = [var_id, body_id], ref_th = [], ref_ci = []};
         IntPairTable.insert abs_ht (var_id, body_id) id;
         tm_parts_set id (var_id, body_id); id
      end

  and emit_comb rator_id rand_id =
    case IntPairTable.lookup comb_ht (rator_id, rand_id) of
      SOME id => id
    | NONE => let val id = alloc_tm ()
      in emit_tm_def id {write = fn out => PFTWriter.comb out id rator_id rand_id,
               ref_ty = [], ref_tm = [rator_id, rand_id], ref_th = [], ref_ci = []};
         IntPairTable.insert comb_ht (rator_id, rand_id) id;
         tm_parts_set id (rator_id, rand_id); id
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
