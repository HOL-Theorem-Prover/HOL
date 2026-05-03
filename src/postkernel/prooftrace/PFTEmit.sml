structure PFTEmit :> PFTEmit = struct

open Lib Redblackset Redblackmap ProofTraceParser

datatype ruleset = HOL4 | Candle

val emit_expect : bool ref = ref false

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
    (* min theory - primitive types and constants *)
    ("min$bool", "bool"), ("min$fun", "fun"), ("min$ind", "ind"),
    ("min$=", "="), ("min$==>", "==>"), ("min$@", "@"),

    (* bool theory - logical connectives *)
    ("bool$T", "T"), ("bool$F", "F"),
    ("bool$/\\", "/\\"), ("bool$\\/", "\\/"),
    ("bool$~", "~"), ("bool$!", "!"), ("bool$?", "?"),
    ("bool$COND", "COND"), ("bool$LET", "LET"),
    ("bool$ONE_ONE", "ONE_ONE"), ("bool$ONTO", "ONTO"),

    (* num theory - natural number type and zero *)
    ("num$num", "num"),
    ("num$0", "_0"),
    ("num$SUC", "SUC"),

    (* prim_rec theory *)
    ("prim_rec$<", "<"),

    (* arithmetic theory - operations and numeral encoding *)
    ("arithmetic$+", "+"),
    ("arithmetic$-", "-"),
    ("arithmetic$*", "*"),
    ("arithmetic$DIV", "DIV"),
    ("arithmetic$MOD", "MOD"),
    ("arithmetic$NUMERAL", "NUMERAL"),
    ("arithmetic$ZERO", "_0"),       (* ZERO is an alias for 0 *)
    ("arithmetic$BIT1", "BIT1"),
    ("arithmetic$BIT2", "BIT2"),  (* kept for theorem loading; translated in compute *)

    (* cv theory - compute value type and operations *)
    ("cv$cv", "cval"),
    ("cv$Num", "Cexp_num"),
    ("cv$Pair", "Cexp_pair"),
    ("cv$cv_add", "Cexp_add"),
    ("cv$cv_sub", "Cexp_sub"),
    ("cv$cv_mul", "Cexp_mul"),
    ("cv$cv_div", "Cexp_div"),
    ("cv$cv_mod", "Cexp_mod"),
    ("cv$cv_lt", "Cexp_less"),
    ("cv$cv_if", "Cexp_if"),
    ("cv$cv_fst", "Cexp_fst"),
    ("cv$cv_snd", "Cexp_snd"),
    ("cv$cv_ispair", "Cexp_ispair"),
    ("cv$cv_eq", "Cexp_eq")
  ]
in
  fun candle_translate_name s =
    case List.find (fn (k,_) => k = s) candle_name_map of
      SOME (_, v) => v
    | NONE => s
end

(* When processing boolTheory in Candle mode, certain constants and axioms
   are already provided by the preamble.  Their definitions/axioms must be
   skipped and replaced by LOADs from the preamble.

   candle_preamble_def: maps the unqualified constant name (as it appears
     in the bool theory heap, e.g. "T") to the preamble SAVE name for
     the definition theorem that has the HOL4-compatible conclusion.

   candle_preamble_axiom: maps the axiom name string (from the trace) to
     the preamble SAVE name for the corresponding theorem. *)
val candle_preamble_def : (string * string) list = [
  ("T",       "candle$T_DEF"),
  ("/\\",     "candle$AND_DEF_HOL4"),
  ("!",       "candle$FORALL_DEF"),
  ("?",       "candle$EXISTS_DEF_HOL4"),
  ("\\/",     "candle$OR_DEF"),
  ("F",       "candle$F_DEF"),
  ("~",       "candle$NOT_DEF"),
  ("ONE_ONE", "candle$ONE_ONE_DEF"),
  ("ONTO",    "candle$ONTO_DEF")
]

val candle_preamble_axiom : (string * string) list = [
  ("SELECT_AX",     "candle$SELECT_AX"),
  ("ETA_AX",        "candle$ETA_AX"),
  ("BOOL_CASES_AX", "candle$BOOL_CASES_AX"),
  ("INFINITY_AX",   "candle$INFINITY_AX")
]

(* ========================================================================= *)
(* emit_theory                                                               *)
(* ========================================================================= *)

fun emit_theory {trace, output, binary, ruleset} = let
  val thyname = thyname_of_path trace
  val is_candle = case ruleset of Candle => true | HOL4 => false
  val tr_name = if is_candle then candle_translate_name else I
  val fun_tyname = tr_name "min$fun"
  val (root_ptr, heap) = parse trace
  val {all_thms, anon_thms, constants, types, ...} = shRoot heap root_ptr

  (* --- Walk pass --------------------------------------------------------- *)

  (* Collect free variable names matching the binder name pattern so that
     fresh_binder_name can avoid collisions with user-chosen names. *)
  val fv_binder_names : string set ref = ref (empty String.compare)
  val binder_infix = " pft%"
  fun is_binder_name s = String.isSubstring binder_infix s
  fun on_fv s = if is_binder_name s
                then fv_binder_names := add(!fv_binder_names, s)
                else ()

  val {tm_defs, ty_defs, is_closed, get_const_id, get_type_id} =
    ProofTraceWalk.walk
      {heap = heap, thyname = thyname,
       named_thms = all_thms, anon_thms = anon_thms,
       incr = K (), on_def_thm = K (),
       on_fv = on_fv}

  (* --- Free variable analysis for binder naming -------------------------- *)

  (* To avoid variable capture when using plain binder names, we need to know
     if the body of a lambda contains a free variable with the same (name, type)
     as the binder.  This analysis is memoized on heap term pointers.

     free_info computes:
     - fvs: set of (name, type_ptr) pairs for Fv nodes that are free
     - open_bvs: set of de Bruijn indices that escape (not yet bound/substituted)

     For top-level heap terms, open_bvs should be empty. It's only needed
     for intermediate computation through Clos nodes. *)

  type name_ty = string * Type.hol_type ptr
  fun name_ty_cmp ((s1, t1): name_ty, (s2, t2): name_ty) =
    case String.compare(s1, s2) of
      EQUAL => Int.compare(ptr t1, ptr t2)
    | x => x

  type free_info = { fvs: name_ty set, open_bvs: int set }
  val empty_fi : free_info =
    { fvs = Redblackset.empty name_ty_cmp,
      open_bvs = Redblackset.empty Int.compare }

  fun merge_fi ({fvs = fvs1, open_bvs = ob1}: free_info,
                {fvs = fvs2, open_bvs = ob2}: free_info) : free_info =
    { fvs = Redblackset.union(fvs1, fvs2),
      open_bvs = Redblackset.union(ob1, ob2) }

  (* Memoization table for free_info, keyed by heap term pointer *)
  val fi_memo : free_info option array = Array.array(heapSize heap, NONE)

  (* Trace a de Bruijn index through a heap substitution.
     Returns (k, SOME t) if index maps to term t shifted by k,
     or (k, NONE) if index maps to de Bruijn index k. *)
  fun exp_rel_heap (subst_ptr: Term.term Subst.subs ptr, n: int)
      : int * Term.term ptr option =
    case shSubs heap subst_ptr of
      Id => (n, NONE)
    | Cons (s', t) =>
        if n = 0 then (0, SOME t)
        else exp_rel_heap(s', n - 1)
    | Shift (k, s') =>
        let val (m, r) = exp_rel_heap(s', n)
        in (m + k, r) end
    | Lift (k, s') =>
        if n < k then (n, NONE)
        else let val (m, r) = exp_rel_heap(s', n - k)
             in (m + k, r) end

  (* Compute free variable info for a heap term *)
  fun free_info_of (tm_ptr: Term.term ptr) : free_info =
    if not (isPtr tm_ptr) then empty_fi
    else let val k = ptr tm_ptr
    in case Array.sub(fi_memo, k) of
         SOME fi => fi
       | NONE => let val fi = free_info_compute tm_ptr
                 in Array.update(fi_memo, k, SOME fi); fi end
    end

  and free_info_compute (tm_ptr: Term.term ptr) : free_info =
    case shTerm heap tm_ptr of
      Fv (s, typ) =>
        { fvs = Redblackset.singleton name_ty_cmp (s, typ),
          open_bvs = Redblackset.empty Int.compare }
    | Bv n =>
        { fvs = Redblackset.empty name_ty_cmp,
          open_bvs = Redblackset.singleton Int.compare n }
    | Const _ => empty_fi
    | Comb (t1, t2) => merge_fi(free_info_of t1, free_info_of t2)
    | Abs (v, body) =>
        let val {fvs, open_bvs} = free_info_of body
            (* decrement open indices > 0, drop index 0 (now bound) *)
            val open_bvs' = Redblackset.foldl (fn (n, acc) =>
                              if n = 0 then acc
                              else Redblackset.add(acc, n - 1))
                            (Redblackset.empty Int.compare) open_bvs
        in {fvs = fvs, open_bvs = open_bvs'} end
    | Clos (subst, t) =>
        let val {fvs, open_bvs} = free_info_of t
            (* Trace each open index through the substitution *)
            val (fvs', open_bvs') =
              Redblackset.foldl (fn (n, (fvs_acc, ob_acc)) =>
                case exp_rel_heap(subst, n) of
                  (k, NONE) => (fvs_acc, Redblackset.add(ob_acc, k))
                | (k, SOME t') =>
                    let val {fvs = fvs_t, open_bvs = ob_t} = free_info_of t'
                        (* shift open indices from t' by k *)
                        val ob_t_shifted = Redblackset.foldl
                                             (fn (m, acc) => Redblackset.add(acc, m + k))
                                             (Redblackset.empty Int.compare) ob_t
                    in (Redblackset.union(fvs_acc, fvs_t),
                        Redblackset.union(ob_acc, ob_t_shifted)) end)
              (fvs, Redblackset.empty Int.compare) open_bvs
        in {fvs = fvs', open_bvs = open_bvs'} end

  (* --- Axiom name pre-scan ----------------------------------------------- *)

  (* Build a map from heap pointer to axiom name by scanning named exports.
     This allows us to emit AXIOM commands with correct names immediately,
     without deferred writes. *)
  val axiom_name_map : string PIntMap.t = let
    val m = ref PIntMap.empty
    fun chase thp =
      let val (_, _, proof_ptr) = shThm heap thp
      in case shProof heap proof_ptr of
           save_dep_prf inner => chase inner
         | Axiom_prf => SOME thp
         | _ => NONE
      end
  in appList heap (fn p => let
       val (nm, (thp, _)) = tuple3 heap (str heap, I, I) p
     in case chase thp of
          SOME ax => m := PIntMap.add (ptr ax) nm (!m)
        | NONE => ()
     end) all_thms;
     !m
  end

  (* Build a map from export name to theorem heap pointer.  Only needed
     for boolTheory in Candle mode, where Def_tyop_prf must reference
     TYPE_DEFINITION_THM from within the same theory without LOAD/SAVE. *)
  val named_thm_map : (string, Thm.thm ptr) Redblackmap.dict =
    if is_candle andalso thyname = "bool" then let
      val m = ref (Redblackmap.mkDict String.compare)
    in appList heap (fn p => let
         val (nm, (thp, _)) = tuple3 heap (str heap, I, I) p
       in m := Redblackmap.insert(!m, nm, thp) end) all_thms;
       !m
    end
    else Redblackmap.mkDict String.compare

  (* --- Open output ------------------------------------------------------- *)

  val ruleset_str = case ruleset of HOL4 => "hol4" | Candle => "candle"
  val out = PFTWriter.openOut
    {file = output, binary = binary, version = "0.1.0", ruleset = ruleset_str}

  (* --- Emit pass state --------------------------------------------------- *)

  (* ID counters *)
  val next_ty = ref 0
  val next_tm = ref 0
  val next_th = ref 0

  fun alloc_ty () = let val id = !next_ty in next_ty := id + 1; id end
  fun alloc_tm () = let val id = !next_tm in next_tm := id + 1; id end
  fun alloc_th () = let val id = !next_th in next_th := id + 1; id end

  (* --- Pointer memos ----------------------------------------------------- *)

  val tm_memo = Array.array(heapSize heap, ~1)
                (* heap ptr -> PFT term ID; hot path, flat array *)
  val ty_memo : int PIntMap.t ref = ref PIntMap.empty
  val th_memo : int PIntMap.t ref = ref PIntMap.empty
  val hol4_compute_init_key = ref ~1

  fun ty_memo_get k = PIntMap.find k (!ty_memo)
                      handle PIntMap.NotFound => ~1
  fun ty_memo_set k v = ty_memo := PIntMap.add k v (!ty_memo)
  fun th_memo_get k = PIntMap.find k (!th_memo)
                      handle PIntMap.NotFound => ~1
  fun th_memo_set k v = th_memo := PIntMap.add k v (!th_memo)

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

  (* Reverse lookup: PFT term ID -> subterm IDs.
     Populated by emit_comb/emit_abs. Enables Clos-safe destructuring
     of PFT terms by ID, without traversing the heap.
     Entries for non-COMB/ABS terms are (~1, ~1). *)
  val tm_part1 = DArray.new(65536, ~1)  (* rator or var *)
  val tm_part2 = DArray.new(65536, ~1)  (* rand or body *)

  fun tm_parts_ensure id = let
    val sz = DArray.size tm_part1
    fun pad 0 = () | pad n = (DArray.push(tm_part1, ~1);
                               DArray.push(tm_part2, ~1); pad (n - 1))
  in if id < sz then () else pad (id - sz + 1)
  end

  fun tm_parts_set id (x, y) =
    (tm_parts_ensure id;
     DArray.update(tm_part1, id, x);
     DArray.update(tm_part2, id, y))

  fun pft_dest_comb id =
    let val f = DArray.sub(tm_part1, id)
        val x = DArray.sub(tm_part2, id)
    in if f >= 0 then (f, x)
       else raise Fail ("pft_dest_comb: term " ^ Int.toString id ^
                         " is not a COMB/ABS")
    end

  fun pft_dest_abs id = pft_dest_comb id  (* same layout: (var, body) *)

  (* Discriminates COMB from ABS: COMBs are registered in comb_ht by
     emit_comb; ABSs never are.  Only needed by callers that genuinely
     need to tell the two apart (e.g. SUBST_prf's rconv); all other
     call sites know the kind from the surrounding proof-rule invariant
     and can use pft_dest_comb / pft_dest_abs directly. *)
  fun tm_part1_of id =
    if id < DArray.size tm_part1 then DArray.sub(tm_part1, id) else ~1
  fun tm_part2_of id =
    if id < DArray.size tm_part2 then DArray.sub(tm_part2, id) else ~1

  fun pft_is_comb id =
    let val f = tm_part1_of id
        val x = tm_part2_of id
    in f >= 0 andalso isSome (IntPairTable.lookup comb_ht (f, x))
    end

  (* Reverse lookup: PFT term ID -> PFT type ID.
     Populated for all emitted terms (Var, Const, Comb, Abs). *)
  val tm_types = DArray.new(65536, ~1)

  fun tm_types_ensure id = let
    val sz = DArray.size tm_types
    fun pad 0 = () | pad n = (DArray.push(tm_types, ~1); pad (n - 1))
  in if id < sz then () else pad (id - sz + 1)
  end

  fun tm_types_set id ty_id =
    (tm_types_ensure id; DArray.update(tm_types, id, ty_id))

  fun pft_type_of id =
    let val ty_id = DArray.sub(tm_types, id)
    in if ty_id >= 0 then ty_id
       else raise Fail ("pft_type_of: term " ^ Int.toString id ^
                         " has no recorded type")
    end

  (* Reverse lookup: PFT type ID -> return type ID (for function types). *)
  val ty_ret = DArray.new(4096, ~1)

  fun ty_ret_ensure id = let
    val sz = DArray.size ty_ret
    fun pad 0 = () | pad n = (DArray.push(ty_ret, ~1); pad (n - 1))
  in if id < sz then () else pad (id - sz + 1)
  end

  fun ty_ret_set id ret_id =
    (ty_ret_ensure id; DArray.update(ty_ret, id, ret_id))

  fun pft_ret_type id =
    let val r = DArray.sub(ty_ret, id)
    in if r >= 0 then r
       else raise Fail ("pft_ret_type: type " ^ Int.toString id ^
                         " is not a function type")
    end

  (* Reverse lookup: PFT VAR term ID -> name.
     Populated by emit_var and emit_binder. *)
  val var_names : string DArray.darray = DArray.new(4096, "")

  fun var_names_ensure id = let
    val sz = DArray.size var_names
    fun pad 0 = () | pad n = (DArray.push(var_names, ""); pad (n - 1))
  in if id < sz then () else pad (id - sz + 1)
  end

  fun var_names_set id name =
    (var_names_ensure id; DArray.update(var_names, id, name))

  fun var_name_of id =
    if id < DArray.size var_names then DArray.sub(var_names, id)
    else ""

  (* Memoized free variable computation for PFT terms.
     Returns set of (name, type_id) pairs free in the term. *)
  type name_ty_pft = string * int
  fun name_ty_pft_cmp ((s1, t1): name_ty_pft, (s2, t2): name_ty_pft) =
    case String.compare(s1, s2) of
      EQUAL => Int.compare(t1, t2)
    | x => x
  type fv_set = name_ty_pft Redblackset.set
  val empty_fv_set : fv_set = Redblackset.empty name_ty_pft_cmp

  val pft_fv_memo : fv_set option DArray.darray = DArray.new(65536, NONE)

  fun pft_fv_memo_ensure id = let
    val sz = DArray.size pft_fv_memo
    fun pad 0 = () | pad n = (DArray.push(pft_fv_memo, NONE); pad (n - 1))
  in if id < sz then () else pad (id - sz + 1)
  end

  fun pft_free_vars (id: int) : fv_set =
    (pft_fv_memo_ensure id;
     case DArray.sub(pft_fv_memo, id) of
       SOME fvs => fvs
     | NONE => let val fvs = pft_free_vars_compute id
               in DArray.update(pft_fv_memo, id, SOME fvs); fvs end)

  and pft_free_vars_compute (id: int) : fv_set =
    let val p1 = if id < DArray.size tm_part1 then DArray.sub(tm_part1, id) else ~1
        val p2 = if id < DArray.size tm_part2 then DArray.sub(tm_part2, id) else ~1
    in if p1 < 0 then
         (* VAR or CONST: check if it's a VAR by looking up var_names *)
         let val name = var_name_of id
         in if name = "" then empty_fv_set  (* CONST *)
            else Redblackset.singleton name_ty_pft_cmp (name, pft_type_of id)
         end
       else if isSome (IntPairTable.lookup comb_ht (p1, p2)) then
         (* COMB *)
         Redblackset.union(pft_free_vars p1, pft_free_vars p2)
       else
         (* ABS: p1 is binder VAR, p2 is body *)
         let val binder_name = var_name_of p1
             val binder_ty = pft_type_of p1
             val body_fvs = pft_free_vars p2
         in Redblackset.delete(body_fvs, (binder_name, binder_ty))
            handle Redblackset.NotFound => body_fvs
         end
    end

  fun var_lookup key = peek(!var_ht, key)
  fun var_insert key v = var_ht := insert(!var_ht, key, v)
  fun const_lookup key = peek(!const_ht, key)
  fun const_insert key v = const_ht := insert(!const_ht, key, v)

  (* --- Unique binder names for Abs capture avoidance ---------------------- *)

  val binder_ctr = ref 0
  fun fresh_binder_name s = let
    fun try () = let
      val n = !binder_ctr
      val () = binder_ctr := n + 1
      val candidate = s ^ binder_infix ^ Int.toString n
    in if member(!fv_binder_names, candidate) then try ()
       else candidate
    end
  in try () end

  (* --- NEW_CONST / NEW_TYPE tracking ------------------------------------- *)

  val const_done : string set ref = ref (empty String.compare)
  val type_done : string set ref = ref (empty String.compare)
  fun mark_const name = const_done := add(!const_done, name)
  fun mark_type name = type_done := add(!type_done, name)
  fun is_const_done name = member(!const_done, name)
  fun is_type_done name = member(!type_done, name)

  (* ======================================================================= *)
  (* Candle pro-forma theorem IDs (lazy-loaded on first use)                 *)
  (* ======================================================================= *)

  val candle_pths : (string, int) dict ref = ref (mkDict String.compare)

  fun candle_load_pth name =
    case peek(!candle_pths, name) of
      SOME id => id
    | NONE => let
        val id = alloc_th ()
      in PFTWriter.load out id name;
         candle_pths := insert(!candle_pths, name, id);
         id
      end

  (* Pro-forma theorems are loaded lazily by candle_load_pth on first use. *)

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
           in PFTWriter.tyvar out id s;
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
                            PFTWriter.new_type out name (length arg_ids))
                      else ()
             val id = alloc_ty ()
           in PFTWriter.tyop out id name arg_ids;
              ty_insert key id;
              ty_memo_set k id;
              (case arg_ids of
                 [_, r] => if name = fun_tyname then ty_ret_set id r else ()
               | _ => ());
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
       Array.update(tm_memo, k, id);
       id
     end
  end

  (* Check if using binder name s with type ty_id would capture a free variable
     in the heap term tm_ptr, given the current substitution environment env.
     
     A capture occurs if:
     1. The heap term contains Fv(s, typ) where emit_type(typ) = ty_id, OR
     2. The heap term has an escaping de Bruijn index n > 0 that resolves
        (via env) to a PFT term containing (s, ty_id) free. *)
  and would_capture (s: string, ty_id: int) (env: int Subst.subs) (tm_ptr: Term.term ptr) : bool =
    let val {fvs, open_bvs} = free_info_of tm_ptr
        (* Check heap fvs: any Fv with same name and type? *)
        val heap_conflict = isSome (Redblackset.find
          (fn (s', typ') => s = s' andalso emit_type typ' = ty_id) fvs)
        (* Check env: for escaping indices n > 0, does env map them to
           PFT terms containing (s, ty_id) free? 
           Note: n=0 will refer to our new binder, so we only check n > 0 *)
        fun env_conflict n =
          if n = 0 then false
          else case Subst.exp_rel(env, n - 1) of
                 (_, SOME tm_id) => Redblackset.member(pft_free_vars tm_id, (s, ty_id))
               | (_, NONE) => false  (* still unresolved, no conflict from env *)
        val env_has_conflict = isSome (Redblackset.find env_conflict open_bvs)
    in heap_conflict orelse env_has_conflict end

  and emit_term_core env (tm_ptr : Term.term ptr) : int =
    case shTerm heap tm_ptr of
      Fv (s, typ) => let
        val ty_id = emit_type typ
        val key = (s, ty_id)
      in case var_lookup key of
           SOME id => id
         | NONE => let
             val id = alloc_tm ()
           in PFTWriter.var out id s ty_id;
              var_insert key id;
              tm_types_set id ty_id;
              var_names_set id s;
              id
           end
      end
    | Const (idp, typ) => let
        val (Thy, Name) = ident heap idp
        val () = check_def tm_defs Thy Name
        val ty_id = emit_type typ
        val qname = tr_name (Thy ^ "$" ^ Name)
        val () = if Thy = thyname andalso not (is_const_done qname)
                 then (mark_const qname;
                       PFTWriter.new_const out qname ty_id)
                 else ()
        val key = (qname, ty_id)
      in case const_lookup key of
           SOME id => id
         | NONE => let
             val id = alloc_tm ()
           in PFTWriter.const out id qname ty_id;
              const_insert key id;
              tm_types_set id ty_id;
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
           in PFTWriter.comb out id id1 id2;
              IntPairTable.insert comb_ht (id1, id2) id;
              tm_parts_set id (id1, id2);
              tm_types_set id (pft_ret_type (pft_type_of id1));
              id
           end
      end
    | Abs (t1, t2) => let
        val (s, typ) = resolve_binder_name t1
        val ty_id = emit_type typ
        val V = alloc_tm ()
        (* Use plain name if it won't capture a free variable in the body;
           otherwise use a unique " pft%" name to avoid capture. *)
        val bname = if would_capture (s, ty_id) env t2
                    then fresh_binder_name s
                    else s
        val () = PFTWriter.var out V bname ty_id
        val () = tm_types_set V ty_id
        val () = var_names_set V bname
        val body_id = emit_term_sub (Subst.cons(env, V)) t2
        val A = alloc_tm ()
      in
        PFTWriter.abs out A V body_id;
        tm_parts_set A (V, body_id);
        tm_types_set A (emit_tyop fun_tyname [ty_id, pft_type_of body_id]);
        A
      end
    | Clos (sbp, tmp) => let
        val env' = Subst.comp #2 (env, emit_subs env sbp)
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
  (* Candle: heap helper                                                     *)
  (* ======================================================================= *)

  (* Get the conclusion pointer of a theorem from the heap *)
  and heap_concl (thm_ptr : Thm.thm ptr) =
    let val (_, concl, _) = shThm heap thm_ptr in concl end

  (* ======================================================================= *)
  (* Candle theorem dispatch                                                 *)
  (* Emits Candle-ruleset commands for each HOL4 proof constructor.          *)
  (* For derived rules, uses pro-formas from the preamble via                *)
  (* INST + PROVE_HYP.                                                      *)
  (* ======================================================================= *)

  and emit_thm_candle result_id concl_ptr proof = let
    val tm = emit_term
    val th = emit_thm
    val ty = emit_type

    (* --- Per-rule Candle wrappers ---------------------------------------- *)
    (* Each allocates a fresh theorem ID, writes the command, returns the ID.*)

    fun c_refl a           = let val id = alloc_th () in PFTWriter.Candle.refl out id a; id end
    fun c_trans a b        = let val id = alloc_th () in PFTWriter.Candle.trans out id a b; id end
    fun c_mk_comb a b      = let val id = alloc_th () in PFTWriter.Candle.mk_comb out id a b; id end
    fun c_abs v th         = let val id = alloc_th () in PFTWriter.Candle.abs_thm out id v th; id end
    fun c_beta a           = let val id = alloc_th () in PFTWriter.Candle.beta out id a; id end
    fun c_assume a         = let val id = alloc_th () in PFTWriter.Candle.assume out id a; id end
    fun c_eq_mp a b        = let val id = alloc_th () in PFTWriter.Candle.eq_mp out id a b; id end
    fun c_deduct a b       = let val id = alloc_th () in PFTWriter.Candle.deduct_antisym_rule out id a b; id end
    fun c_inst th ps       = let val id = alloc_th () in PFTWriter.Candle.inst out id th ps; id end
    fun c_inst_type th ps  = let val id = alloc_th () in PFTWriter.Candle.inst_type out id th ps; id end
    fun c_sym a            = let val id = alloc_th () in PFTWriter.Candle.sym out id a; id end
    fun c_prove_hyp a b    = let val id = alloc_th () in PFTWriter.Candle.prove_hyp out id a b; id end
    fun c_new_spec a ns    = let val id = alloc_th () in PFTWriter.Candle.new_specification out id a ns; id end

    (* Write a command to the pre-allocated result_id (for the final step). *)
    fun r_refl a           = (PFTWriter.Candle.refl out result_id a; result_id)
    fun r_trans a b        = (PFTWriter.Candle.trans out result_id a b; result_id)
    fun r_mk_comb a b      = (PFTWriter.Candle.mk_comb out result_id a b; result_id)
    fun r_abs v th         = (PFTWriter.Candle.abs_thm out result_id v th; result_id)
    fun r_beta a           = (PFTWriter.Candle.beta out result_id a; result_id)
    fun r_assume a         = (PFTWriter.Candle.assume out result_id a; result_id)
    fun r_eq_mp a b        = (PFTWriter.Candle.eq_mp out result_id a b; result_id)
    fun r_deduct a b       = (PFTWriter.Candle.deduct_antisym_rule out result_id a b; result_id)
    fun r_inst th ps       = (PFTWriter.Candle.inst out result_id th ps; result_id)
    fun r_inst_type th ps  = (PFTWriter.Candle.inst_type out result_id th ps; result_id)
    fun r_sym a            = (PFTWriter.Candle.sym out result_id a; result_id)
    fun r_prove_hyp a b    = (PFTWriter.Candle.prove_hyp out result_id a b; result_id)

    (* Preamble variable term IDs — memoized via emit_var hash-cons *)
    val bool_tyid = emit_tyop "bool" []
    val pvar_p = emit_var "p" bool_tyid
    val pvar_q = emit_var "q" bool_tyid
    val pvar_t = emit_var "t" bool_tyid
    val pvar_r = emit_var "r" bool_tyid
    val pvar_Q = emit_var "Q" bool_tyid

    (* Candle equality constant at bool type — for building eq terms *)
    val bbb_tyid = emit_tyop "fun" [bool_tyid, emit_tyop "fun" [bool_tyid, bool_tyid]]
    val eq_bool_const = emit_const "=" bbb_tyid

    (* Candle /\ constant *)
    val and_const = emit_const "/\\" bbb_tyid

    (* Candle ==> constant *)
    val imp_const = emit_const "==>" bbb_tyid

    (* Candle F constant *)
    val const_F_tm = emit_const "F" bool_tyid

    (* mk_tyvar_cached: get or create a type variable by name *)
    fun mk_tyvar_cached name = let val key = TyVarK name
      in case ty_lookup key of SOME id => id
       | NONE => let val id = alloc_ty ()
         in PFTWriter.tyvar out id name;
            ty_insert key id; id end end

    (* Type variable 'a: the polymorphic parameter of the preamble
       pro-formas (GEN, SPEC, EXISTS, CHOOSE, SELECT_AX_SPEC,
       EXISTS_DEF_HOL4, TYPE_DEFINITION_THM). Matches HOL4's native
       type-variable naming. *)
    val tyvar_A = mk_tyvar_cached "'a"
    val tyvar_B = mk_tyvar_cached "'b"

    (* === Candle derived-rule helpers ===
       These emit sequences of Candle commands and return theorem IDs. *)

    (* do_MP: from ith: ⊢ a ==> b and th: ⊢ a, derive ⊢ b.
       Uses MP_rth = {p} ⊢ (p ==> q) = q. *)
    fun do_MP ith a_tm b_tm ant_th =
      let val rth = c_inst (candle_load_pth "candle$MP")
                      [(pvar_p, a_tm), (pvar_q, b_tm)]
      in c_eq_mp (c_eq_mp (c_deduct ant_th rth) ant_th) ith end

    (* do_CONJ: from th1: A ⊢ a and th2: B ⊢ b, derive A ∪ B ⊢ a ∧ b *)
    fun do_CONJ a_tm b_tm th1 th2 =
      let val ci = c_inst (candle_load_pth "candle$CONJ")
                     [(pvar_p, a_tm), (pvar_q, b_tm)]
      in c_prove_hyp th2 (c_prove_hyp th1 ci) end

    (* do_CONJUNCT1: from th: A ⊢ a ∧ b, derive A ⊢ a *)
    fun do_CONJUNCT1 a_tm b_tm th =
      c_prove_hyp th (c_inst (candle_load_pth "candle$CONJUNCT1")
                     [(pvar_p, a_tm), (pvar_q, b_tm)])

    (* do_CONJUNCT2: from th: A ⊢ a ∧ b, derive A ⊢ b *)
    fun do_CONJUNCT2 a_tm b_tm th =
      c_prove_hyp th (c_inst (candle_load_pth "candle$CONJUNCT2")
                     [(pvar_p, a_tm), (pvar_q, b_tm)])

    (* do_DISCH: from a_tm and th: A ⊢ c, derive A\{a} ⊢ a ==> c. *)
    fun do_DISCH a_tm c_tm th_c =
      let val a_and_c = emit_comb (emit_comb and_const a_tm) c_tm
          val ci = c_inst (candle_load_pth "candle$CONJ")
                     [(pvar_p, a_tm), (pvar_q, c_tm)]
          val cj = c_prove_hyp th_c (c_prove_hyp (c_assume a_tm) ci)
          val c1i = c_inst (candle_load_pth "candle$CONJUNCT1")
                      [(pvar_p, a_tm), (pvar_q, c_tm)]
          val da = c_deduct cj (c_prove_hyp (c_assume a_and_c) c1i)
          val di = c_inst (candle_load_pth "candle$DISCH")
                     [(pvar_p, a_tm), (pvar_q, c_tm)]
      in c_eq_mp di da end

    (* do_GEN: from v_tm and th: A ⊢ s, derive A ⊢ ∀v. s. *)
    fun do_GEN v_tm v_ty s_tm th_s =
      let val eqt_pth = c_inst (candle_load_pth "candle$EQT_INTRO")
                           [(pvar_t, s_tm)]
          val abs_eq = c_abs v_tm (c_eq_mp eqt_pth th_s)
          val Ab = emit_tyop "fun" [v_ty, bool_tyid]
          val gen_inst = c_inst (c_inst_type (candle_load_pth "candle$GEN")
                           [(tyvar_A, v_ty)])
                           [(emit_var "P" Ab, emit_abs v_tm s_tm)]
      in c_eq_mp gen_inst abs_eq end

    (* do_SPEC: from t_tm, pred_tm: λv. s, th: A ⊢ ∀v. s, derive A ⊢ s[t/v] *)
    fun do_SPEC t_tm pred_tm forall_tm v_ty th_forall =
      let val Ab = emit_tyop "fun" [v_ty, bool_tyid]
          val spec_inst = c_inst (c_inst_type (candle_load_pth "candle$SPEC")
                            [(tyvar_A, v_ty)])
                            [(emit_var "P" Ab, pred_tm),
                             (emit_var "x" v_ty, t_tm)]
          val mp_result = do_MP spec_inst forall_tm (emit_comb pred_tm t_tm) th_forall
          val (actual_bv, _) = pft_dest_abs pred_tm
          val beta_th = c_beta (emit_comb pred_tm actual_bv)
          val beta_inst = if actual_bv = t_tm then beta_th
            else c_inst beta_th [(actual_bv, t_tm)]
      in c_eq_mp beta_inst mp_result end

    (* do_beta_reduce: from lam_tm (a PFT abs term) and arg_tm,
       derive ⊢ lam_tm arg_tm = body[arg/binder]. *)
    fun do_beta_reduce lam_tm arg_tm =
      let val (actual_bv, _) = pft_dest_abs lam_tm
          val beta_th = c_beta (emit_comb lam_tm actual_bv)
      in if actual_bv = arg_tm then beta_th
         else c_inst beta_th [(actual_bv, arg_tm)] end

    (* do_EXISTS: from th: A ⊢ body[witness/v], pred = λv. body, derive A ⊢ ∃v. body *)
    fun do_EXISTS pred_tm var_tm witness_tm v_ty th =
      let val Ab_v = emit_tyop "fun" [v_ty, bool_tyid]
          val exists_inst = c_inst (c_inst_type (candle_load_pth "candle$EXISTS")
                              [(tyvar_A, v_ty)])
                              [(emit_var "P" Ab_v, pred_tm),
                               (emit_var "x" v_ty, witness_tm)]
          val witness_hyp = c_eq_mp (c_sym (do_beta_reduce pred_tm witness_tm)) th
      in c_prove_hyp witness_hyp exists_inst end

    (* do_AP_TERM: from f and th: ⊢ x = y, derive ⊢ f x = f y *)
    fun do_AP_TERM f th = c_mk_comb (c_refl f) th

    (* exist_to_witness: from th: ⊢ ∃v. body, derive ⊢ (λv. body) (@v. body)
       using CHOOSE_pth + SELECT_AX. *)
    fun exist_to_witness exists_th exists_concl_id = let
      val (_, pred_id) = pft_dest_comb exists_concl_id
      val (bv_id, pred_body_id) = pft_dest_abs pred_id
      val v_ty = pft_type_of bv_id
      val Ab = emit_tyop "fun" [v_ty, bool_tyid]
      val select_c = emit_const "@" (emit_tyop "fun" [Ab, v_ty])
      val witness = emit_comb select_c pred_id
      val pred_witness = emit_comb pred_id witness
      val var_P_Ab = emit_var "P" Ab
      val sel_inst = c_inst (c_inst_type (candle_load_pth "candle$SELECT_AX_SPEC")
                       [(tyvar_A, v_ty)])
                       [(var_P_Ab, pred_id)]
      val choose_inst = c_inst (c_inst_type (candle_load_pth "candle$CHOOSE")
                          [(tyvar_A, v_ty)])
                          [(var_P_Ab, pred_id), (pvar_Q, pred_witness)]
      val bv_x_v = emit_binder "x" v_ty
      val forall_inner = emit_comb (emit_const "!" (emit_tyop "fun" [Ab, bool_tyid]))
        (emit_abs bv_x_v (emit_comb (emit_comb (imp_const) (emit_comb pred_id bv_x_v)) pred_witness))
      val imp_forall_pw = emit_comb (emit_comb (imp_const) forall_inner) pred_witness
      val mp1 = do_MP choose_inst exists_concl_id imp_forall_pw exists_th
      val result = do_MP mp1 forall_inner pred_witness sel_inst
    in (result, pred_id, pred_body_id, Ab, v_ty) end

  in
    case proof of
    (* === Direct mappings (1:1 to Candle core rules) === *)
      REFL_prf a => r_refl (tm a)
    | TRANS_prf (a, b) => r_trans (th a) (th b)
    | MK_COMB_prf (a, b) => r_mk_comb (th a) (th b)
    | ABS_prf (a, b) => r_abs (tm a) (th b)
    | EQ_MP_prf (a, b) => r_eq_mp (th a) (th b)
    | ASSUME_prf a => r_assume (tm a)
    | SYM_prf a => r_sym (th a)
    | INST_prf (a, b) => let
        val pairs = list heap (tuple2 heap (tm, tm)) a
      in r_inst (th b) pairs end
    | INST_TYPE_prf (a, b) => let
        val pairs = list heap (tuple2 heap (ty, ty)) a
      in r_inst_type (th b) pairs end
    | deductAntisym_prf (a, b) => r_deduct (th a) (th b)

    (* Axiom_prf and Disk_prf are handled in emit_thm before dispatch *)

    (* === Simple compositions === *)
    | AP_TERM_prf (a, b) => r_mk_comb (c_refl (tm a)) (th b)
    | AP_THM_prf (a, b) => r_mk_comb (th a) (c_refl (tm b))

    (* === Pro-forma based: conjunction === *)
    | CONJ_prf (a, b) => let
        val a_th = th a val b_th = th b
        val a_tm = tm (heap_concl a) val b_tm = tm (heap_concl b)
        val ci = c_inst (candle_load_pth "candle$CONJ")
                   [(pvar_p, a_tm), (pvar_q, b_tm)]
      in r_prove_hyp b_th (c_prove_hyp a_th ci) end

    | CONJUNCT1_prf a => let
        val a_th = th a
        val concl_id = tm (heap_concl a)
        val (and_l_id, r_tm) = pft_dest_comb concl_id
        val (_, l_tm) = pft_dest_comb and_l_id
      in r_prove_hyp a_th (c_inst (candle_load_pth "candle$CONJUNCT1")
                        [(pvar_p, l_tm), (pvar_q, r_tm)]) end

    | CONJUNCT2_prf a => let
        val a_th = th a
        val concl_id = tm (heap_concl a)
        val (and_l_id, r_tm) = pft_dest_comb concl_id
        val (_, l_tm) = pft_dest_comb and_l_id
      in r_prove_hyp a_th (c_inst (candle_load_pth "candle$CONJUNCT2")
                        [(pvar_p, l_tm), (pvar_q, r_tm)]) end

    (* === Pro-forma based: implication === *)
    | MP_prf (a, b) => let
        val a_th = th a val b_th = th b
        val concl_a_id = tm (heap_concl a)
        val (imp_p_id, rhs_tm) = pft_dest_comb concl_a_id
        (* HOL4's MP treats ~p as p ==> F via dest_imp/dest_neg.
           When the conclusion is ~p rather than p ==> q, unfold
           the negation using NOT_ELIM before the normal MP step. *)
        val (a_th, p_tm, q_tm) =
          case total pft_dest_comb imp_p_id of
            SOME (_, p) => (a_th, p, rhs_tm)
          | NONE => let
              val ne = c_inst (candle_load_pth "candle$NOT_ELIM")
                         [(pvar_p, rhs_tm)]
            in (c_prove_hyp a_th ne, rhs_tm, const_F_tm) end
        val rth = c_inst (candle_load_pth "candle$MP")
                    [(pvar_p, p_tm), (pvar_q, q_tm)]
      in r_eq_mp (c_prove_hyp b_th rth) a_th end

    | EQ_IMP_RULE1_prf a => let
        val a_th = th a
        val concl_id = tm (heap_concl a)
        val (eq_l_id, q_tm) = pft_dest_comb concl_id
        val (_, p_tm) = pft_dest_comb eq_l_id
      in r_prove_hyp a_th (c_inst (candle_load_pth "candle$EQ_IMP_RULE1")
                        [(pvar_p, p_tm), (pvar_q, q_tm)]) end

    | EQ_IMP_RULE2_prf a => let
        val a_th = th a
        val concl_id = tm (heap_concl a)
        val (eq_l_id, q_tm) = pft_dest_comb concl_id
        val (_, p_tm) = pft_dest_comb eq_l_id
      in r_prove_hyp a_th (c_inst (candle_load_pth "candle$EQ_IMP_RULE2")
                        [(pvar_p, p_tm), (pvar_q, q_tm)]) end

    | NOT_ELIM_prf a => let
        val a_th = th a
        val (_, p_tm) = pft_dest_comb (tm (heap_concl a))
      in r_prove_hyp a_th (c_inst (candle_load_pth "candle$NOT_ELIM")
                        [(pvar_p, p_tm)]) end

    | NOT_INTRO_prf a => let
        val a_th = th a
        val concl_id = tm (heap_concl a)
        val (imp_p_id, _) = pft_dest_comb concl_id
        val (_, p_tm) = pft_dest_comb imp_p_id
      in r_prove_hyp a_th (c_inst (candle_load_pth "candle$NOT_INTRO")
                        [(pvar_p, p_tm)]) end

    | DISJ1_prf (a, b) => let
        val a_th = th a val q_tm = tm b
        val p_tm = tm (heap_concl a)
        val pth = c_inst (candle_load_pth "candle$DISJ1")
                    [(pvar_p, p_tm), (pvar_q, q_tm)]
      in r_prove_hyp a_th pth end

    | DISJ2_prf (a, b) => let
        val p_tm = tm a val b_th = th b
        val q_tm = tm (heap_concl b)
        val pth = c_inst (candle_load_pth "candle$DISJ2")
                    [(pvar_p, p_tm), (pvar_q, q_tm)]
      in r_prove_hyp b_th pth end

    | Mk_comb_prf (a, b, c) => r_trans (th a) (c_mk_comb (th b) (th c))

    | Mk_abs_prf (a, b, c) => let
        (* ABS over the heap's Bvar as a free Fv (emitted via `tm b`), not
           over the fresh binder that emit_term allocated inside a_th's
           lambda: Bvar's free occurrences in c_th use the former, so only
           that choice makes TRANS's mid-terms alpha-equivalent. *)
        val a_th = th a val c_th = th c
        val bv_id = tm b
      in r_trans a_th (c_abs bv_id c_th) end

    | Beta_prf a => let
        val a_th = th a
        val concl_id = tm (heap_concl a)
        val (_, rhs_id) = pft_dest_comb concl_id
        val (lam_tm, arg_tm) = pft_dest_comb rhs_id
        val (actual_bv, _) = pft_dest_abs lam_tm
        val beta_th = c_beta (emit_comb lam_tm actual_bv)
        val beta_inst = if actual_bv = arg_tm then beta_th
          else c_inst beta_th [(actual_bv, arg_tm)]
      in r_trans a_th beta_inst end

    | BETA_CONV_prf a => let
        val app_id = tm a
        val (lam_tm, arg_tm) = pft_dest_comb app_id
        val (actual_bv, _) = pft_dest_abs lam_tm
        val app_var = emit_comb lam_tm actual_bv
      in if actual_bv = arg_tm then r_beta app_var
         else r_inst (c_beta app_var) [(actual_bv, arg_tm)] end

    | ALPHA_prf (t1, _) =>
        c_refl (tm t1)

    | DISCH_prf (a, b) => let
        val p_tm = tm a val b_th = th b val q_tm = tm (heap_concl b)
      in do_DISCH p_tm q_tm b_th end

    | GEN_prf (a, b) => let
        val v_tm = tm a val b_th = th b
        val s_tm = tm (heap_concl b)
        val v_ty = pft_type_of v_tm
      in do_GEN v_tm v_ty s_tm b_th end

    | GENL_prf (a, b) => let
        val var_ids = list heap tm a
        val inner_th = th b
        fun get_abs_body id = let
          val (_, lam_id) = pft_dest_comb id
          val (_, body_id) = pft_dest_abs lam_id
        in body_id end
        val n = length var_ids
        val concl_id = tm concl_ptr
        fun build_concls 0 _ = []
          | build_concls k c = c :: build_concls (k-1) (get_abs_body c)
        val outer_concls = build_concls n concl_id
        val inner_concl_id = tm (heap_concl b)
        val rev_vars = List.rev var_ids
        val rev_s_ids = inner_concl_id :: List.rev outer_concls
        val gen_pairs = ListPair.zip (rev_vars, List.take (rev_s_ids, n))

        fun fold_gens [] th_acc = th_acc
          | fold_gens ((v_tm, s_tm) :: rest) th_acc = let
              val v_ty = pft_type_of v_tm
            in fold_gens rest (do_GEN v_tm v_ty s_tm th_acc) end
      in fold_gens gen_pairs inner_th end

    | SPEC_prf (a, b) =>
        emit_thm_candle result_id concl_ptr (Specialize_prf (a, b))

    | Specialize_prf (a, b) => let
        val t_tm = tm a val b_th = th b
        val forall_P_tm = tm (heap_concl b)
        val (_, pred_tm) = pft_dest_comb forall_P_tm
        val v_ty = pft_type_of t_tm
      in do_SPEC t_tm pred_tm forall_P_tm v_ty b_th end

    | DISJ_CASES_prf (a, b, c) => let
        val a_th = th a val b_th = th b val c_th = th c
        val concl_a_id = tm (heap_concl a)
        val (or_p_id, q_tm) = pft_dest_comb concl_a_id
        val (_, p_tm) = pft_dest_comb or_p_id
        val r_tm = tm (heap_concl b)
        val pth = c_inst (candle_load_pth "candle$DISJ_CASES")
                    [(pvar_p, p_tm), (pvar_q, q_tm), (pvar_r, r_tm)]
        val th3 = c_eq_mp (c_deduct a_th pth) a_th
        val th4 = c_prove_hyp (do_DISCH p_tm r_tm b_th) th3
      in r_prove_hyp (do_DISCH q_tm r_tm c_th) th4 end

    | CCONTR_prf (a, b) => let
        val p_tm = tm a val b_th = th b
        val neg_tm = emit_const "~" (emit_tyop "fun" [bool_tyid, bool_tyid])
        val neg_p = emit_comb neg_tm p_tm
        val disch_th = do_DISCH neg_p const_F_tm b_th
        val ccontr_inst = c_inst (candle_load_pth "candle$CCONTR")
                            [(pvar_p, p_tm)]
        val neg_p_imp_F = emit_comb (emit_comb imp_const neg_p) const_F_tm
      in do_MP ccontr_inst neg_p_imp_F p_tm disch_th end

    | EXISTS_prf (a, b, c) => let
        val c_th = th c
        val witness_tm = tm b
        val exists_id = tm a
        val (_, pred_tm) = pft_dest_comb exists_id
        val (var_tm, _) = pft_dest_abs pred_tm
        val v_ty = pft_type_of var_tm
      in do_EXISTS pred_tm var_tm witness_tm v_ty c_th end

    | CHOOSE_prf (a, b, c) => let
        val v_tm = tm a val b_th = th b val c_th = th c
        val q_tm = tm (heap_concl c)
        val exists_P_tm = tm (heap_concl b)
        val (_, pred_tm) = pft_dest_comb exists_P_tm
        val (bv_tm, _) = pft_dest_abs pred_tm
        val v_ty = pft_type_of bv_tm
        val cmb = emit_comb pred_tm v_tm
        val c_with_cmb = c_prove_hyp
                            (c_eq_mp (do_beta_reduce pred_tm v_tm) (c_assume cmb)) c_th
        val imp_cmb_q = emit_comb (emit_comb imp_const cmb) q_tm
        val gen_v = do_GEN v_tm v_ty imp_cmb_q (do_DISCH cmb q_tm c_with_cmb)
        val Ab_v = emit_tyop "fun" [v_ty, bool_tyid]
        val choose_inst = c_inst (c_inst_type (candle_load_pth "candle$CHOOSE")
                            [(tyvar_A, v_ty)])
                            [(emit_var "P" Ab_v, pred_tm), (pvar_Q, q_tm)]
        val forall_v_imp = emit_comb
          (emit_const "!" (emit_tyop "fun" [Ab_v, bool_tyid])) (emit_abs v_tm imp_cmb_q)
        val imp_forall_q = emit_comb (emit_comb imp_const forall_v_imp) q_tm
        val mp_choose1 = do_MP choose_inst exists_P_tm imp_forall_q b_th
      in do_MP mp_choose1 forall_v_imp q_tm gen_v end

    | SUBST_prf (a, b, c) => let
        val pairs = list heap (tuple2 heap (fn p => p, fn p => p)) a
        val template_ptr = b
        val c_th = th c
        val subst_map : (int * int) list =
          List.map (fn (var_ptr, thm_ptr) =>
            (tm var_ptr, th thm_ptr)) pairs
        fun lookup_subst var_id =
          case List.find (fn (v, _) => v = var_id) subst_map of
            SOME (_, th_id) => SOME th_id
          | NONE => NONE
        val source_id = tm (heap_concl c)
        val template_id = tm template_ptr
        (* Do NOT short-circuit on src_id = tmpl_id at compound
           templates: HOL4's SUBST allows the redex to be any free
           variable of the template (including one that also appears
           unchanged in the source, e.g. SUBST [(v, ⊢ v = a)] (P v) (⊢ P v)
           produces ⊢ P a).  Structural equality does not imply that no
           substitution applies inside, so we must always descend through
           the template to pick up redex lookups.  Only leaf VAR/CONSTs
           that are neither bound nor a redex may emit c_refl. *)
        fun rconv binder_map src_id tmpl_id =
          case List.find (fn (tv, _) => tv = tmpl_id) binder_map of
            SOME (_, sv) =>
              if sv = src_id then c_refl src_id
              else raise Fail ("rconv: binder variable mismatch: src "
                               ^ Int.toString src_id ^ " vs mapped "
                               ^ Int.toString sv)
          | NONE =>
          case lookup_subst tmpl_id of
            SOME th_id => th_id
          | NONE =>
            if pft_is_comb tmpl_id then
              let val (sf, sx) = pft_dest_comb src_id
                  val (tf, tx) = pft_dest_comb tmpl_id
              in c_mk_comb (rconv binder_map sf tf)
                           (rconv binder_map sx tx)
              end
            else if tm_part1_of tmpl_id >= 0 then
              let val (sv, sb) = pft_dest_abs src_id
                  val (tv, tb) = pft_dest_abs tmpl_id
                  (* ABS_THM requires the abstracted variable not to be
                     free in the hypotheses of the recursive theorem.
                     SUBST's recursive congruence theorem inherits the
                     substitution hypotheses, so the original binder may
                     be unsafe.  Alpha-rename both sides to a fresh
                     synthetic binder before applying ABS_THM. *)
                  val bv = emit_binder "v" (pft_type_of sv)
                  val sb' = pft_rename_free sv bv sb
                  val tb' = pft_rename_free tv bv tb
              in c_abs bv (rconv binder_map sb' tb')
              end
            else if src_id = tmpl_id then c_refl src_id
            else raise Fail ("rconv: leaf mismatch: src "
                             ^ Int.toString src_id
                             ^ " vs tmpl " ^ Int.toString tmpl_id)
        val conv_th = rconv [] source_id template_id
        (* rconv may alpha-rename binders internally to satisfy ABS_THM.
           Its RHS is the substituted result with freshened bound names.
           Bridge back to this SUBST proof node's actual conclusion, whose
           bound names are the names expected by downstream proof steps. *)
        val result_id = tm concl_ptr
        val conv_to_result = c_trans conv_th (c_refl result_id)
      in r_eq_mp conv_to_result c_th end

    | GEN_ABS_prf (a, b, c) => let
        val vars = list heap tm b
        val c_th = th c
        (* HOL4's GEN_ABS retypes the binder per variable (Thm.list_mk_binder
           / Logging.GEN_ABS_prf), so we must too — otherwise mixed-type
           variable lists yield ill-typed MK_COMB terms. *)
        val step = case option heap (fn p => p) a of
            NONE => (fn (v_tm, th_acc) => c_abs v_tm th_acc)
          | SOME c_ptr => let
              val c_refl0 = c_refl (emit_term c_ptr)
              fun dom ty_ptr = case shType heap ty_ptr of
                  Tyapp (_, args) => hd (list heap (fn p => p) args)
                | _ => raise Fail "GEN_ABS_prf: c's type is not a function"
              val sigma = case shTerm heap c_ptr of
                  Const (_, ty) => emit_type (dom (dom ty))
                | _ => raise Fail "GEN_ABS_prf: c is not a constant"
              fun refl_at v_ty =
                if v_ty = sigma then c_refl0
                else c_inst_type c_refl0 [(sigma, v_ty)]
            in fn (v_tm, th_acc) =>
                 c_mk_comb (refl_at (pft_type_of v_tm)) (c_abs v_tm th_acc)
            end
      in List.foldr step c_th vars end

    (* === Definition commands === *)
    | Def_const_prf (a, b) => let
        val (Thy, Name) = get_const_id b
        val cname = tr_name (thyname ^ "$" ^ Name)
        (* In boolTheory, constants already defined by the preamble are
           not re-defined; instead we LOAD the preamble's definition
           theorem (which has an alpha-equivalent or HOL4-compatible
           conclusion). *)
        val preamble_name =
          if thyname = "bool" then
            List.find (fn (k,_) => k = Name) candle_preamble_def
          else NONE
      in case preamble_name of
           SOME (_, load_name) => let
             val () = mark_const cname
           in candle_load_pth load_name end
         | NONE =>
           if (thyname, Name) = ("arithmetic", "ZERO") then
           let val () = mark_const cname
           in r_refl (emit_const "_0" (emit_tyop "num" [])) end
           else let
             val rhs_id = emit_term a
             val rhs_ty_id = pft_type_of rhs_id
             val bool_ty_c = emit_tyop "bool" []
             val eq_ty = emit_tyop "fun" [rhs_ty_id, emit_tyop "fun" [rhs_ty_id, bool_ty_c]]
             val eq_tm = emit_comb (emit_comb (emit_const "=" eq_ty)
                           (emit_var cname rhs_ty_id)) rhs_id
             val () = mark_const cname
           in PFTWriter.Candle.new_specification out result_id
                (c_assume eq_tm) [cname]; result_id end
      end

    | Def_const_list_prf (a, b) => let
        (* The two rulesets require incompatible naming conventions:
             - pft-ruleset-hol4.md, DEF_SPEC_GEN: each `s_i` MUST match
               `thy$v_i` for some common theory prefix `thy`.  So the
               trace's hypothesis LHS is the bare-named variable `v_i`
               while the command's argument name is `thy$v_i`.
             - pft-ruleset-candle.md, new_specification: each `s_i`
               MUST equal the name of `v_i`.  Hypothesis LHS name and
               command argument name must coincide verbatim.
           Passing the HOL4-shaped theorem and name list directly to
           Candle would therefore violate Candle's side condition.  We
           bridge the two conventions by INST-ing each bare-named
           hypothesis variable to a fresh prefix-named one before the
           hand-off, matching the name convention used by the sibling
           branches Def_const_prf and Def_spec_prf. *)
        val const_ptrs = list heap (fn p => p) b
        val ids = List.map get_const_id const_ptrs
        val preamble_name =
          if thyname = "bool" then
            case ids of [(_, nm)] =>
              List.find (fn (k,_) => k = nm) candle_preamble_def
            | _ => NONE
          else NONE
      in case preamble_name of
           SOME (_, load_name) =>
             (mark_const (tr_name (thyname ^ "$" ^ #2 (hd ids))); candle_load_pth load_name)
         | NONE => let
             val a_th = th a

             (* For each constant pointer, build the bare-named and
                prefix-named variables at the constant's type.  By
                emit_var hash-consing, v_old is the very same term ID
                that appears inside a_th's hypothesis LHS and as a
                free variable in the body, so a single INST rewrites
                both at once. *)
             fun mk_rename cp = let
                   val (Thy, Name) = get_const_id cp
                   val ty_ptr =
                     case shTerm heap cp of
                       Const (_, typ) => typ
                     | _ => raise Fail "Def_const_list_prf: not a const"
                   val cname = tr_name (Thy ^ "$" ^ Name)
                   val v_ty  = emit_type ty_ptr
                   val v_old = emit_var Name  v_ty
                   val v_new = emit_var cname v_ty
                   val ()    = mark_const cname
                 in (cname, v_old, v_new) end
             val triples = List.map mk_rename const_ptrs
             val cnames  = List.map #1 triples
             val subs    = List.map (fn (_, old, new) => (old, new)) triples

             (* Candle INST is a parallel free-variable substitution;
                since the v_new's are all prefix-named (disjoint from
                the bare v_old's and from each other), the parallel
                and sequential forms coincide. *)
             val a_th'   = if null subs then a_th else c_inst a_th subs
           in PFTWriter.Candle.new_specification out result_id a_th' cnames;
              result_id end
      end

    | Def_spec_prf (a, b) => let
        (* Candle's new_specification requires each hypothesis ti in
           [v_1=t_1,...,v_n=t_n] ⊢ p to be CLOSED (pft-ruleset-candle.md
           §212).  From input ⊢ ∃v_1...∃v_n. body we:
             1. build closed Hilbert-select witnesses
                  W_i = @(λv_i. body_i [W_1/v_1,...,W_{i-1}/v_{i-1}])
                (note: W_j substituted, not the constant-named variables);
             2. peel the existentials using W_i as witness at each step
                to get  ⊢ body [W_1/v_1,...,W_n/v_n]  (no hypotheses);
             3. congruence-rewrite over body's AST to turn each v_i
                position from W_i into a fresh variable c_var_i (named
                after the constant), using ASSUME(c_var_i=W_i)+SYM.
           The final theorem {c_var_i=W_i} ⊢ body[c_var/v] with closed W_i
           is exactly what new_specification accepts. *)

        val const_ptrs = list heap (fn p => p) b
        val input_th = th a
        val input_concl_id = tm (heap_concl a)
        val n = List.length const_ptrs
        val () = if n = 0
                 then raise Fail "Def_spec_prf: empty constants list"
                 else ()

        (* Destructure ∃v_1...∃v_n. body into [v_1,...,v_n] and body.
           Also collect each intermediate body_i = ∃v_{i+1}...∃v_n. body. *)
        fun strip_exists 0 body acc_v acc_body =
              (rev acc_v, rev acc_body, body)
          | strip_exists k tm_id acc_v acc_body =
              let val (_, pred) = pft_dest_comb tm_id
                  val (v, body) = pft_dest_abs pred
              in strip_exists (k-1) body (v::acc_v) (body::acc_body) end
        val (vs, bodies, body_raw) =
              strip_exists n input_concl_id [] []

        (* Per-constant data: constant-name variable c_var_i at v_i's type,
           plus the cname string for the final new_specification call.
           Also registers each constant via mark_const. *)
        fun mk_const_var (cp, v_id) = let
              val (Thy, Name) = get_const_id cp
              val cname = tr_name (Thy ^ "$" ^ Name)
              val v_ty = pft_type_of v_id
              val () = mark_const cname
            in (cname, emit_var cname v_ty, v_ty) end
        val cvt = List.map mk_const_var (ListPair.zipEq (const_ptrs, vs))
        val cnames = List.map #1 cvt

        (* Phase 1a: build each W_i by substituting earlier W_j's into body_i. *)
        fun mk_witness (v_id, v_ty, body_i, prev_vw) = let
              val body_c =
                List.foldl (fn ((vj, wj), t) => pft_subst_tm vj wj t)
                           body_i prev_vw
              val pred_c = emit_abs v_id body_c
              val Ab = emit_tyop "fun" [v_ty, bool_tyid]
              val w_i = emit_comb
                          (emit_const "@" (emit_tyop "fun" [Ab, v_ty]))
                          pred_c
            in (pred_c, w_i) end
        fun build_ws acc [] [] [] = rev acc
          | build_ws acc ((_, _, v_ty)::cvt') (v_id::vs') (body_i::bodies') = let
              val prev_vw = List.map (fn (v, _, _, w) => (v, w)) (rev acc)
              val (pred_c, w_i) = mk_witness (v_id, v_ty, body_i, prev_vw)
            in build_ws ((v_id, v_ty, pred_c, w_i) :: acc)
                        cvt' vs' bodies' end
          | build_ws _ _ _ _ = raise Fail "Def_spec_prf: length mismatch"
        val wdata = build_ws [] cvt vs bodies
        (* wdata : [(v_id, v_ty, pred_closed, W_i), ...] *)

        (* Phase 1b: peel each ∃ using W_i, producing ⊢ body_raw[W/v]. *)
        fun peel ((_, v_ty, pred_c, w_i), th_acc) = let
              val Ab = emit_tyop "fun" [v_ty, bool_tyid]
              val bv_P = emit_binder "P" Ab
              val select_c = emit_const "@" (emit_tyop "fun" [Ab, v_ty])
              val lam_PP = emit_abs bv_P
                             (emit_comb bv_P (emit_comb select_c bv_P))
              val exists_def = c_inst_type
                     (candle_load_pth "candle$EXISTS_DEF_HOL4")
                     [(tyvar_A, v_ty)]
              (* ⊢ ?pred_c = (λP. P(@P)) pred_c *)
              val ap_th = c_mk_comb exists_def (c_refl pred_c)
              (* ⊢ (λP. P(@P)) pred_c = pred_c (@ pred_c) = pred_c W_i *)
              val beta_th = do_beta_reduce lam_PP pred_c
              val strip = c_trans ap_th beta_th
              (* ⊢ pred_c W_i *)
              val th1 = c_eq_mp strip th_acc
              (* ⊢ body_closed_i [W_i / v_id] *)
            in c_eq_mp (do_beta_reduce pred_c w_i) th1 end
        val th_closed = List.foldl peel input_th wdata

        (* Phase 2: for each i, eq_i : {c_var_i = W_i} ⊢ W_i = c_var_i. *)
        val v_eqs =
          List.map
            (fn ((v_id, v_ty, _, w_i), (_, c_var, _)) => let
                  val eq_ty = emit_tyop "fun"
                                [v_ty, emit_tyop "fun" [v_ty, bool_tyid]]
                  val eq_tm = emit_comb
                                (emit_comb (emit_const "=" eq_ty) c_var) w_i
                in (v_id, c_sym (c_assume eq_tm)) end)
            (ListPair.zipEq (wdata, cvt))

        (* Phase 3: congruence walk over body_raw.
           cong t : ⊢ t[W/v] = t[c/v], with hypotheses drawn from
           {c_var_i = W_i}.  At each v_i leaf we emit eq_i; elsewhere
           we recurse structurally.  No memoization: bodies are small
           in practice; if profiling shows it matters, memoize on tm_id. *)
        fun cong tm_id =
          case List.find (fn (v, _) => v = tm_id) v_eqs of
            SOME (_, eq_i) => eq_i
          | NONE => let
              val f = tm_part1_of tm_id
            in if f < 0 then c_refl tm_id  (* VAR or CONST, not a v_i *)
               else let val x = tm_part2_of tm_id
               in if isSome (IntPairTable.lookup comb_ht (f, x))
                  then c_mk_comb (cong f) (cong x)
                  else c_abs f (cong x)   (* ABS f x *)
               end
            end

        (* Sanity: every v_i must occur free in body_raw, else the
           corresponding hypothesis would be missing from final_th and
           new_specification would reject (or accept a malformed input). *)
        fun occurs_free v_id tm_id =
            tm_id = v_id orelse
            (let val f = tm_part1_of tm_id
             in f >= 0 andalso
                  let val x = tm_part2_of tm_id
                  in if isSome (IntPairTable.lookup comb_ht (f, x))
                     then occurs_free v_id f orelse occurs_free v_id x
                     else f <> v_id andalso occurs_free v_id x
                  end
             end)
        val () = List.app
          (fn (v_id, _) =>
             if occurs_free v_id body_raw then ()
             else raise Fail ("Def_spec_prf: some v_i does not appear "
                    ^ "free in body; cannot form required hypothesis"))
          v_eqs

        val final_th = c_eq_mp (cong body_raw) th_closed
      in PFTWriter.Candle.new_specification out result_id final_th cnames;
         result_id
      end

    | Def_tyop_prf (a, b, c) => let
        val _ = list heap ty a
        val () = if thyname = "bool"
                 then check_def tm_defs thyname "TYPE_DEFINITION" else ()
        val b_th = th b
        val (Thy, Tyop) = get_type_id c
        val () = mark_type Tyop
        val tyname = tr_name (Thy ^ "$" ^ Tyop)
        val (th_pw, pred_id, pred_body_id, Ab, rep_ty) =
          exist_to_witness b_th (tm (heap_concl b))

        val absname = tyname ^ "_abs"
        val repname = tyname ^ "_rep"
        (* new_type_definition produces two theorems at consecutive IDs:
           tydef_id   = ⊢ abs (rep a) = a
           tydef_id+1 = ⊢ P r = (rep (abs r) = r)
           We allocate both IDs here so the counter advances past the
           implicitly-created second theorem. *)
        val tydef_id = alloc_th ()
        val tydef_id2 = alloc_th ()
        val () = PFTWriter.Candle.new_type_definition out tydef_id th_pw
            tyname absname repname

        val tyvars_ptrs = list heap I a
        val new_ty = emit_tyop tyname (List.map ty tyvars_ptrs)
        val abs_ty = emit_tyop "fun" [rep_ty, new_ty]
        val rep_fn_ty = emit_tyop "fun" [new_ty, rep_ty]
        val abs_c = emit_const absname abs_ty
        val rep_c = emit_const repname rep_fn_ty
        val Ab_new = emit_tyop "fun" [new_ty, bool_tyid]
        val eq_new = emit_const "=" (emit_tyop "fun" [new_ty, emit_tyop "fun" [new_ty, bool_tyid]])
        val eq_rep = emit_const "=" (emit_tyop "fun" [rep_ty, emit_tyop "fun" [rep_ty, bool_tyid]])
        val Abb_new = emit_tyop "fun" [Ab_new, bool_tyid]

        val var_a = emit_var "a" new_ty
        val var_r_rep = emit_var "r" rep_ty
        val bv_x_rep = emit_binder "x" rep_ty
        val bv_x' = emit_binder "x'" new_ty
        val bv_x'' = emit_binder "x''" new_ty
        val rep_x' = emit_comb rep_c bv_x'
        val rep_x'' = emit_comb rep_c bv_x''
        val abs_x = emit_comb abs_c bv_x_rep
        val phi_x = emit_comb pred_id bv_x_rep

        val ar_x' = c_inst tydef_id [(var_a, bv_x')] (* ⊢ abs (rep x') = x' *)
        val ar_x'' = c_inst tydef_id [(var_a, bv_x'')] (* ⊢ abs (rep x'') = x'' *)
        val rr = emit_comb (emit_comb eq_rep rep_x') rep_x'' (* rep x' = rep x'' *)
        val arr = do_AP_TERM abs_c (c_assume rr) (* rep x' = rep x'' ⊢ abs (rep x') = abs (rep x'') *)
        val th_inj = c_trans (c_trans (c_sym ar_x') arr) ar_x'' (* rep x' = rep x'' ⊢ x' = x'' *)
        val x'_eq_x'' = emit_comb (emit_comb eq_new bv_x') bv_x'' (* x' = x'' *)
        val inj_body = emit_comb (emit_comb (imp_const) rr) x'_eq_x'' (* rep x' = rep x'' ⇒ x' = x'' *)
        val forall_new = emit_const "!" Abb_new
        val th_conj1 = do_GEN bv_x' new_ty
          (emit_comb forall_new (emit_abs bv_x'' inj_body))
          (do_GEN bv_x'' new_ty inj_body (do_DISCH rr x'_eq_x'' th_inj))
          (* ⊢ (∀x' x''. rep x' = rep x'' ⇒ x' = x'') *)

        val ra_x = c_inst tydef_id2 [(var_r_rep, bv_x_rep)] (* ⊢ P x = (rep (abs x) = x) *)
        val sym_ra_x = c_sym ra_x (* ⊢ (rep (abs x) = x) = P x *)
        val x_eq_rep_x' = emit_comb (emit_comb eq_rep bv_x_rep) rep_x' (* x = rep x' *)
        val pred_exists = emit_abs bv_x' x_eq_rep_x' (* λx'. x = rep x' *)
        val exist_x_eq = emit_comb (emit_const "?" Abb_new) pred_exists (* ∃x'. x = rep x' *)

        (* Forward: {phi x} |- ?x'. x = rep x' *)
        val sym_repabs = c_sym (c_eq_mp ra_x (c_assume phi_x)) (* P x ⊢ x = rep (abs x) *)
        val th_fwd = do_EXISTS pred_exists bv_x' abs_x new_ty sym_repabs
        (* P x ⊢ ∃x'. x = rep x' *)

        (* Backward: {?x'. x = rep x'} |- phi x *)
        val pred_x' = emit_comb pred_exists bv_x' (* (λx'. x = rep x') x' *)
        val assume_xeq = c_assume x_eq_rep_x' (* x = rep x' ⊢ x = rep x' *)
        val abs_x_eq_x' = c_trans (do_AP_TERM abs_c assume_xeq) ar_x' (* x = rep x' ⊢ abs x = x' *)
        val th_repabsx = c_trans (do_AP_TERM rep_c abs_x_eq_x') (c_sym assume_xeq) (* x = rep x' ⊢ rep (abs x) = x *)
        val th_phi_from_xeq = c_eq_mp sym_ra_x th_repabsx (* x = rep x' ⊢ P x *)
        val beta_pred_x' = do_beta_reduce pred_exists bv_x' (* ⊢ (λx'. x = rep x') x' = x = rep x' *)
        val th_phi_from_pred_x' = c_prove_hyp
            (c_eq_mp beta_pred_x' (c_assume pred_x'))
            th_phi_from_xeq (* (λx'. x = rep x') x' ⊢ P x *)
        val pred_x'_imp_phi = emit_comb (emit_comb imp_const pred_x') phi_x (* (λx'. x = rep x') x' ⇒ P x *)
        val var_P_Ab_new = emit_var "P" Ab_new
        val choose_inst_bwd = c_inst (c_inst_type (candle_load_pth "candle$CHOOSE")
                                [(tyvar_A, new_ty)])
                                [(var_P_Ab_new, pred_exists), (pvar_Q, phi_x)]
                              (* ⊢ (∃x'. x = rep x') ⇒ (∀x''. (λx'. x = rep x') x'' ⇒ P x) ⇒ P x *)
        val forall_new_imp = emit_comb forall_new
            (emit_abs bv_x' pred_x'_imp_phi) (* ∀x'. (λx'. x = rep x') x' ⇒ P x *)
        val th_bwd1 = do_MP choose_inst_bwd exist_x_eq
                        (emit_comb (emit_comb imp_const forall_new_imp) phi_x)
                        (c_assume exist_x_eq)
                      (* ∃x'. x = rep x' ⊢ (∀x'. (λx'. x = rep x') x' ⇒ P x) ⇒ P x *)
        val th_bwd2 = do_DISCH pred_x' phi_x th_phi_from_pred_x' (* ⊢ (λx'. x = rep x') x' ⇒ P x *)
        val th_bwd3 = do_GEN bv_x' new_ty pred_x'_imp_phi th_bwd2 (* ⊢ ∀x'. (λx'. x = rep x') x' ⇒ P x *)
        val th_bwd = do_MP th_bwd1 forall_new_imp phi_x th_bwd3
                     (* ∃x'. x = rep x' ⊢ P x *)

        val th_char_x = c_deduct th_bwd th_fwd (* ⊢ P x = ∃x'. x = rep x' *)
        val phi_eq_exists = emit_comb (emit_comb (eq_bool_const) phi_x) exist_x_eq (* P x = ∃x'. x = rep x' *)
        val th_conj2 = do_GEN bv_x_rep rep_ty phi_eq_exists th_char_x
                       (* ⊢ ∀x. P x = ∃x'. x = rep x' *)

        val forall_rep = emit_const "!" (emit_tyop "fun" [Ab, bool_tyid])
        val conj1_body = emit_comb forall_new
          (emit_abs bv_x' (emit_comb forall_new (emit_abs bv_x'' inj_body)))
          (* ∀x' x''. rep x' = rep x'' ⇒ x' = x'' *)
        val conj2_body = emit_comb forall_rep (emit_abs bv_x_rep phi_eq_exists)
          (* ∀x. P x = ∃x'. x = rep x' *)
        val conj_th = do_CONJ conj1_body conj2_body th_conj1 th_conj2
          (* ⊢ (∀x' x''. rep x' = rep x'' ⇒ x' = x'') ∧
               (∀x. P x = ∃x'. x = rep x' *)

        (* --- Instantiate TYPE_DEFINITION_THM via two SPECs --------------- *)

        val tydef_th =
          if thyname = "bool"
          then emit_thm (Redblackmap.find(named_thm_map, "TYPE_DEFINITION_THM"))
          else candle_load_pth "bool$TYPE_DEFINITION_THM"
        val tydef_inst = c_inst_type tydef_th
                           [(tyvar_A, rep_ty),
                            (tyvar_B, new_ty)]
          (* ∀P rep. TYPE_DEFINITION P rep ⇔
                     (∀x' x''. rep x' = rep x'' ⇒ x' = x'') ∧
                     (∀x. P x ⇔ ∃x'. x = rep x') *)
        val bv_P_v = emit_binder "P" Ab
        val bv_rep_v = emit_binder "rep" rep_fn_ty
        val rep_fn_ty_bool = emit_tyop "fun" [rep_fn_ty, bool_tyid]
        val tydef_ty = emit_tyop "fun" [Ab, rep_fn_ty_bool]
        val tydef_c = emit_const "bool$TYPE_DEFINITION" tydef_ty
        val forall_rep_fn = emit_const "!"
          (emit_tyop "fun" [rep_fn_ty_bool, bool_tyid])

        (* Build the TYPE_DEFINITION body with generic P, rep variables.
           TYPE_DEFINITION P rep ≡
             (∀x' x''. rep x' = rep x'' ⇒ x' = x'') ∧
             (∀x. P x = ∃x'. x = rep x') *)
        val rep_v_x' = emit_comb bv_rep_v bv_x' (* rep x' *)
        val rep_v_x'' = emit_comb bv_rep_v bv_x'' (* rep x'' *)
        val inj_body_v = emit_comb forall_new
          (emit_abs bv_x' (emit_comb forall_new (emit_abs bv_x''
            (emit_comb (emit_comb imp_const
              (emit_comb (emit_comb eq_rep rep_v_x') rep_v_x''))
              (emit_comb (emit_comb eq_new bv_x') bv_x'')))))
           (* ∀x' x''. rep x' = rep x'' ⇒ x' = x'' *)
        val exist_v = emit_comb (emit_const "?" (emit_tyop "fun" [Ab_new, bool_tyid]))
          (emit_abs bv_x' (emit_comb (emit_comb eq_rep bv_x_rep) rep_v_x'))
           (* ∃x'. x = rep x' *)
        fun mk_char_body P_x = emit_comb forall_rep
          (emit_abs bv_x_rep (emit_comb (emit_comb eq_bool_const P_x) exist_v))
           (* ∀x. ^P_x = ∃x'. x = rep x' *)
        val and_inj_body_v = emit_comb and_const inj_body_v
        val tydef_body_v = emit_comb and_inj_body_v
                             (mk_char_body (emit_comb bv_P_v bv_x_rep))
           (* (∀x' x''. rep x' = rep x'' ⇒ x' = x'') ∧
              (∀x. P x = ∃x'. x = rep x') *)
        val tydef_eq_v = emit_comb (emit_comb eq_bool_const
          (emit_comb (emit_comb tydef_c bv_P_v) bv_rep_v)) tydef_body_v
           (* TYPE_DEFINITION P rep = ... *)
        val inner_forall = emit_comb forall_rep_fn (emit_abs bv_rep_v tydef_eq_v)
           (* ∀rep. TYPE_DEFINITION P rep = ... *)
        val outer_lam = emit_abs bv_P_v inner_forall
           (* λP. ∀rep. TYPE_DEFINITION P rep = ... *)
        val forall_Ab = emit_const "!"
          (emit_tyop "fun" [emit_tyop "fun" [Ab, bool_tyid], bool_tyid])
        val outer_forall = emit_comb forall_Ab outer_lam
           (* ∀P rep. TYPE_DEFINITION P rep = ... *)

        (* SPEC P := pred_id *)
        val spec1 = do_SPEC pred_id outer_lam outer_forall Ab tydef_inst
         (* ⊢ ∀rep. TYPE_DEFINITION P rep = ... *)

        (* SPEC rep := rep_c — need the post-P-specialization body *)
        val tydef_phi_body = emit_comb and_inj_body_v (mk_char_body phi_x)
        val tydef_phi_bv_rep = emit_comb (emit_comb tydef_c pred_id) bv_rep_v
        val tydef_phi_eq = emit_comb
                             (emit_comb eq_bool_const tydef_phi_bv_rep)
                                 tydef_phi_body
        val lam_rep_tydef_phi_eq = emit_abs bv_rep_v tydef_phi_eq
        val inner_forall2 = emit_comb forall_rep_fn lam_rep_tydef_phi_eq
                            (* ∀rep. TYPE_DEFINITION P rep = ... *)
        val spec2 = do_SPEC rep_c lam_rep_tydef_phi_eq
                      inner_forall2 rep_fn_ty spec1
         (* ⊢ TYPE_DEFINITION P rep = ... *)

        val tydef_proved = c_eq_mp (c_sym spec2) conj_th
         (* ⊢ TYPE_DEFINITION P rep *)

        (* HOL4's prim_type_definition destructures the input witness's
           body as P v = dest_comb Body and then produces
             ⊢ ∃rep. TYPE_DEFINITION P rep
           with the un-eta-expanded P.  `pred_id` here is the λ from the
           witness's ∃, and `pred_body_id` is `P v`; so `pred_uneta` is
           the un-eta-expanded predicate HOL4 would use. *)
        val (pred_uneta, _) = pft_dest_comb pred_body_id

        (* Build ⊢ (λx. P x) = P via ETA_AX at (rep_ty, bool). *)
        val eta_inst = c_inst_type (candle_load_pth "candle$ETA_AX")
                         [(tyvar_A, rep_ty),
                          (tyvar_B, bool_tyid)]
        val eq_Ab = emit_const "="
          (emit_tyop "fun" [Ab, emit_tyop "fun" [Ab, bool_tyid]])
        val bv_t = emit_binder "t" Ab
        val abs_x_t_x = emit_abs bv_x_rep (emit_comb bv_t bv_x_rep)
        val eta_eq_body = emit_comb (emit_comb eq_Ab abs_x_t_x) bv_t
        val abs_eta_eq = emit_abs bv_t eta_eq_body
        val P_uneta_eq = do_SPEC pred_uneta abs_eta_eq
                           (emit_comb forall_Ab abs_eta_eq) Ab eta_inst
         (* ⊢ (λx. P x) = P *)

        (* Rewrite tydef_proved : ⊢ TYPE_DEFINITION (λx. P x) rep
           into                   ⊢ TYPE_DEFINITION P rep, so that the
           following do_EXISTS builds ?-at-rep_fn_ty with the correct
           un-eta-expanded P. *)
        val tydef_P_eq = do_AP_TERM tydef_c P_uneta_eq
         (* ⊢ TYPE_DEFINITION (λx. P x) = TYPE_DEFINITION P *)
        val tydef_P_rep_eq = c_mk_comb tydef_P_eq (c_refl rep_c)
         (* ⊢ TYPE_DEFINITION (λx. P x) rep = TYPE_DEFINITION P rep *)
        val tydef_uneta = c_eq_mp tydef_P_rep_eq tydef_proved
         (* ⊢ TYPE_DEFINITION P rep *)

        val tydef_P_bv_rep =
          emit_comb (emit_comb tydef_c pred_uneta) bv_rep_v
        val exist_pred_rep_uneta = emit_abs bv_rep_v tydef_P_bv_rep
         (* λrep. TYPE_DEFINITION P rep *)
      in do_EXISTS exist_pred_rep_uneta bv_rep_v rep_c rep_fn_ty tydef_uneta end

    | compute_prf (a, b) =>
        let
          (* Compute preamble theorems and COMPUTE_INIT are emitted by the
             standalone Candle compute preamble PFT.  Per-theory Candle PFTs
             only LOAD those helper theorems and emit COMPUTE commands. *)

          (* Parse compute_prf arguments *)
          val (compute_args_ptr, ths_ptr) = tuple2 heap (I, I) a

          (* Emit and translate code equations.
             Each code equation is ⊢ lhs = rhs where rhs may contain
             HOL4-form numerals that need translation to Candle form. *)
          val code_eqn_ths = list heap (fn th_ptr => let
            val th_id = emit_thm th_ptr
            (* Get the conclusion of this theorem to find its RHS *)
            val (_, concl_p, _) = shThm heap th_ptr
            val rhs_ptr = case shTerm heap concl_p of
                Comb (eq_lhs_ptr, rhs_ptr) => rhs_ptr
              | _ => raise Fail "compute_prf: code equation not an equation"
            val rhs_id = emit_term rhs_ptr
            val (candle_rhs_id, rhs_xlate_th) =
              translate_term_numerals_hol4_to_candle rhs_ptr rhs_id
          in
            if rhs_xlate_th < 0 then th_id
            else
              (* TRANS th_id rhs_xlate_th: lhs = rhs_candle *)
              let val id = alloc_th ()
              in PFTWriter.Candle.trans out id th_id rhs_xlate_th; id end
          end) ths_ptr

          (* The input term from the trace *)
          val input_tm_ptr = b

          (* Get the expected result from the conclusion.
             concl_ptr points to "input_tm = expected_result" *)
          val (expected_result_ptr, _) = case shTerm heap concl_ptr of
              Comb (eq_lhs_ptr, rhs_ptr) =>
                (case shTerm heap eq_lhs_ptr of
                   Comb (_, lhs_ptr) => (rhs_ptr, lhs_ptr)
                 | _ => raise Fail "compute_prf: malformed conclusion")
            | _ => raise Fail "compute_prf: conclusion not an equation"

          (* Emit the input term (which may contain HOL4-form numerals) *)
          val input_tm_id = emit_term input_tm_ptr

          (* Translate input term's numerals from HOL4 to Candle form.
             Returns (candle_tm_id, translation_th_id) where
             translation_th_id proves: input_tm = candle_tm *)
          val (candle_input_tm, input_xlate_th) =
            translate_term_numerals_hol4_to_candle input_tm_ptr input_tm_id

          (* Call COMPUTE: candle_input_tm, code_eqn_ths
             Returns theorem: candle_input_tm = candle_result *)
          val compute_th_id = alloc_th ()
          val () = PFTWriter.Candle.compute out compute_th_id
                     candle_input_tm code_eqn_ths
          (* compute_th_id: candle_input_tm = candle_result *)

          (* Chain input translation with compute result:
             input_xlate_th: input_tm = candle_input_tm
             compute_th: candle_input_tm = candle_result
             TRANS gives: input_tm = candle_result *)
          val step1_th =
            if input_xlate_th < 0 then compute_th_id
            else let val id = alloc_th ()
              in PFTWriter.Candle.trans out id input_xlate_th compute_th_id; id end
          (* step1_th: input_tm = candle_result *)

          (* Now translate the result back from Candle to HOL4 form.
             The expected result is in expected_result_ptr (HOL4 form).
             We need to prove: candle_result = expected_result *)
          val expected_result_id = emit_term expected_result_ptr
          val (candle_result_id, result_xlate_th) =
            translate_term_numerals_hol4_to_candle expected_result_ptr expected_result_id
          (* result_xlate_th: expected_result = candle_result (HOL4 = Candle)
             We need: candle_result = expected_result, so use SYM *)

          val final_th =
            if result_xlate_th < 0 then
              (* No translation needed in result *)
              step1_th
            else let
              (* SYM result_xlate_th: candle_result = expected_result *)
              val sym_th = let val id = alloc_th ()
                in PFTWriter.Candle.sym out id result_xlate_th; id end
              (* TRANS step1_th sym_th: input_tm = expected_result *)
              val id = alloc_th ()
            in PFTWriter.Candle.trans out id step1_th sym_th; id end
        in
          final_th
        end

    | save_dep_prf _ => raise Fail "unreachable"
    | deleted_prf => raise Fail "emit_thm_candle: deleted"
    | Axiom_prf => raise Fail "unreachable: handled in emit_thm"
    | Disk_prf _ => raise Fail "unreachable: handled in emit_thm"
  end

  (* ======================================================================= *)
  (* Candle COMPUTE helpers                                                  *)
  (* ======================================================================= *)

  (* Check if a term is a numeral (NUMERAL applied to bits) *)
  and is_numeral_term tm_ptr =
    case shTerm heap tm_ptr of
      Comb (rator_ptr, _) =>
        (case shTerm heap rator_ptr of
           Const (id_ptr, _) =>
             let val (thy, name) = ident heap id_ptr
             in thy = "arithmetic" andalso name = "NUMERAL" end
         | _ => false)
    | _ => false

  (* Extract numeric value from HOL4 numeral bits (inside NUMERAL wrapper)
     Returns NONE if not a valid numeral bit pattern *)
  and numeral_value_of_bits tm_ptr : int option =
    case shTerm heap tm_ptr of
      Const (id_ptr, _) =>
        let val (thy, name) = ident heap id_ptr
        in if (thy = "arithmetic" andalso name = "ZERO") orelse
              (thy = "num" andalso name = "0")
           then SOME 0
           else NONE
        end
    | Comb (rator_ptr, arg_ptr) =>
        (case shTerm heap rator_ptr of
           Const (id_ptr, _) =>
             let val (thy, name) = ident heap id_ptr
             in if thy = "arithmetic" then
                  case numeral_value_of_bits arg_ptr of
                    SOME n =>
                      if name = "BIT1" then SOME (2 * n + 1)
                      else if name = "BIT2" then SOME (2 * n + 2)
                      else NONE
                  | NONE => NONE
                else NONE
             end
         | _ => NONE)
    | _ => NONE

  (* Check if a number needs translation (contains BIT2 in HOL4 form) *)
  and needs_numeral_translation 0 = false
    | needs_numeral_translation n =
        if n mod 2 = 1 then needs_numeral_translation ((n - 1) div 2)
        else true  (* even > 0 means BIT2 *)

  (* Translate a single numeral from HOL4 to Candle form.
     Given: tm_ptr pointing to NUMERAL (BIT... _0), tm_id its emitted term ID
     Returns: (candle_tm_id, xlate_th_id) where xlate_th proves tm = candle_tm
     If no translation needed, returns (tm_id, ~1) *)
  and translate_numeral_hol4_to_candle tm_ptr tm_id : int * int =
    case shTerm heap tm_ptr of
      Comb (numeral_ptr, bits_ptr) =>
        (case numeral_value_of_bits bits_ptr of
           SOME n =>
             if not (needs_numeral_translation n) then (tm_id, ~1)
             else if n < 256 then
               (* Use cached translation theorem *)
               let
                 val xlate_th = candle_load_pth ("candle$NUM_XLATE_" ^ Int.toString n)
                 (* xlate_th: hol4_bits = candle_bits (without NUMERAL wrapper)
                    We need: NUMERAL hol4_bits = NUMERAL candle_bits
                    Use AP_TERM NUMERAL xlate_th *)
                 val numeral_const_id = emit_term numeral_ptr
                 val wrapped_th = let val id = alloc_th ()
                   in PFTWriter.Candle.mk_comb out id
                        (let val r = alloc_th () in PFTWriter.Candle.refl out r numeral_const_id; r end)
                        xlate_th;
                      id
                   end
                 (* Build the Candle numeral term *)
                 val candle_bits_id = emit_candle_numeral_bits n
                 val candle_tm_id = emit_comb numeral_const_id candle_bits_id
               in (candle_tm_id, wrapped_th) end
             else
               (* Large numeral: construct translation on-the-fly using
                  BIT2_eq_BIT0_SUC, SUC_0, SUC_BIT0, SUC_BIT1 *)
               let
                 val numeral_const_id = emit_term numeral_ptr
                 (* Translate the bits portion, get (candle_bits_id, bits_xlate_th)
                    where bits_xlate_th: hol4_bits = candle_bits *)
                 val (candle_bits_id, bits_xlate_th) =
                   translate_hol4_bits_to_candle bits_ptr
                 (* Wrap with NUMERAL: MK_COMB (REFL NUMERAL) bits_xlate_th *)
                 val wrapped_th = let val id = alloc_th ()
                   in PFTWriter.Candle.mk_comb out id
                        (let val r = alloc_th () in PFTWriter.Candle.refl out r numeral_const_id; r end)
                        bits_xlate_th;
                      id
                   end
                 val candle_tm_id = emit_comb numeral_const_id candle_bits_id
               in (candle_tm_id, wrapped_th) end
         | NONE => (tm_id, ~1))  (* Not a valid numeral, no translation *)
    | _ => (tm_id, ~1)

  (* Translate HOL4 bits (BIT1/BIT2/_0) to Candle bits (BIT0/BIT1/_0).
     Returns (candle_bits_id, xlate_th) where xlate_th: hol4_bits = candle_bits *)
  and translate_hol4_bits_to_candle bits_ptr : int * int =
    case shTerm heap bits_ptr of
      Const (id_ptr, _) =>
        let val (thy, name) = ident heap id_ptr
        in if (thy = "arithmetic" andalso name = "ZERO") orelse
              (thy = "num" andalso name = "0")
           then
             (* _0 -> _0, REFL *)
             let val bits_id = emit_term bits_ptr
                 val refl_th = let val id = alloc_th ()
                   in PFTWriter.Candle.refl out id bits_id; id end
             in (bits_id, refl_th) end
           else raise Fail "translate_hol4_bits: unexpected const"
        end
    | Comb (rator_ptr, arg_ptr) =>
        (case shTerm heap rator_ptr of
           Const (id_ptr, _) =>
             let val (thy, name) = ident heap id_ptr
             in if thy <> "arithmetic" then
                  raise Fail "translate_hol4_bits: unexpected rator"
                else if name = "BIT1" then
                  (* BIT1 n -> BIT1 (translate n)
                     If translate n gives (n', th) where th: n = n'
                     then MK_COMB (REFL BIT1) th gives BIT1 n = BIT1 n' *)
                  let
                    val (inner_candle, inner_th) = translate_hol4_bits_to_candle arg_ptr
                    val ty_num = emit_tyop "num" []
                    val ty_nn = emit_tyop "fun" [ty_num, ty_num]
                    val bit1_id = emit_const "BIT1" ty_nn
                    val bit1_refl = let val id = alloc_th ()
                      in PFTWriter.Candle.refl out id bit1_id; id end
                    val result_th = let val id = alloc_th ()
                      in PFTWriter.Candle.mk_comb out id bit1_refl inner_th; id end
                    val result_tm = emit_comb bit1_id inner_candle
                  in (result_tm, result_th) end
                else if name = "BIT2" then
                  (* BIT2 n -> BIT0 (SUC (translate n))
                     1. translate n to get (n', th1) where th1: n = n'
                     2. derive SUC n' to get (suc_n', th2) where th2: SUC n' = suc_n'
                     3. BIT2_eq_BIT0_SUC[n/n]: BIT2 n = BIT0 (SUC n)
                     4. Chain: BIT2 n = BIT0 (SUC n) = BIT0 (SUC n') = BIT0 suc_n' *)
                  let
                    val (inner_candle, inner_th) = translate_hol4_bits_to_candle arg_ptr
                    (* inner_th: n = n' (where n is HOL4 form, n' is Candle form) *)

                    (* Derive SUC n' = simplified form *)
                    val (suc_result, suc_th) = derive_suc_candle_bits inner_candle
                    (* suc_th: SUC n' = suc_result *)

                    (* Load BIT2_eq_BIT0_SUC and instantiate with original n *)
                    val bit2_eq = candle_load_pth "candle$BIT2_eq_BIT0_SUC"
                    val arg_id = emit_term arg_ptr
                    val ty_num = emit_tyop "num" []
                    val var_n = emit_var "n" ty_num
                    val bit2_inst = let val id = alloc_th ()
                      in PFTWriter.Candle.inst out id bit2_eq [(var_n, arg_id)]; id end
                    (* bit2_inst: BIT2 n = BIT0 (SUC n) *)

                    (* Now chain: BIT2 n = BIT0 (SUC n) = BIT0 (SUC n') = BIT0 suc_result *)
                    (* Step 1: Use inner_th (n = n') to get SUC n = SUC n' *)
                    val ty_nn = emit_tyop "fun" [ty_num, ty_num]
                    val suc_id = emit_const "SUC" ty_nn
                    val suc_refl = let val id = alloc_th ()
                      in PFTWriter.Candle.refl out id suc_id; id end
                    val suc_eq = let val id = alloc_th ()
                      in PFTWriter.Candle.mk_comb out id suc_refl inner_th; id end
                    (* suc_eq: SUC n = SUC n' *)

                    (* Step 2: Wrap with BIT0: BIT0 (SUC n) = BIT0 (SUC n') *)
                    val bit0_id = emit_const "BIT0" ty_nn
                    val bit0_refl = let val id = alloc_th ()
                      in PFTWriter.Candle.refl out id bit0_id; id end
                    val bit0_suc_eq = let val id = alloc_th ()
                      in PFTWriter.Candle.mk_comb out id bit0_refl suc_eq; id end
                    (* bit0_suc_eq: BIT0 (SUC n) = BIT0 (SUC n') *)

                    (* Step 3: Use suc_th to get BIT0 (SUC n') = BIT0 suc_result *)
                    val bit0_suc_simp = let val id = alloc_th ()
                      in PFTWriter.Candle.mk_comb out id bit0_refl suc_th; id end
                    (* bit0_suc_simp: BIT0 (SUC n') = BIT0 suc_result *)

                    (* Chain: bit2_inst TRANS bit0_suc_eq TRANS bit0_suc_simp *)
                    val step1 = let val id = alloc_th ()
                      in PFTWriter.Candle.trans out id bit2_inst bit0_suc_eq; id end
                    val result_th = let val id = alloc_th ()
                      in PFTWriter.Candle.trans out id step1 bit0_suc_simp; id end

                    val result_tm = emit_comb bit0_id suc_result
                  in (result_tm, result_th) end
                else raise Fail "translate_hol4_bits: unexpected BIT constructor"
             end
         | _ => raise Fail "translate_hol4_bits: rator not a const")
    | _ => raise Fail "translate_hol4_bits: unexpected term structure"

  (* Derive SUC of a Candle-form numeral bits, returning simplified result.
     Input: term ID for a Candle numeral bits (BIT0/BIT1/_0)
     Returns: (result_id, th) where th: SUC input = result *)
  and derive_suc_candle_bits bits_id : int * int =
    let
      val ty_num = emit_tyop "num" []
      val ty_nn = emit_tyop "fun" [ty_num, ty_num]
      val suc_id = emit_const "SUC" ty_nn
      val suc_bits = emit_comb suc_id bits_id

      (* Examine the structure of bits_id to determine which rule to apply.
         We need to look at what term bits_id represents. *)
      val (f_id, x_id) = (tm_part1_of bits_id, tm_part2_of bits_id)
    in
      if f_id < 0 then
        (* bits_id is a constant (_0) - use SUC_0: SUC _0 = BIT1 _0 *)
        let
          val suc_0_th = candle_load_pth "candle$SUC_0"
          val bit1_id = emit_const "BIT1" ty_nn
          val zero_id = emit_const "_0" ty_num
          val result = emit_comb bit1_id zero_id
        in (result, suc_0_th) end
      else
        (* bits_id is a Comb - check if it's BIT0 or BIT1 *)
        (* We identify BIT0 vs BIT1 by looking up the constant name.
           This is tricky since we only have term IDs. We need to check
           what constant f_id represents. *)
        (* For now, use the numeric value approach: examine the term structure *)
        (* Actually, we can check if f_id matches the BIT0 or BIT1 constant *)
        let
          val bit0_id = emit_const "BIT0" ty_nn
          val bit1_id = emit_const "BIT1" ty_nn
        in
          if f_id = bit0_id then
            (* SUC (BIT0 n) = BIT1 n, use SUC_BIT0 instantiated with n=x_id *)
            let
              val suc_bit0_th = candle_load_pth "candle$SUC_BIT0"
              val var_n = emit_var "n" ty_num
              val inst_th = let val id = alloc_th ()
                in PFTWriter.Candle.inst out id suc_bit0_th [(var_n, x_id)]; id end
              val result = emit_comb bit1_id x_id
            in (result, inst_th) end
          else if f_id = bit1_id then
            (* SUC (BIT1 n) = BIT0 (SUC n), use SUC_BIT1 then recurse *)
            let
              val suc_bit1_th = candle_load_pth "candle$SUC_BIT1"
              val var_n = emit_var "n" ty_num
              val inst_th = let val id = alloc_th ()
                in PFTWriter.Candle.inst out id suc_bit1_th [(var_n, x_id)]; id end
              (* inst_th: SUC (BIT1 n) = BIT0 (SUC n) where n = x_id *)

              (* Recurse to simplify SUC x_id *)
              val (suc_inner, suc_inner_th) = derive_suc_candle_bits x_id
              (* suc_inner_th: SUC x_id = suc_inner *)

              (* Wrap with BIT0: BIT0 (SUC x_id) = BIT0 suc_inner *)
              val bit0_refl = let val id = alloc_th ()
                in PFTWriter.Candle.refl out id bit0_id; id end
              val wrapped_th = let val id = alloc_th ()
                in PFTWriter.Candle.mk_comb out id bit0_refl suc_inner_th; id end
              (* wrapped_th: BIT0 (SUC x_id) = BIT0 suc_inner *)

              (* Chain: inst_th TRANS wrapped_th *)
              val result_th = let val id = alloc_th ()
                in PFTWriter.Candle.trans out id inst_th wrapped_th; id end
              val result = emit_comb bit0_id suc_inner
            in (result, result_th) end
          else
            raise Fail "derive_suc_candle_bits: unexpected BIT constructor"
        end
    end

  (* Build a Candle-form numeral bits term (using BIT0/BIT1/_0) for value n *)
  and emit_candle_numeral_bits 0 =
        (* _0 constant *)
        let val ty_num = emit_tyop "num" []
        in emit_const "_0" ty_num end
    | emit_candle_numeral_bits n =
        let val ty_num = emit_tyop "num" []
            val ty_nn = emit_tyop "fun" [ty_num, ty_num]
            val r = n mod 2
            val q = n div 2
            val inner = emit_candle_numeral_bits q
        in if r = 1 then
             emit_comb (emit_const "BIT1" ty_nn) inner
           else
             emit_comb (emit_const "BIT0" ty_nn) inner
        end

  (* Check if a heap term pointer is cv$Num (emitted as Cexp_num) *)
  and is_cv_num tm_ptr =
    case shTerm heap tm_ptr of
      Const (id_ptr, _) =>
        let val (thy, name) = ident heap id_ptr
        in thy = "cv" andalso name = "Num" end
    | _ => false

  (* Check if a heap term pointer is bare numeral bits (BIT1/BIT2/ZERO)
     without a NUMERAL wrapper.  These need BIT2→BIT0/BIT1 translation. *)
  and is_bare_bits_term tm_ptr =
    case shTerm heap tm_ptr of
      Const (id_ptr, _) =>
        let val (thy, name) = ident heap id_ptr
        in (thy = "arithmetic" andalso name = "ZERO") orelse
           (thy = "num" andalso name = "0")
        end
    | Comb (rator_ptr, _) =>
        (case shTerm heap rator_ptr of
           Const (id_ptr, _) =>
             let val (thy, name) = ident heap id_ptr
             in thy = "arithmetic" andalso
                  (name = "BIT1" orelse name = "BIT2")
             end
         | _ => false)
    | _ => false

  (* Translate all numerals in a term from HOL4 to Candle form.
     Returns (candle_tm_id, xlate_th_id) where xlate_th proves: original = candle_tm
     If no translation needed, returns (original_tm_id, ~1) *)
  and translate_term_numerals_hol4_to_candle tm_ptr tm_id : int * int =
    if is_numeral_term tm_ptr then
      translate_numeral_hol4_to_candle tm_ptr tm_id
    else if is_bare_bits_term tm_ptr then
      translate_hol4_bits_to_candle tm_ptr
    else
      case shTerm heap tm_ptr of
        Comb (rator_ptr, rand_ptr) =>
          if is_cv_num rator_ptr then
            let
              val rator_id = emit_term rator_ptr
              val rand_id = emit_term rand_ptr
              val (rand_c, rand_th) = translate_term_numerals_hol4_to_candle rand_ptr rand_id
            in
              if is_numeral_term rand_ptr then
                (* Cexp_num (NUMERAL bits) : no wrap needed, just chain any
                   BIT2 translation from rand *)
                if rand_th < 0 then (tm_id, ~1)
                else let val rator_eq = let val id = alloc_th ()
                       in PFTWriter.Candle.refl out id rator_id; id end
                     val comb_th = let val id = alloc_th ()
                       in PFTWriter.Candle.mk_comb out id rator_eq rand_th; id end
                 in (emit_comb rator_id rand_c, comb_th) end
              else
                (* Cexp_num X where X is not NUMERAL(...) : translate X,
                   then wrap with NUMERAL.
                   Proof: AP_TERM Cexp_num (TRANS rand_th (SYM (INST eq5))) *)
                let
                  val eq5 = candle_load_pth "candle$COMPUTE_EQ_5"
                  val ty_num = emit_tyop "num" []
                  val var_n = emit_var "n" ty_num
                  val eq5_inst = let val id = alloc_th ()
                    in PFTWriter.Candle.inst out id eq5 [(var_n, rand_c)]; id end
                  val eq5_sym = let val id = alloc_th ()
                    in PFTWriter.Candle.sym out id eq5_inst; id end
                  val inner_th = if rand_th < 0 then eq5_sym
                                 else let val id = alloc_th ()
                                   in PFTWriter.Candle.trans out id rand_th eq5_sym; id end
                  val rator_refl = let val id = alloc_th ()
                    in PFTWriter.Candle.refl out id rator_id; id end
                  val xlate_th = let val id = alloc_th ()
                    in PFTWriter.Candle.mk_comb out id rator_refl inner_th; id end
                  val numeral_id = emit_const "NUMERAL" (emit_tyop "fun" [ty_num, ty_num])
                in (emit_comb rator_id (emit_comb numeral_id rand_c), xlate_th) end
            end
          else
            let
              val rator_id = emit_term rator_ptr
              val rand_id = emit_term rand_ptr
              val (rator_c, rator_th) = translate_term_numerals_hol4_to_candle rator_ptr rator_id
              val (rand_c, rand_th) = translate_term_numerals_hol4_to_candle rand_ptr rand_id
            in
              if rator_th < 0 andalso rand_th < 0 then
                (tm_id, ~1)
              else
                let
                  val rator_eq = if rator_th < 0 then
                      let val id = alloc_th () in PFTWriter.Candle.refl out id rator_id; id end
                    else rator_th
                  val rand_eq = if rand_th < 0 then
                      let val id = alloc_th () in PFTWriter.Candle.refl out id rand_id; id end
                    else rand_th
                  val comb_th = let val id = alloc_th ()
                    in PFTWriter.Candle.mk_comb out id rator_eq rand_eq; id end
                in (emit_comb rator_c rand_c, comb_th) end
            end
      | Abs (var_ptr, body_ptr) =>
          let
            val var_id = emit_term var_ptr
            val body_id = emit_term body_ptr
            val (body_c, body_th) = translate_term_numerals_hol4_to_candle body_ptr body_id
          in
            if body_th < 0 then (tm_id, ~1)
            else
              let
                val abs_th = let val id = alloc_th ()
                  in PFTWriter.Candle.abs_thm out id var_id body_th; id end
                val result_tm = emit_abs var_id body_c
              in (result_tm, abs_th) end
          end
      | _ => (tm_id, ~1)  (* Var or Const, no translation *)

  (* ======================================================================= *)
  (* Theorem emission                                                        *)
  (* ======================================================================= *)

  and emit_thm (thm_ptr : Thm.thm ptr) : int =
    if not (isPtr thm_ptr) then raise Fail "emit_thm: not a ptr"
    else let val k = ptr thm_ptr
             val cached = th_memo_get k
    in if cached >= 0 then cached
       else let
         val (hyps_ptr, concl_ptr, proof_ptr) = shThm heap thm_ptr
         val proof = shProof heap proof_ptr
         val identity_th = case proof of
             save_dep_prf th => SOME th
           | GENL_prf (vars, th) =>
               if not (isPtr vars) then SOME th else NONE
           | GEN_ABS_prf (_, vars, th) =>
               if not (isPtr vars) then SOME th else NONE
           | INST_prf (subst, th) =>
               if not (isPtr subst) then SOME th else NONE
           | INST_TYPE_prf (subst, th) =>
               if not (isPtr subst) then SOME th else NONE
           | SUBST_prf (subst, _, th) =>
               if not (isPtr subst) then SOME th else NONE
           | _ => NONE
       in case identity_th of
            SOME th => let
              val inner_id = emit_thm th
            in th_memo_set k inner_id; inner_id end
          | NONE =>
       if is_candle
       then let
         val id = alloc_th ()
         val () = th_memo_set k id
       in case proof of
           Axiom_prf => let
             val name = (SOME (PIntMap.find k axiom_name_map))
                        handle PIntMap.NotFound => NONE
             (* In boolTheory, some axioms are already in the preamble *)
             val preamble_name =
               if thyname = "bool" then
                 case name of
                   SOME n => List.find (fn (k,_) => k = n)
                               candle_preamble_axiom
                 | NONE => NONE
               else NONE
           in case preamble_name of
                SOME (_, load_name) =>
                  (PFTWriter.load out id load_name; id)
              | NONE => let
                  val c = emit_term concl_ptr
                in PFTWriter.axiom out id c name; id end
           end
         | Disk_prf (dep_thy, b) => let
             val dep_id = thmId heap b
             val save_name = disk_save_name dep_thy dep_id
           in PFTWriter.load out id save_name; id end
         | _ => let
             val actual_id = emit_thm_candle id concl_ptr proof
             val () = th_memo_set k actual_id
             val () =
               if !emit_expect then let
                 val concl_id = emit_term concl_ptr
                 val hyp_ids = ref []
                 val () = appSet heap
                   (fn p => hyp_ids := emit_term p :: !hyp_ids) hyps_ptr
               in PFTWriter.expect out actual_id (!hyp_ids) concl_id end
               else ()
           in actual_id end
       end
       else let
         val id = alloc_th ()
         val () = th_memo_set k id
       in
         case proof of
           Axiom_prf => let
             val c = emit_term concl_ptr
             val name = (SOME (PIntMap.find k axiom_name_map))
                        handle PIntMap.NotFound => NONE
           in PFTWriter.axiom out id c name end
         | Disk_prf (dep_thy, b) => let
             val dep_id = thmId heap b
             val save_name = disk_save_name dep_thy dep_id
           in PFTWriter.load out id save_name end
         | _ =>
           case proof of
            ABS_prf (a, b) => let val a = emit_term a val b = emit_thm b
              in PFTWriter.HOL4.abs_thm out id a b end
          | ALPHA_prf (a, b) => let val a = emit_term a val b = emit_term b
              in PFTWriter.HOL4.alpha out id a b end
          | AP_TERM_prf (a, b) => let val a = emit_term a val b = emit_thm b
              in PFTWriter.HOL4.ap_term out id a b end
          | AP_THM_prf (a, b) => let val a = emit_thm a val b = emit_term b
              in PFTWriter.HOL4.ap_thm out id a b end
          | ASSUME_prf a => let val a = emit_term a
              in PFTWriter.HOL4.assume out id a end
          | BETA_CONV_prf a => let val a = emit_term a
              in PFTWriter.HOL4.beta_conv out id a end
          | Beta_prf a => let val a = emit_thm a
              in PFTWriter.HOL4.beta_thm out id a end
          | CCONTR_prf (a, b) => let val a = emit_term a val b = emit_thm b
              in PFTWriter.HOL4.ccontr out id a b end
          | CHOOSE_prf (a, b, c) => let
              val a = emit_term a val b = emit_thm b val c = emit_thm c
              in PFTWriter.HOL4.choose out id a b c end
          | CONJUNCT1_prf a => let val a = emit_thm a
              in PFTWriter.HOL4.conjunct1 out id a end
          | CONJUNCT2_prf a => let val a = emit_thm a
              in PFTWriter.HOL4.conjunct2 out id a end
          | CONJ_prf (a, b) => let val a = emit_thm a val b = emit_thm b
              in PFTWriter.HOL4.conj out id a b end
          | DISCH_prf (a, b) => let val a = emit_term a val b = emit_thm b
              in PFTWriter.HOL4.disch out id a b end
          | DISJ1_prf (a, b) => let val a = emit_thm a val b = emit_term b
              in PFTWriter.HOL4.disj1 out id a b end
          | DISJ2_prf (a, b) => let val a = emit_term a val b = emit_thm b
              in PFTWriter.HOL4.disj2 out id a b end
          | DISJ_CASES_prf (a, b, c) => let
              val a = emit_thm a val b = emit_thm b val c = emit_thm c
              in PFTWriter.HOL4.disj_cases out id a b c end
          | Def_const_list_prf (a, b) => let
              val a = emit_thm a
              val ids = list heap get_const_id b
              val names = List.map (fn (Thy,nm) => tr_name (Thy ^ "$" ^ nm)) ids
              val () = List.app (fn (Thy,nm) => mark_const (tr_name (Thy ^ "$" ^ nm))) ids
            in PFTWriter.HOL4.def_spec_gen out id a names end
          | Def_const_prf (a, b) => emit_def_const id (a, b)
          | Def_spec_prf (a, b) => let
              val a = emit_thm a
              val ids = list heap get_const_id b
              val names = List.map (fn (Thy,nm) => tr_name (Thy ^ "$" ^ nm)) ids
              val () = List.app (fn (Thy,nm) => mark_const (tr_name (Thy ^ "$" ^ nm))) ids
            in PFTWriter.HOL4.def_spec out id a names end
          | Def_tyop_prf (a, b, c) => let
              val _ = list heap emit_type a
              val () = if thyname = "bool"
                       then check_def tm_defs thyname "TYPE_DEFINITION"
                       else ()
              val b = emit_thm b
              val (Thy, Tyop) = get_type_id c
              val () = mark_type Tyop
            in PFTWriter.HOL4.def_tyop out id b (tr_name (Thy ^ "$" ^ Tyop)) end
          | EQ_IMP_RULE1_prf a => let val a = emit_thm a
              in PFTWriter.HOL4.eq_imp_rule1 out id a end
          | EQ_IMP_RULE2_prf a => let val a = emit_thm a
              in PFTWriter.HOL4.eq_imp_rule2 out id a end
          | EQ_MP_prf (a, b) => let val a = emit_thm a val b = emit_thm b
              in PFTWriter.HOL4.eq_mp out id a b end
          | EXISTS_prf (a, b, c) => let
              val a = emit_term a val b = emit_term b val c = emit_thm c
              in PFTWriter.HOL4.exists out id a b c end
          | GENL_prf (a, b) => let
              val tms = list heap emit_term a
              val b = emit_thm b
            in PFTWriter.HOL4.genl out id b tms end
          | GEN_ABS_prf (a, b, c) => let
              val opt = option heap emit_term a
              val tms = list heap emit_term b
              val c = emit_thm c
            in case opt of
                 SOME c_id => PFTWriter.HOL4.gen_abs out id c c_id tms
               | NONE => PFTWriter.HOL4.absl out id c tms
            end
          | GEN_prf (a, b) => let val a = emit_term a val b = emit_thm b
              in PFTWriter.HOL4.gen out id a b end
          | INST_TYPE_prf (a, b) => let
              val pairs = list heap (tuple2 heap (emit_type, emit_type)) a
              val b = emit_thm b
            in PFTWriter.HOL4.inst_type out id b pairs end
          | INST_prf (a, b) => let
              val pairs = list heap (tuple2 heap (emit_term, emit_term)) a
              val b = emit_thm b
            in PFTWriter.HOL4.inst out id b pairs end
          | MK_COMB_prf (a, b) => let val a = emit_thm a val b = emit_thm b
              in PFTWriter.HOL4.mk_comb out id a b end
          | MP_prf (a, b) => let val a = emit_thm a val b = emit_thm b
              in PFTWriter.HOL4.mp out id a b end
          | Mk_abs_prf (a, _, c) => let
              val a = emit_thm a
              val c = emit_thm c
            in PFTWriter.HOL4.mk_abs_thm out id a c end
          | Mk_comb_prf (a, b, c) => let
              val a = emit_thm a val b = emit_thm b val c = emit_thm c
            in PFTWriter.HOL4.mk_comb_thm out id a b c end
          | NOT_ELIM_prf a => let val a = emit_thm a
              in PFTWriter.HOL4.not_elim out id a end
          | NOT_INTRO_prf a => let val a = emit_thm a
              in PFTWriter.HOL4.not_intro out id a end
          | REFL_prf a => let val a = emit_term a
              in PFTWriter.HOL4.refl out id a end
          | SPEC_prf (a, b) => let val a = emit_term a val b = emit_thm b
              in PFTWriter.HOL4.spec out id a b end
          | SUBST_prf (a, b, c) => let
              val pairs = list heap (tuple2 heap (emit_term, emit_thm)) a
              val b = emit_term b
              val c = emit_thm c
            in PFTWriter.HOL4.subst out id b c pairs end
          | SYM_prf a => let val a = emit_thm a
              in PFTWriter.HOL4.sym out id a end
          | Specialize_prf (a, b) => let
              val a = emit_term a val b = emit_thm b
            in PFTWriter.HOL4.specialize out id a b end
          | TRANS_prf (a, b) => let val a = emit_thm a val b = emit_thm b
              in PFTWriter.HOL4.trans out id a b end
          | compute_prf (a, b) => emit_compute id (tuple2 heap (I, I) a, b)
          | deductAntisym_prf (a, b) => let
              val a = emit_thm a val b = emit_thm b
            in PFTWriter.HOL4.deductAntisym out id a b end
          | deleted_prf => raise Fail "emit_thm: deleted"
          | save_dep_prf _ => raise Fail "unreachable"
          | Axiom_prf => raise Fail "unreachable: handled above"
          | Disk_prf _ => raise Fail "unreachable: handled above"
       ; id end end
    end

  (* ======================================================================= *)
  (* Def_const (HOL4)                                                        *)
  (* ======================================================================= *)

  and emit_def_const thm_id (rhs_p, const_ptr) = let
    val rhs_id = emit_term rhs_p
    val (Thy, Name) = get_const_id const_ptr
    val rhs_ty_id = pft_type_of rhs_id
    val bool_ty_id = emit_tyop "min$bool" []
    val fun_ty1_id = emit_tyop "min$fun" [rhs_ty_id, bool_ty_id]
    val eq_ty_id = emit_tyop "min$fun" [rhs_ty_id, fun_ty1_id]
    val var_id = emit_var Name rhs_ty_id
    val eq_id = emit_const "min$=" eq_ty_id
    val eq_var_id = emit_comb eq_id var_id
    val eq_tm_id = emit_comb eq_var_id rhs_id
    val assume_id = alloc_th ()
    val () = PFTWriter.HOL4.assume out assume_id eq_tm_id
    val () = mark_const (tr_name (thyname ^ "$" ^ Name))
    val () = PFTWriter.HOL4.def_spec_gen out thm_id assume_id
        [tr_name (thyname ^ "$" ^ Name)]
  in () end

  (* Hash-consed helpers for synthesized objects *)
  and emit_tyop name args =
    let val key = TyOpK(name, args)
    in case ty_lookup key of
         SOME id => id
       | NONE => let val id = alloc_ty ()
         in PFTWriter.tyop out id name args;
            ty_insert key id;
            (case args of
               [_, r] => if name = fun_tyname then ty_ret_set id r else ()
             | _ => ());
            id
         end
    end

  and emit_var name ty_id =
    let val key = (name, ty_id)
    in case var_lookup key of
         SOME id => id
       | NONE => let val id = alloc_tm ()
         in PFTWriter.var out id name ty_id;
            var_insert key id;
            tm_types_set id ty_id;
            var_names_set id name;
            id
         end
    end

  (* Like emit_var but uses fresh_binder_name for unique binder names.
     Used for synthesized lambda binders in Candle translations. *)
  and emit_binder name ty_id =
    let val id = alloc_tm ()
        val bname = fresh_binder_name name
    in PFTWriter.var out id bname ty_id;
       tm_types_set id ty_id;
       var_names_set id bname;
       id
    end

  and emit_const name ty_id =
    let val key = (name, ty_id)
    in case const_lookup key of
         SOME id => id
       | NONE => let val id = alloc_tm ()
         in PFTWriter.const out id name ty_id;
            const_insert key id;
            tm_types_set id ty_id; id
         end
    end

  and emit_abs var_id body_id =
    case IntPairTable.lookup abs_ht (var_id, body_id) of
      SOME id => id
    | NONE => let val id = alloc_tm ()
      in PFTWriter.abs out id var_id body_id;
         IntPairTable.insert abs_ht (var_id, body_id) id;
         tm_parts_set id (var_id, body_id);
         tm_types_set id (emit_tyop fun_tyname
           [pft_type_of var_id, pft_type_of body_id]);
         id
      end

  and emit_comb rator_id rand_id =
    case IntPairTable.lookup comb_ht (rator_id, rand_id) of
      SOME id => id
    | NONE => let val id = alloc_tm ()
      in PFTWriter.comb out id rator_id rand_id;
         IntPairTable.insert comb_ht (rator_id, rand_id) id;
         tm_parts_set id (rator_id, rand_id);
         tm_types_set id (pft_ret_type (pft_type_of rator_id));
         id
      end

  (* Substitute old_id -> new_id in a PFT term, rebuilding via emit_comb/
     emit_abs.  Distinguishes COMB from ABS by checking comb_ht: all COMBs
     (heap and synthesised) are registered there; ABSs never are. *)
  and pft_subst_tm old_id new_id tm_id =
    if tm_id = old_id then new_id
    else let val f = tm_part1_of tm_id
    in if f < 0 then tm_id (* VAR or CONST — no children *)
       else let val x = tm_part2_of tm_id
                val f' = pft_subst_tm old_id new_id f
                val x' = pft_subst_tm old_id new_id x
            in if f' = f andalso x' = x then tm_id
               else case IntPairTable.lookup comb_ht (f, x) of
                      SOME _ => emit_comb f' x'
                    | NONE   => emit_abs f' x'
            end
    end

  (* Like pft_subst_tm but only substitutes free occurrences of old_id.
     Tracks shadowing when entering ABS nodes. *)
  and pft_rename_free old_id new_id tm_id = let
    fun go shadowed t =
      if t = old_id then (if shadowed then t else new_id)
      else let val f = tm_part1_of t
      in if f < 0 then t (* VAR or CONST *)
         else let val x = tm_part2_of t
         in if isSome (IntPairTable.lookup comb_ht (f, x)) then
              (* COMB: recurse into both children *)
              let val f' = go shadowed f
                  val x' = go shadowed x
              in if f' = f andalso x' = x then t else emit_comb f' x' end
            else
              (* ABS: binder is f, body is x; shadow if binder = old_id *)
              let val x' = go (shadowed orelse f = old_id) x
              in if x' = x then t else emit_abs f x' end
         end
      end
  in go false tm_id end

  (* ======================================================================= *)
  (* compute (HOL4)                                                          *)
  (* ======================================================================= *)

  and emit_compute thm_id ((compute_args_ptr, ths_ptr), tm_p) = let
    val () = emit_compute_init compute_args_ptr
    val th_id_list = list heap emit_thm ths_ptr
    val tm_id = emit_term tm_p
  in PFTWriter.HOL4.compute out thm_id tm_id th_id_list end

  and emit_compute_init (args_ptr : compute_args ptr) : unit = let
    val k = ptr args_ptr
  in if !hol4_compute_init_key = k then ()
     else if !hol4_compute_init_key >= 0 then
       raise Fail "PFTEmit: multiple distinct HOL4 COMPUTE_INIT contexts"
     else let
       val {num_type, char_eqns, cval_type, cval_terms} = shComputeArgs heap args_ptr
       val num_ty = emit_type num_type
       val cval_ty = emit_type cval_type
       val char_eqns = list heap (tuple2 heap (str heap, emit_thm)) char_eqns
       val cval_terms = list heap (tuple2 heap (str heap, emit_term)) cval_terms
       val () = PFTWriter.HOL4.compute_init out num_ty cval_ty
           char_eqns cval_terms
       val () = hol4_compute_init_key := k
     in () end
  end

  (* ======================================================================= *)
  (* Process exports                                                         *)
  (* ======================================================================= *)

  val () = appList heap (fn p => let
    val (nm, (thp, _)) = tuple3 heap (str heap, I, I) p
    val thm_id = emit_thm thp
  in PFTWriter.save out (thyname ^ "$" ^ nm) thm_id end) all_thms

  val anon_idx = ref 0
  val () = appList heap (fn p => let
    val i = !anon_idx
    val () = anon_idx := i + 1
    val thm_id = emit_thm p
  in PFTWriter.save out (thyname ^ "#" ^ Int.toString i) thm_id end) anon_thms

  (* Ensure all theory constants/types are introduced *)

  val () = appList heap (fn p => let
    val (Name, ty_ptr) = tuple2 heap (str heap, I) p
    val () = check_def tm_defs thyname Name
  in if is_const_done (tr_name (thyname ^ "$" ^ Name)) then ()
     else let
       val ty_id = emit_type ty_ptr
       val () = mark_const (tr_name (thyname ^ "$" ^ Name))
     in PFTWriter.new_const out (tr_name (thyname ^ "$" ^ Name)) ty_id end
  end) constants

  val () = appList heap (fn p => let
    val (Tyop, arity) = tuple2 heap (str heap, int) p
    val () = check_def ty_defs thyname Tyop
  in if is_type_done Tyop then ()
     else (mark_type Tyop;
           PFTWriter.new_type out (tr_name (thyname ^ "$" ^ Tyop)) arity)
  end) types

  (* ======================================================================= *)
  (* Close output                                                            *)
  (* ======================================================================= *)

  val n_ty = !next_ty
  val n_tm = !next_tm
  val n_th = !next_th

in
  PFTWriter.closeOut out
    {n_ty = n_ty, n_tm = n_tm, n_th = n_th}
end

end
