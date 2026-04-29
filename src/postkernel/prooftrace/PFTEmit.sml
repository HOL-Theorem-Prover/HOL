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

(* Compute preamble: emitted once on first compute_prf encounter *)
(* at module level so it persists across emit_theory calls *)
val compute_preamble_emitted = ref false

(* TYPE_DEFINITION_THM_FREE: lazily derived during boolTheory, SAVEd
   as candle$TYPE_DEFINITION_THM_FREE so later theories can LOAD it.
   Tracks whether the SAVE has been emitted in the current PFT file. *)
val tydef_thm_free_saved : bool ref = ref false

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
    {file = output, binary = binary, version = 1, ruleset = ruleset_str}

  (* --- Emit pass state --------------------------------------------------- *)

  (* ID counters *)
  val next_ty = ref 0
  val next_tm = ref 0
  val next_th = ref 0
  val next_ci = ref 0

  fun alloc_ty () = let val id = !next_ty in next_ty := id + 1; id end
  fun alloc_tm () = let val id = !next_tm in next_tm := id + 1; id end
  fun alloc_th () = let val id = !next_th in next_th := id + 1; id end
  fun alloc_ci () = let val id = !next_ci in next_ci := id + 1; id end

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

  (* Candle compute context: initialized once after preamble, reused for all COMPUTE calls *)
  val candle_compute_init_id : int ref = ref ~1

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
  fun pft_is_comb id =
    let val f = DArray.sub(tm_part1, id)
        val x = DArray.sub(tm_part2, id)
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
        val bname = fresh_binder_name s
        val () = PFTWriter.var out V bname ty_id
        val () = tm_types_set V ty_id
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

    (* ===================================================================== *)
    (* Candle derived-rule helpers                                           *)
    (* These emit sequences of Candle commands and return theorem IDs.       *)
    (* ===================================================================== *)

    (* do_MP
       -------
       Signature: ith: A ⊢ a ==> b
                  ant_th: B ⊢ a
                  a_tm, b_tm: term IDs for a and b
                  Result: A ∪ B ⊢ b

       Pro-forma: candle$MP = {p} ⊢ (p ==> q) = q

       Derivation:
         rth = INST candle$MP [p↦a, q↦b]
             : {a} ⊢ (a ==> b) = b
         c_deduct ant_th rth
             : DEDUCT_ANTISYM (B ⊢ a) ({a} ⊢ (a==>b)=b)
             : (B \ {(a==>b)=b}) ∪ ({a} \ {a}) ⊢ a = ((a==>b)=b)
             : B ⊢ a = ((a ==> b) = b)
         c_eq_mp (c_deduct ant_th rth) ant_th
             : EQ_MP (B ⊢ a = ((a==>b)=b)) (B ⊢ a)
             : B ⊢ (a ==> b) = b
         c_eq_mp (...) ith
             : EQ_MP (B ⊢ (a==>b)=b) (A ⊢ a==>b)
             : A ∪ B ⊢ b
    *)
    fun do_MP ith a_tm b_tm ant_th =
      let val rth = c_inst (candle_load_pth "candle$MP")
                      [(pvar_p, a_tm), (pvar_q, b_tm)]
                    (* rth: {a} ⊢ (a ==> b) = b *)
          val da = c_deduct ant_th rth
                   (* da: B ⊢ a = ((a ==> b) = b) *)
          val eq1 = c_eq_mp da ant_th
                    (* eq1: B ⊢ (a ==> b) = b *)
      in c_eq_mp eq1 ith end
         (* result: A ∪ B ⊢ b *)

    (* do_CONJ
       --------
       Signature: th1: A ⊢ a
                  th2: B ⊢ b
                  a_tm, b_tm: term IDs for a and b
                  Result: A ∪ B ⊢ a ∧ b

       Pro-forma: candle$CONJ = {p, q} ⊢ p ∧ q

       Derivation:
         ci = INST candle$CONJ [p↦a, q↦b]
            : {a, b} ⊢ a ∧ b
         c_prove_hyp th1 ci
            : PROVE_HYP (A ⊢ a) ({a, b} ⊢ a ∧ b)
            : A ∪ ({a, b} \ {a}) ⊢ a ∧ b
            : A ∪ {b} ⊢ a ∧ b
         c_prove_hyp th2 (...)
            : PROVE_HYP (B ⊢ b) (A ∪ {b} ⊢ a ∧ b)
            : B ∪ ((A ∪ {b}) \ {b}) ⊢ a ∧ b
            : A ∪ B ⊢ a ∧ b
    *)
    fun do_CONJ a_tm b_tm th1 th2 =
      let val ci = c_inst (candle_load_pth "candle$CONJ")
                     [(pvar_p, a_tm), (pvar_q, b_tm)]
                   (* ci: {a, b} ⊢ a ∧ b *)
          val step1 = c_prove_hyp th1 ci
                      (* step1: A ∪ {b} ⊢ a ∧ b *)
      in c_prove_hyp th2 step1 end
         (* result: A ∪ B ⊢ a ∧ b *)

    (* do_CONJUNCT1
       -------------
       Signature: th: A ⊢ a ∧ b
                  a_tm, b_tm: term IDs for a and b
                  Result: A ⊢ a

       Pro-forma: candle$CONJUNCT1 = {p ∧ q} ⊢ p

       Derivation:
         c1i = INST candle$CONJUNCT1 [p↦a, q↦b]
             : {a ∧ b} ⊢ a
         c_prove_hyp th c1i
             : PROVE_HYP (A ⊢ a ∧ b) ({a ∧ b} ⊢ a)
             : A ∪ ({a ∧ b} \ {a ∧ b}) ⊢ a
             : A ⊢ a
    *)
    fun do_CONJUNCT1 a_tm b_tm th =
      let val c1i = c_inst (candle_load_pth "candle$CONJUNCT1")
                      [(pvar_p, a_tm), (pvar_q, b_tm)]
                    (* c1i: {a ∧ b} ⊢ a *)
      in c_prove_hyp th c1i end
         (* result: A ⊢ a *)

    (* do_CONJUNCT2
       -------------
       Signature: th: A ⊢ a ∧ b
                  a_tm, b_tm: term IDs for a and b
                  Result: A ⊢ b

       Pro-forma: candle$CONJUNCT2 = {p ∧ q} ⊢ q

       Derivation:
         c2i = INST candle$CONJUNCT2 [p↦a, q↦b]
             : {a ∧ b} ⊢ b
         c_prove_hyp th c2i
             : A ⊢ b
    *)
    fun do_CONJUNCT2 a_tm b_tm th =
      let val c2i = c_inst (candle_load_pth "candle$CONJUNCT2")
                      [(pvar_p, a_tm), (pvar_q, b_tm)]
                    (* c2i: {a ∧ b} ⊢ b *)
      in c_prove_hyp th c2i end
         (* result: A ⊢ b *)

    (* do_DISCH
       ---------
       Signature: th_c: A ⊢ c
                  a_tm, c_tm: term IDs for a and c
                  Result: A \ {a} ⊢ a ==> c

       Pro-formas used:
         candle$CONJ = {p, q} ⊢ p ∧ q
         candle$CONJUNCT1 = {p ∧ q} ⊢ p
         candle$DISCH = ⊢ ((p ∧ q) = p) = (p ==> q)

       Derivation:
         ci = INST candle$CONJ [p↦a, q↦c]
            : {a, c} ⊢ a ∧ c

         c_assume a_tm
            : {a} ⊢ a

         c_prove_hyp (c_assume a_tm) ci
            : PROVE_HYP ({a} ⊢ a) ({a, c} ⊢ a ∧ c)
            : {a} ∪ ({a, c} \ {a}) ⊢ a ∧ c
            : {a, c} ⊢ a ∧ c

         cj = c_prove_hyp th_c (c_prove_hyp (c_assume a_tm) ci)
            : PROVE_HYP (A ⊢ c) ({a, c} ⊢ a ∧ c)
            : A ∪ ({a, c} \ {c}) ⊢ a ∧ c
            : A ∪ {a} ⊢ a ∧ c

         c1i = INST candle$CONJUNCT1 [p↦a, q↦c]
             : {a ∧ c} ⊢ a

         c_assume a_and_c
             : {a ∧ c} ⊢ a ∧ c

         c_prove_hyp (c_assume a_and_c) c1i
             : PROVE_HYP ({a ∧ c} ⊢ a ∧ c) ({a ∧ c} ⊢ a)
             : {a ∧ c} ∪ ({a ∧ c} \ {a ∧ c}) ⊢ a
             : {a ∧ c} ⊢ a

         da = c_deduct cj (c_prove_hyp (c_assume a_and_c) c1i)
            : DEDUCT_ANTISYM (A ∪ {a} ⊢ a ∧ c) ({a ∧ c} ⊢ a)
            : ((A ∪ {a}) \ {a}) ∪ ({a ∧ c} \ {a ∧ c}) ⊢ (a ∧ c) = a
            : (A ∪ {a}) \ {a} ⊢ (a ∧ c) = a

         Note: (A ∪ {a}) \ {a} = A \ {a}  (if a ∈ A then A, else A)
               More precisely: = A if a ∉ A, = A \ {a} if a ∈ A
               In either case this equals A \ {a}.

         di = INST candle$DISCH [p↦a, q↦c]
            : ⊢ ((a ∧ c) = a) = (a ==> c)

         c_eq_mp di da
            : EQ_MP (⊢ ((a∧c)=a) = (a==>c)) (A\{a} ⊢ (a∧c)=a)
            : A \ {a} ⊢ a ==> c
    *)
    fun do_DISCH a_tm c_tm th_c =
      let val a_and_c = emit_comb (emit_comb and_const a_tm) c_tm
          val ci = c_inst (candle_load_pth "candle$CONJ")
                     [(pvar_p, a_tm), (pvar_q, c_tm)]
                   (* ci: {a, c} ⊢ a ∧ c *)
          val cj = c_prove_hyp th_c (c_prove_hyp (c_assume a_tm) ci)
                   (* cj: A ∪ {a} ⊢ a ∧ c *)
          val c1i = c_inst (candle_load_pth "candle$CONJUNCT1")
                      [(pvar_p, a_tm), (pvar_q, c_tm)]
                    (* c1i: {a ∧ c} ⊢ a *)
          val da = c_deduct cj (c_prove_hyp (c_assume a_and_c) c1i)
                   (* da: (A ∪ {a}) \ {a} ⊢ (a ∧ c) = a
                        = A \ {a} ⊢ (a ∧ c) = a *)
          val di = c_inst (candle_load_pth "candle$DISCH")
                     [(pvar_p, a_tm), (pvar_q, c_tm)]
                   (* di: ⊢ ((a ∧ c) = a) = (a ==> c) *)
      in c_eq_mp di da end
         (* result: A \ {a} ⊢ a ==> c *)

    (* do_GEN
       -------
       Signature: th_s: A ⊢ s
                  v_tm: term ID of free variable v in s
                  v_ty: type ID of v
                  s_tm: term ID for s
                  Result: A ⊢ ∀v. s
                  Side condition: v not free in A

       Pro-formas used:
         candle$EQT_INTRO = ⊢ t = (t = T)
         candle$GEN = ⊢ (P = λx. T) = !P

       Note: We create a fresh binder bv and substitute v_tm -> bv
       to avoid using a free variable as a binder (which would violate
       PFTRename's uniqueness assumption that each binder VAR ID appears
       as the first argument of exactly one ABS command).

       Derivation:
         bv = fresh binder variable with unique name "v pft%N"
         s_tm_bv = s[bv/v]  (substitute v with bv in the term)
         th_s_bv = INST th_s [v↦bv]
                 : A[bv/v] ⊢ s[bv/v]
                 : A ⊢ s[bv/v]  (since v not free in A)

         eqt_pth = INST candle$EQT_INTRO [t↦s[bv/v]]
                 : ⊢ s[bv/v] = (s[bv/v] = T)

         c_eq_mp eqt_pth th_s_bv
                 : EQ_MP (⊢ s[bv/v] = (s[bv/v] = T)) (A ⊢ s[bv/v])
                 : A ⊢ s[bv/v] = T

         abs_eq = c_abs bv (A ⊢ s[bv/v] = T)
                : A ⊢ (λbv. s[bv/v]) = (λbv. T)
                  (bv not free in A by side condition)

         gen_inst = INST (INST_TYPE candle$GEN ['a↦v_ty]) [P↦(λbv. s[bv/v])]
                  : ⊢ ((λbv. s[bv/v]) = (λx. T)) = !(λbv. s[bv/v])

         c_eq_mp gen_inst abs_eq
                  : A ⊢ !(λbv. s[bv/v])
                  : A ⊢ ∀bv. s[bv/v]

         This is alpha-equivalent to A ⊢ ∀v. s
    *)
    fun do_GEN v_tm v_ty s_tm th_s =
      let val bv = emit_binder "v" v_ty
                   (* bv: fresh binder with unique name *)
          val s_tm_bv = pft_subst_tm v_tm bv s_tm
                        (* s_tm_bv: s[bv/v] *)
          val th_s_bv = c_inst th_s [(v_tm, bv)]
                        (* th_s_bv: A ⊢ s[bv/v] *)
          val eqt_pth = c_inst (candle_load_pth "candle$EQT_INTRO")
                           [(pvar_t, s_tm_bv)]
                        (* eqt_pth: ⊢ s[bv/v] = (s[bv/v] = T) *)
          val abs_eq = c_abs bv (c_eq_mp eqt_pth th_s_bv)
                       (* abs_eq: A ⊢ (λbv. s[bv/v]) = (λbv. T) *)
          val Ab = emit_tyop "fun" [v_ty, bool_tyid]
          val gen_inst = c_inst (c_inst_type (candle_load_pth "candle$GEN")
                           [(tyvar_A, v_ty)])
                           [(emit_var "P" Ab, emit_abs bv s_tm_bv)]
                         (* gen_inst: ⊢ ((λbv. s[bv/v]) = (λx. T)) = !(λbv. s[bv/v]) *)
      in c_eq_mp gen_inst abs_eq end
         (* result: A ⊢ ∀bv. s[bv/v]  ≡α  A ⊢ ∀v. s *)

    (* do_SPEC
       --------
       Signature: th_forall: A ⊢ ∀v. s  (i.e., A ⊢ !pred_tm where pred_tm = λv. s)
                  t_tm: term ID to substitute for v
                  pred_tm: term ID for λv. s
                  forall_tm: term ID for !pred_tm
                  v_ty: type of the bound variable
                  Result: A ⊢ s[t/v]

       Pro-forma used:
         candle$SPEC = ⊢ (!P) ==> P x

       Derivation:
         spec_inst = INST (INST_TYPE candle$SPEC ['a↦v_ty]) [P↦pred_tm, x↦t_tm]
                   : ⊢ (!pred_tm) ==> pred_tm t_tm
                   : ⊢ (∀v. s) ==> (λv. s) t

         mp_result = do_MP spec_inst forall_tm (pred_tm t_tm) th_forall
                   : A ⊢ (λv. s) t

         actual_bv = binder variable of pred_tm (from pft_dest_abs)
         beta_th = c_beta (emit_comb pred_tm actual_bv)
                 : ⊢ (λv. s) v = s
                 (Candle BETA requires the argument to be exactly the binder)

         beta_inst = if actual_bv = t_tm then beta_th
                     else INST beta_th [actual_bv↦t_tm]
                   : ⊢ (λv. s) t = s[t/v]

         c_eq_mp beta_inst mp_result
                   : A ⊢ s[t/v]
    *)
    fun do_SPEC t_tm pred_tm forall_tm v_ty th_forall =
      let val Ab = emit_tyop "fun" [v_ty, bool_tyid]
          val spec_inst = c_inst (c_inst_type (candle_load_pth "candle$SPEC")
                            [(tyvar_A, v_ty)])
                            [(emit_var "P" Ab, pred_tm),
                             (emit_var "x" v_ty, t_tm)]
                          (* spec_inst: ⊢ (!pred_tm) ==> pred_tm t_tm *)
          val mp_result = do_MP spec_inst forall_tm (emit_comb pred_tm t_tm) th_forall
                          (* mp_result: A ⊢ pred_tm t_tm = (λv. s) t *)
          val (actual_bv, _) = pft_dest_abs pred_tm
          val beta_th = c_beta (emit_comb pred_tm actual_bv)
                        (* beta_th: ⊢ (λv. s) v = s *)
          val beta_inst = if actual_bv = t_tm then beta_th
            else c_inst beta_th [(actual_bv, t_tm)]
                        (* beta_inst: ⊢ (λv. s) t = s[t/v] *)
      in c_eq_mp beta_inst mp_result end
         (* result: A ⊢ s[t/v] *)

    (* do_DOUBLE_SPEC
       ----------------
       Signature: th: ⊢ ∀v1. ∀v2. body
                  v1_tm, v2_tm: term IDs for free variables to substitute
                  v1_ty, v2_ty: types of v1 and v2
                  inner_body: term ID for body with v1, v2 free
                  Result: ⊢ body  (with v1_tm, v2_tm free)

       Note: The input theorem has binders that we don't know the IDs of,
       so we construct fresh predicates using fresh binders bv1, bv2.
       do_SPEC will apply INST to convert from bv1/bv2 to v1_tm/v2_tm.

       Derivation:
         We build:
           outer_pred = λbv1. !(λbv2. body[bv1/v1, bv2/v2])
           inner_pred = λbv2. body[bv1/v1, bv2/v2]

         step1 = do_SPEC v1_tm outer_pred (!outer_pred) v1_ty th
               : ⊢ !(λbv2. body[bv1/v1, bv2/v2])[v1/bv1]
               : ⊢ !(λbv2. body[v1/v1, bv2/v2])
               : ⊢ ∀bv2. body[bv2/v2]  (since body[v1/v1] = body when v1 is the same var)

         inner_pred_after = λbv2. body[bv2/v2]  (with v1 already at v1_tm)

         result = do_SPEC v2_tm inner_pred_after (!inner_pred_after) v2_ty step1
                : ⊢ body[bv2/v2][v2/bv2]
                : ⊢ body
    *)
    fun do_DOUBLE_SPEC th v1_tm v1_ty v2_tm v2_ty inner_body = let
        val bv1 = emit_binder "v" v1_ty
        val bv2 = emit_binder "v" v2_ty
        (* Substitute free vars with binders in inner_body *)
        val inner_body_bv = pft_subst_tm v1_tm bv1 (pft_subst_tm v2_tm bv2 inner_body)
                            (* inner_body_bv: body[bv1/v1, bv2/v2] *)
        val inner_pred = emit_abs bv2 inner_body_bv
                         (* inner_pred: λbv2. body[bv1/v1, bv2/v2] *)
        val Ab2 = emit_tyop "fun" [v2_ty, bool_tyid]
        val forall2_const = emit_const "!" (emit_tyop "fun" [Ab2, bool_tyid])
        val inner_forall = emit_comb forall2_const inner_pred
                           (* inner_forall: ∀bv2. body[bv1/v1, bv2/v2] *)
        val outer_pred = emit_abs bv1 inner_forall
                         (* outer_pred: λbv1. ∀bv2. body[bv1/v1, bv2/v2] *)
        val Ab1 = emit_tyop "fun" [v1_ty, bool_tyid]
        val forall1_const = emit_const "!" (emit_tyop "fun" [Ab1, bool_tyid])
        val step1 = do_SPEC v1_tm outer_pred (emit_comb forall1_const outer_pred) v1_ty th
                    (* step1: ⊢ ∀bv2. body[bv2/v2]
                       (do_SPEC internally does INST [bv1↦v1_tm]) *)
        (* For second SPEC, we need pred with v1 already specialized *)
        val inner_body_v1_bv2 = pft_subst_tm v2_tm bv2 inner_body
                                (* inner_body_v1_bv2: body[bv2/v2] (v1 stays as v1_tm) *)
        val inner_pred_after = emit_abs bv2 inner_body_v1_bv2
                               (* inner_pred_after: λbv2. body[bv2/v2] *)
    in do_SPEC v2_tm inner_pred_after (emit_comb forall2_const inner_pred_after) v2_ty step1 end
       (* result: ⊢ body *)

    (* do_beta_reduce
       ---------------
       Signature: lam_tm: term ID for (λv. body)
                  arg_tm: term ID for argument t
                  Result: ⊢ (λv. body) t = body[t/v]

       Note: Candle's BETA rule only works on (λv. body) v where the
       argument is exactly the bound variable. We use INST to generalize.

       Derivation:
         actual_bv = bound variable of lam_tm
         beta_th = BETA ((λv. body) v)
                 : ⊢ (λv. body) v = body

         if actual_bv = arg_tm:
           return beta_th
         else:
           INST beta_th [actual_bv ↦ arg_tm]
           : ⊢ (λv. body) t = body[t/v]
    *)
    fun do_beta_reduce lam_tm arg_tm =
      let val (actual_bv, _) = pft_dest_abs lam_tm
          val beta_th = c_beta (emit_comb lam_tm actual_bv)
                        (* beta_th: ⊢ (λv. body) v = body *)
      in if actual_bv = arg_tm then beta_th
         else c_inst beta_th [(actual_bv, arg_tm)] end
         (* result: ⊢ (λv. body) t = body[t/v] *)

    (* do_EXISTS
       ----------
       Signature: th: A ⊢ body[witness/v]
                  pred_tm: term ID for λv. body
                  var_tm: term ID for v (binder of pred_tm)
                  witness_tm: term ID for witness
                  v_ty: type of v
                  Result: A ⊢ ∃v. body

       Pro-forma: candle$EXISTS = {P x} ⊢ ?P

       Derivation:
         exists_inst = INST (INST_TYPE candle$EXISTS ['a↦v_ty])
                            [P↦pred_tm, x↦witness_tm]
                     : {pred_tm witness_tm} ⊢ ?pred_tm
                     : {(λv. body) witness} ⊢ ∃v. body

         do_beta_reduce pred_tm witness_tm
                     : ⊢ (λv. body) witness = body[witness/v]

         c_sym (...)
                     : ⊢ body[witness/v] = (λv. body) witness

         witness_hyp = c_eq_mp (c_sym (do_beta_reduce ...)) th
                     : EQ_MP (⊢ body[w/v] = (λv.body) w) (A ⊢ body[w/v])
                     : A ⊢ (λv. body) witness

         c_prove_hyp witness_hyp exists_inst
                     : PROVE_HYP (A ⊢ (λv.body) w) ({(λv.body) w} ⊢ ∃v. body)
                     : A ∪ ({(λv.body) w} \ {(λv.body) w}) ⊢ ∃v. body
                     : A ⊢ ∃v. body
    *)
    fun do_EXISTS pred_tm var_tm witness_tm v_ty th =
      let val Ab_v = emit_tyop "fun" [v_ty, bool_tyid]
          val exists_inst = c_inst (c_inst_type (candle_load_pth "candle$EXISTS")
                              [(tyvar_A, v_ty)])
                              [(emit_var "P" Ab_v, pred_tm),
                               (emit_var "x" v_ty, witness_tm)]
                            (* exists_inst: {(λv.body) witness} ⊢ ∃v. body *)
          val witness_hyp = c_eq_mp (c_sym (do_beta_reduce pred_tm witness_tm)) th
                            (* witness_hyp: A ⊢ (λv. body) witness *)
      in c_prove_hyp witness_hyp exists_inst end
         (* result: A ⊢ ∃v. body *)

    (* do_AP_TERM
       -----------
       Signature: th: A ⊢ x = y
                  f: term ID for function f
                  Result: A ⊢ f x = f y

       Derivation:
         c_refl f : ⊢ f = f
         c_mk_comb (⊢ f = f) (A ⊢ x = y) : A ⊢ f x = f y
    *)
    fun do_AP_TERM f th = c_mk_comb (c_refl f) th

    (* exist_to_witness
       ------------------
       Signature: exists_th: ⊢ ∃v. body  (no hypotheses)
                  exists_concl_id: term ID for ∃v. body = ?(λv. body)
                  Result: (th, pred_id, pred_body_id, Ab, v_ty) where
                          th: ⊢ (λv. body) (@ (λv. body))
                          pred_id: term ID for λv. body
                          pred_body_id: term ID for body
                          Ab: type ID for v_ty -> bool
                          v_ty: type ID for v

       Pro-formas used:
         candle$SELECT_AX_SPEC = ⊢ !x. P x ==> P (@ P)  (P : 'a->bool free)
         candle$CHOOSE = ⊢ (?P) ==> (!x. P x ==> Q) ==> Q

       Let P = λv. body, w = @ P (the witness)

       Derivation:
         sel_inst = INST (INST_TYPE candle$SELECT_AX_SPEC ['a↦v_ty]) [P↦pred_id]
                  : ⊢ !x. (λv.body) x ==> (λv.body) (@ (λv.body))
                  : ⊢ ∀x. P x ==> P w

         choose_inst = INST (INST_TYPE candle$CHOOSE ['a↦v_ty])
                            [P↦pred_id, Q↦(P w)]
                     : ⊢ (?P) ==> (!x. P x ==> P w) ==> P w

         forall_inner = !x. P x ==> P w  (term)
         imp_forall_pw = (!x. P x ==> P w) ==> P w  (term)

         mp1 = do_MP choose_inst (?P) imp_forall_pw exists_th
             : ⊢ (!x. P x ==> P w) ==> P w

         result = do_MP mp1 forall_inner (P w) sel_inst
                : ⊢ P w
                : ⊢ (λv. body) (@ (λv. body))
    *)
    fun exist_to_witness exists_th exists_concl_id = let
      val (_, pred_id) = pft_dest_comb exists_concl_id
                         (* pred_id: λv. body *)
      val (bv_id, pred_body_id) = pft_dest_abs pred_id
                                  (* bv_id: binder v, pred_body_id: body *)
      val v_ty = pft_type_of bv_id
      val Ab = emit_tyop "fun" [v_ty, bool_tyid]
                (* Ab: v_ty -> bool *)
      val select_c = emit_const "@" (emit_tyop "fun" [Ab, v_ty])
      val witness = emit_comb select_c pred_id
                    (* witness: @ (λv. body) *)
      val pred_witness = emit_comb pred_id witness
                         (* pred_witness: (λv. body) (@ (λv. body)) = P w *)
      val var_P_Ab = emit_var "P" Ab
      val sel_inst = c_inst (c_inst_type (candle_load_pth "candle$SELECT_AX_SPEC")
                       [(tyvar_A, v_ty)])
                       [(var_P_Ab, pred_id)]
                     (* sel_inst: ⊢ !x. P x ==> P w *)
      val choose_inst = c_inst (c_inst_type (candle_load_pth "candle$CHOOSE")
                          [(tyvar_A, v_ty)])
                          [(var_P_Ab, pred_id), (pvar_Q, pred_witness)]
                        (* choose_inst: ⊢ (?P) ==> (!x. P x ==> P w) ==> P w *)
      val bv_x_v = emit_binder "x" v_ty
      val forall_inner = emit_comb (emit_const "!" (emit_tyop "fun" [Ab, bool_tyid]))
        (emit_abs bv_x_v (emit_comb (emit_comb (imp_const) (emit_comb pred_id bv_x_v)) pred_witness))
                         (* forall_inner: !x. P x ==> P w *)
      val imp_forall_pw = emit_comb (emit_comb (imp_const) forall_inner) pred_witness
                          (* imp_forall_pw: (!x. P x ==> P w) ==> P w *)
      val mp1 = do_MP choose_inst exists_concl_id imp_forall_pw exists_th
                (* mp1: ⊢ (!x. P x ==> P w) ==> P w *)
      val result = do_MP mp1 forall_inner pred_witness sel_inst
                   (* result: ⊢ P w = (λv. body) (@ (λv. body)) *)
    in (result, pred_id, pred_body_id, Ab, v_ty) end

    (* Ensure candle$TYPE_DEFINITION_THM_FREE is available.
       Derived once from bool$TYPE_DEFINITION_THM by stripping both outer ∀s
       via do_DOUBLE_SPEC, then renaming the resulting “pft%”-named free
       variables (from the original binders) to clean names ("P", "rep")
       via INST, so that downstream INST in Def_tyop_prf can target them
       by name.  SAVEd as candle$TYPE_DEFINITION_THM_FREE.
       During boolTheory the derivation happens here and the id is used directly;
       later theories LOAD it via candle_load_pth.
       Returns the theorem id. *)
    fun ensure_tydef_thm_free () =
      if !tydef_thm_free_saved
      then candle_load_pth "candle$TYPE_DEFINITION_THM_FREE"
      else let
        val tydef_th =
          if thyname = "bool"
          then emit_thm (Redblackmap.find(named_thm_map, "TYPE_DEFINITION_THM"))
          else candle_load_pth "bool$TYPE_DEFINITION_THM"
        (* Get the conclusion PFT term ID.
           For boolTheory, the terms are freshly emitted, so pft_dest_comb/abs
           are available. For other theories, this would fail — but other
           theories should always hit the !tydef_thm_free_saved branch above
           (the SAVE was done during boolTheory's prior emit_theory call,
           and the module-level flag persists). *)
        val tydef_concl_id =
          if thyname = "bool"
          then tm (heap_concl (Redblackmap.find(named_thm_map,
                                                "TYPE_DEFINITION_THM")))
          else raise Fail "ensure_tydef_thm_free: not bool, not saved"
        (* Destructure ∀P. ∀rep. body:
           ! (λP. !(λrep. body)) *)
        val (_, outer_pred) = pft_dest_comb tydef_concl_id
        val (P_bv, inner_forall_id) = pft_dest_abs outer_pred
        val P_ty = pft_type_of P_bv
        val (_, inner_pred) = pft_dest_comb inner_forall_id
        val (rep_bv, body_eq_id) = pft_dest_abs inner_pred
        val rep_ty_gen = pft_type_of rep_bv
        (* Build clean-named free-variable terms that downstream INST can
           target by name.  P_bv/rep_bv have "pft%"-suffixed names that
           won't match the emit_var "P" / emit_var "rep" redexes used
           later in Def_tyop_prf. *)
        val P_free = emit_var "P" (emit_tyop "fun" [mk_tyvar_cached "'a", bool_tyid])
        val rep_free = emit_var "rep" (emit_tyop "fun" [mk_tyvar_cached "'b",
                                                        mk_tyvar_cached "'a"])
        (* Strip both ∀s via do_DOUBLE_SPEC, passing the actual binder
           variable IDs (P_bv, rep_bv) from pft_dest_abs so that
           pft_subst_tm correctly finds them in body_eq_id.  The result
           has P_bv/rep_bv free, which have "pft%" names; we then INST
           them to the clean-named P_free/rep_free. *)
        val tydef_free_raw = do_DOUBLE_SPEC tydef_th
                               P_bv P_ty rep_bv rep_ty_gen body_eq_id
        val tydef_free = c_inst tydef_free_raw
                           [(P_bv, P_free), (rep_bv, rep_free)]
        (* SAVE for later LOAD by other theories *)
        val () = PFTWriter.save out "candle$TYPE_DEFINITION_THM_FREE" tydef_free
        val () = tydef_thm_free_saved := true
      in tydef_free end

  in
    case proof of
    (* ================================================================= *)
    (* Direct mappings (1:1 to Candle core rules)                        *)
    (* These proof rules map directly to Candle primitive inference rules*)
    (* ================================================================= *)

    (* REFL_prf: t → ⊢ t = t *)
      REFL_prf a => r_refl (tm a)

    (* TRANS_prf: A ⊢ l = m, B ⊢ m = r → A ∪ B ⊢ l = r *)
    | TRANS_prf (a, b) => r_trans (th a) (th b)

    (* MK_COMB_prf: A ⊢ f = g, B ⊢ x = y → A ∪ B ⊢ f x = g y *)
    | MK_COMB_prf (a, b) => r_mk_comb (th a) (th b)

    (* ABS_prf: v, A ⊢ l = r → A ⊢ (λv. l) = (λv. r) (v not free in A) *)
    | ABS_prf (a, b) => r_abs (tm a) (th b)

    (* EQ_MP_prf: A ⊢ p = q, B ⊢ p → A ∪ B ⊢ q *)
    | EQ_MP_prf (a, b) => r_eq_mp (th a) (th b)

    (* ASSUME_prf: p → {p} ⊢ p *)
    | ASSUME_prf a => r_assume (tm a)

    (* SYM_prf: A ⊢ l = r → A ⊢ r = l *)
    | SYM_prf a => r_sym (th a)

    (* INST_prf: [(v1,t1),...], A ⊢ p → A[t/v] ⊢ p[t/v] *)
    | INST_prf (a, b) => let
        val pairs = list heap (tuple2 heap (tm, tm)) a
      in r_inst (th b) pairs end

    (* INST_TYPE_prf: [(α1,ty1),...], A ⊢ p → A[ty/α] ⊢ p[ty/α] *)
    | INST_TYPE_prf (a, b) => let
        val pairs = list heap (tuple2 heap (ty, ty)) a
      in r_inst_type (th b) pairs end

    (* deductAntisym_prf: A ⊢ p, B ⊢ q → (A \ {q}) ∪ (B \ {p}) ⊢ p = q *)
    | deductAntisym_prf (a, b) => r_deduct (th a) (th b)

    (* Axiom_prf and Disk_prf are handled in emit_thm before dispatch *)

    (* ================================================================= *)
    (* Simple compositions                                               *)
    (* ================================================================= *)

    (* AP_TERM_prf: f, A ⊢ x = y → A ⊢ f x = f y
       Derivation: MK_COMB (REFL f) (A ⊢ x = y) *)
    | AP_TERM_prf (a, b) => r_mk_comb (c_refl (tm a)) (th b)

    (* AP_THM_prf: A ⊢ f = g, x → A ⊢ f x = g x
       Derivation: MK_COMB (A ⊢ f = g) (REFL x) *)
    | AP_THM_prf (a, b) => r_mk_comb (th a) (c_refl (tm b))

    (* ================================================================= *)
    (* Pro-forma based: conjunction                                      *)
    (* ================================================================= *)

    (* CONJ_prf
       ---------
       HOL4 rule: A ⊢ p, B ⊢ q  →  A ∪ B ⊢ p ∧ q

       Pro-forma: candle$CONJ = {p, q} ⊢ p ∧ q

       Derivation:
         ci = INST candle$CONJ [p↦a, q↦b]
            : {a, b} ⊢ a ∧ b
         c_prove_hyp a_th ci
            : A ∪ {b} ⊢ a ∧ b
         r_prove_hyp b_th (...)
            : A ∪ B ⊢ a ∧ b  ✓
    *)
    | CONJ_prf (a, b) => let
        val a_th = th a val b_th = th b
        val a_tm = tm (heap_concl a) val b_tm = tm (heap_concl b)
        val ci = c_inst (candle_load_pth "candle$CONJ")
                   [(pvar_p, a_tm), (pvar_q, b_tm)]
      in r_prove_hyp b_th (c_prove_hyp a_th ci) end

    (* CONJUNCT1_prf
       --------------
       HOL4 rule: A ⊢ p ∧ q  →  A ⊢ p

       Pro-forma: candle$CONJUNCT1 = {p ∧ q} ⊢ p

       Derivation:
         pth = INST candle$CONJUNCT1 [p↦l, q↦r]
             : {l ∧ r} ⊢ l
         r_prove_hyp a_th pth
             : A ⊢ l  ✓
    *)
    | CONJUNCT1_prf a => let
        val a_th = th a
        val concl_id = tm (heap_concl a)
        val (and_l_id, r_tm) = pft_dest_comb concl_id
        val (_, l_tm) = pft_dest_comb and_l_id
      in r_prove_hyp a_th (c_inst (candle_load_pth "candle$CONJUNCT1")
                        [(pvar_p, l_tm), (pvar_q, r_tm)]) end

    (* CONJUNCT2_prf
       --------------
       HOL4 rule: A ⊢ p ∧ q  →  A ⊢ q

       Pro-forma: candle$CONJUNCT2 = {p ∧ q} ⊢ q

       Derivation:
         pth = INST candle$CONJUNCT2 [p↦l, q↦r]
             : {l ∧ r} ⊢ r
         r_prove_hyp a_th pth
             : A ⊢ r  ✓
    *)
    | CONJUNCT2_prf a => let
        val a_th = th a
        val concl_id = tm (heap_concl a)
        val (and_l_id, r_tm) = pft_dest_comb concl_id
        val (_, l_tm) = pft_dest_comb and_l_id
      in r_prove_hyp a_th (c_inst (candle_load_pth "candle$CONJUNCT2")
                        [(pvar_p, l_tm), (pvar_q, r_tm)]) end

    (* MP_prf
       -------
       HOL4 rule: A ⊢ p ==> q, B ⊢ p  →  A ∪ B ⊢ q
       Also handles: A ⊢ ~p, B ⊢ p  →  A ∪ B ⊢ F  (via dest_neg treating ~p as p ==> F)

       Pro-formas:
         candle$MP = {p} ⊢ (p ==> q) = q
         candle$NOT_ELIM = {~p} ⊢ p ==> F

       Derivation (normal case: a_th: A ⊢ p ==> q, b_th: B ⊢ p):
         rth = INST candle$MP [p↦p, q↦q]
             : {p} ⊢ (p ==> q) = q

         c_prove_hyp b_th rth
             : PROVE_HYP (B ⊢ p) ({p} ⊢ (p ==> q) = q)
             : B ∪ ({p} \ {p}) ⊢ (p ==> q) = q
             : B ⊢ (p ==> q) = q

         r_eq_mp (c_prove_hyp b_th rth) a_th
             : EQ_MP (B ⊢ (p ==> q) = q) (A ⊢ p ==> q)
             : A ∪ B ⊢ q  ✓

       Derivation (negation case: a_th: A ⊢ ~p, b_th: B ⊢ p):
         ne = INST candle$NOT_ELIM [p↦p]
            : {~p} ⊢ p ==> F

         a_th' = c_prove_hyp a_th ne
               : PROVE_HYP (A ⊢ ~p) ({~p} ⊢ p ==> F)
               : A ⊢ p ==> F

         Then proceed as normal case with q = F.
    *)
    | MP_prf (a, b) => let
        val a_th = th a val b_th = th b
                   (* a_th: A ⊢ p ==> q (or A ⊢ ~p)
                      b_th: B ⊢ p *)
        val concl_a_id = tm (heap_concl a)
        val (imp_p_id, rhs_tm) = pft_dest_comb concl_a_id
        (* HOL4's MP treats ~p as p ==> F via dest_imp/dest_neg.
           When the conclusion is ~p rather than p ==> q, unfold
           the negation using NOT_ELIM before the normal MP step. *)
        val (a_th, p_tm, q_tm) =
          case total pft_dest_comb imp_p_id of
            SOME (_, p) => (a_th, p, rhs_tm)
                           (* Normal case: concl is (==>) p q, so p_tm = p, q_tm = q *)
          | NONE => let
              (* Negation case: concl is ~ rhs_tm, so p = rhs_tm, q = F *)
              val ne = c_inst (candle_load_pth "candle$NOT_ELIM")
                         [(pvar_p, rhs_tm)]
                       (* ne: {~rhs_tm} ⊢ rhs_tm ==> F *)
            in (c_prove_hyp a_th ne, rhs_tm, const_F_tm) end
                           (* a_th': A ⊢ rhs_tm ==> F *)
        val rth = c_inst (candle_load_pth "candle$MP")
                    [(pvar_p, p_tm), (pvar_q, q_tm)]
                  (* rth: {p} ⊢ (p ==> q) = q *)
      in r_eq_mp (c_prove_hyp b_th rth) a_th end
         (* result: A ∪ B ⊢ q *)

    (* EQ_IMP_RULE1_prf
       ------------------
       HOL4 rule: A ⊢ p = q  →  A ⊢ p ==> q

       Pro-forma: candle$EQ_IMP_RULE1 = {p = q} ⊢ p ==> q

       Derivation:
         pth = INST candle$EQ_IMP_RULE1 [p↦p, q↦q]
             : {p = q} ⊢ p ==> q
         r_prove_hyp a_th pth
             : PROVE_HYP (A ⊢ p = q) ({p = q} ⊢ p ==> q)
             : A ⊢ p ==> q  ✓
    *)
    | EQ_IMP_RULE1_prf a => let
        val a_th = th a
        val concl_id = tm (heap_concl a)
        val (eq_l_id, q_tm) = pft_dest_comb concl_id
        val (_, p_tm) = pft_dest_comb eq_l_id
      in r_prove_hyp a_th (c_inst (candle_load_pth "candle$EQ_IMP_RULE1")
                        [(pvar_p, p_tm), (pvar_q, q_tm)]) end

    (* EQ_IMP_RULE2_prf
       ------------------
       HOL4 rule: A ⊢ p = q  →  A ⊢ q ==> p

       Pro-forma: candle$EQ_IMP_RULE2 = {p = q} ⊢ q ==> p

       Derivation:
         pth = INST candle$EQ_IMP_RULE2 [p↦p, q↦q]
             : {p = q} ⊢ q ==> p
         r_prove_hyp a_th pth
             : A ⊢ q ==> p  ✓
    *)
    | EQ_IMP_RULE2_prf a => let
        val a_th = th a
        val concl_id = tm (heap_concl a)
        val (eq_l_id, q_tm) = pft_dest_comb concl_id
        val (_, p_tm) = pft_dest_comb eq_l_id
      in r_prove_hyp a_th (c_inst (candle_load_pth "candle$EQ_IMP_RULE2")
                        [(pvar_p, p_tm), (pvar_q, q_tm)]) end

    (* NOT_ELIM_prf
       -------------
       HOL4 rule: A ⊢ ~p  →  A ⊢ p ==> F

       Pro-forma: candle$NOT_ELIM = {~p} ⊢ p ==> F

       Derivation:
         pth = INST candle$NOT_ELIM [p↦p]
             : {~p} ⊢ p ==> F
         r_prove_hyp a_th pth
             : A ⊢ p ==> F  ✓
    *)
    | NOT_ELIM_prf a => let
        val a_th = th a
        val (_, p_tm) = pft_dest_comb (tm (heap_concl a))
      in r_prove_hyp a_th (c_inst (candle_load_pth "candle$NOT_ELIM")
                        [(pvar_p, p_tm)]) end

    (* NOT_INTRO_prf
       --------------
       HOL4 rule: A ⊢ p ==> F  →  A ⊢ ~p

       Pro-forma: candle$NOT_INTRO = {p ==> F} ⊢ ~p

       Derivation:
         pth = INST candle$NOT_INTRO [p↦p]
             : {p ==> F} ⊢ ~p
         r_prove_hyp a_th pth
             : A ⊢ ~p  ✓
    *)
    | NOT_INTRO_prf a => let
        val a_th = th a
        val concl_id = tm (heap_concl a)
        val (imp_p_id, _) = pft_dest_comb concl_id
        val (_, p_tm) = pft_dest_comb imp_p_id
      in r_prove_hyp a_th (c_inst (candle_load_pth "candle$NOT_INTRO")
                        [(pvar_p, p_tm)]) end

    (* DISJ1_prf
       ----------
       HOL4 rule: A ⊢ p, q  →  A ⊢ p ∨ q

       Pro-forma: candle$DISJ1 = {p} ⊢ p ∨ q

       Derivation:
         pth = INST candle$DISJ1 [p↦p, q↦q]
             : {p} ⊢ p ∨ q
         r_prove_hyp a_th pth
             : A ⊢ p ∨ q  ✓
    *)
    | DISJ1_prf (a, b) => let
        val a_th = th a val q_tm = tm b
        val p_tm = tm (heap_concl a)
        val pth = c_inst (candle_load_pth "candle$DISJ1")
                    [(pvar_p, p_tm), (pvar_q, q_tm)]
      in r_prove_hyp a_th pth end

    (* DISJ2_prf
       ----------
       HOL4 rule: p, A ⊢ q  →  A ⊢ p ∨ q

       Pro-forma: candle$DISJ2 = {q} ⊢ p ∨ q

       Derivation:
         pth = INST candle$DISJ2 [p↦p, q↦q]
             : {q} ⊢ p ∨ q
         r_prove_hyp b_th pth
             : A ⊢ p ∨ q  ✓
    *)
    | DISJ2_prf (a, b) => let
        val p_tm = tm a val b_th = th b
        val q_tm = tm (heap_concl b)
        val pth = c_inst (candle_load_pth "candle$DISJ2")
                    [(pvar_p, p_tm), (pvar_q, q_tm)]
      in r_prove_hyp b_th pth end

    (* Mk_comb_prf
       ------------
       HOL4 rule: A ⊢ t = (f x), B ⊢ f = g, C ⊢ x = y  →  A ∪ B ∪ C ⊢ t = (g y)

       Derivation:
         th a: A ⊢ t = (f x)
         th b: B ⊢ f = g
         th c: C ⊢ x = y
         c_mk_comb (th b) (th c): B ∪ C ⊢ f x = g y
         r_trans (th a) (...): A ∪ B ∪ C ⊢ t = g y  ✓
    *)
    | Mk_comb_prf (a, b, c) => r_trans (th a) (c_mk_comb (th b) (th c))

    (* Mk_abs_prf
       -----------
       HOL4 rule: A ⊢ t = (λv. l), B ⊢ l = r  →  A ∪ B ⊢ t = (λv. r)
       Side condition: v not free in A or B

       Note: For PFTRename compliance, we must use a fresh binder for the new ABS.

       Derivation:
         a_th: A ⊢ t = (λv. l)
         c_th: B ⊢ l = r
         v_tm: variable from heap
         bv: fresh binder
         c_th' = INST c_th [(v_tm, bv)]: B ⊢ l[bv/v] = r[bv/v]
         c_abs bv c_th': B ⊢ (λbv. l[bv/v]) = (λbv. r[bv/v])
         r_trans a_th (...): A ∪ B ⊢ t = (λbv. r[bv/v])  ✓
    *)
    | Mk_abs_prf (a, b, c) => let
        (* ABS requires a unique binder variable to satisfy PFTRename.
           We create a fresh binder and INST c_th to replace the free
           variable with the fresh binder. *)
        val a_th = th a val c_th = th c
        val v_tm = tm b  (* free variable from heap *)
        val v_ty = pft_type_of v_tm
        val bv = emit_binder "v" v_ty
        val c_th' = c_inst c_th [(v_tm, bv)]
      in r_trans a_th (c_abs bv c_th') end

    (* Beta_prf
       ---------
       HOL4 rule: A ⊢ t = ((λv. body) x)  →  A ⊢ t = body[x/v]

       Derivation:
         a_th: A ⊢ t = (λv. body) x

         actual_bv = binder of the lambda
         beta_th = BETA ((λv. body) actual_bv)
                 : ⊢ (λv. body) actual_bv = body

         if actual_bv = arg_tm:
           beta_inst = beta_th: ⊢ (λv. body) x = body[x/v]
         else:
           beta_inst = INST beta_th [(actual_bv, arg_tm)]
                     : ⊢ (λv. body) x = body[x/v]

         r_trans a_th beta_inst: A ⊢ t = body[x/v]  ✓
    *)
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

    (* BETA_CONV_prf
       --------------
       HOL4 rule: (λv. body) x  →  ⊢ (λv. body) x = body[x/v]

       Derivation:
         actual_bv = binder of the lambda
         BETA ((λv. body) actual_bv): ⊢ (λv. body) actual_bv = body

         if actual_bv = arg_tm:
           return the BETA result directly
         else:
           INST [(actual_bv, arg_tm)]: ⊢ (λv. body) x = body[x/v]  ✓
    *)
    | BETA_CONV_prf a => let
        val app_id = tm a
        val (lam_tm, arg_tm) = pft_dest_comb app_id
        val (actual_bv, _) = pft_dest_abs lam_tm
        val app_var = emit_comb lam_tm actual_bv
      in if actual_bv = arg_tm then r_beta app_var
         else r_inst (c_beta app_var) [(actual_bv, arg_tm)] end

    (* ALPHA_prf
       ----------
       HOL4 rule: t1, t2  →  ⊢ t1 = t2  (where t1 and t2 are alpha-equivalent)

       In Candle, alpha-equivalent terms are equal, so REFL suffices.
    *)
    | ALPHA_prf (t1, _) =>
        c_refl (tm t1)

    (* DISCH_prf
       ----------
       HOL4 rule: p, A ⊢ q  →  A \ {p} ⊢ p ==> q

       Just calls do_DISCH helper function.
    *)
    | DISCH_prf (a, b) => let
        val p_tm = tm a val b_th = th b val q_tm = tm (heap_concl b)
      in do_DISCH p_tm q_tm b_th end

    (* GEN_prf
       --------
       HOL4 rule: A ⊢ s  →  A ⊢ ∀v. s
       Side condition: v not free in A

       Just calls do_GEN helper function.
    *)
    | GEN_prf (a, b) => let
        val v_tm = tm a val b_th = th b
        val s_tm = tm (heap_concl b)
        val v_ty = pft_type_of v_tm
      in do_GEN v_tm v_ty s_tm b_th end

    (* GENL_prf
       ---------
       HOL4 rule: A ⊢ s  →  A ⊢ ∀v1...∀vn. s
       Side condition: v1,...,vn not free in A

       Derivation: Fold do_GEN from innermost to outermost.
       For each variable vi, we construct the appropriate conclusion term
       (the forall at that level) and call do_GEN.
    *)
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

    (* SPEC_prf
       ---------
       HOL4 rule: A ⊢ ∀v. s  →  A ⊢ s[t/v]

       Same as Specialize_prf.
    *)
    | SPEC_prf (a, b) =>
        emit_thm_candle result_id concl_ptr (Specialize_prf (a, b))

    (* Specialize_prf
       ---------------
       HOL4 rule: A ⊢ ∀v. s  →  A ⊢ s[t/v]

       Just calls do_SPEC helper function.
    *)
    | Specialize_prf (a, b) => let
        val t_tm = tm a val b_th = th b
        val forall_P_tm = tm (heap_concl b)
        val (_, pred_tm) = pft_dest_comb forall_P_tm
        val v_ty = pft_type_of t_tm
      in do_SPEC t_tm pred_tm forall_P_tm v_ty b_th end

    (* DISJ_CASES_prf
       ----------------
       HOL4 rule: A ⊢ p ∨ q, B ⊢ r, C ⊢ r
                  → A ∪ (B \ {p}) ∪ (C \ {q}) ⊢ r
       where B has hypothesis p and C has hypothesis q.

       Pro-forma: candle$DISJ_CASES = {p ∨ q, p ==> r, q ==> r} ⊢ r

       Derivation:
         a_th: A ⊢ p ∨ q
         b_th: B ⊢ r  (with p ∈ B)
         c_th: C ⊢ r  (with q ∈ C)

         pth = INST candle$DISJ_CASES [p↦p, q↦q, r↦r]
             : {p ∨ q, p ==> r, q ==> r} ⊢ r

         c_deduct a_th pth
             : DEDUCT_ANTISYM (A ⊢ p∨q) ({p∨q, p==>r, q==>r} ⊢ r)
             : (A \ {r}) ∪ ({p∨q, p==>r, q==>r} \ {p∨q}) ⊢ (p∨q) = r
             : A ∪ {p==>r, q==>r} ⊢ (p∨q) = r
               (since r ∉ A typically, and p∨q is the conclusion being discharged)

         th3 = c_eq_mp (c_deduct a_th pth) a_th
             : EQ_MP (A ∪ {p==>r, q==>r} ⊢ (p∨q) = r) (A ⊢ p∨q)
             : A ∪ {p==>r, q==>r} ⊢ r

         do_DISCH p_tm r_tm b_th
             : B \ {p} ⊢ p ==> r

         th4 = c_prove_hyp (do_DISCH p_tm r_tm b_th) th3
             : PROVE_HYP (B\{p} ⊢ p==>r) (A ∪ {p==>r, q==>r} ⊢ r)
             : (B\{p}) ∪ ((A ∪ {p==>r, q==>r}) \ {p==>r}) ⊢ r
             : (B\{p}) ∪ A ∪ {q==>r} ⊢ r

         do_DISCH q_tm r_tm c_th
             : C \ {q} ⊢ q ==> r

         r_prove_hyp (do_DISCH q_tm r_tm c_th) th4
             : PROVE_HYP (C\{q} ⊢ q==>r) ((B\{p}) ∪ A ∪ {q==>r} ⊢ r)
             : (C\{q}) ∪ (((B\{p}) ∪ A ∪ {q==>r}) \ {q==>r}) ⊢ r
             : (C\{q}) ∪ (B\{p}) ∪ A ⊢ r
             : A ∪ (B\{p}) ∪ (C\{q}) ⊢ r  ✓
    *)
    | DISJ_CASES_prf (a, b, c) => let
        val a_th = th a val b_th = th b val c_th = th c
                   (* a_th: A ⊢ p ∨ q
                      b_th: B ⊢ r  (with p ∈ B)
                      c_th: C ⊢ r  (with q ∈ C) *)
        val concl_a_id = tm (heap_concl a)
        val (or_p_id, q_tm) = pft_dest_comb concl_a_id
        val (_, p_tm) = pft_dest_comb or_p_id
        val r_tm = tm (heap_concl b)
        val pth = c_inst (candle_load_pth "candle$DISJ_CASES")
                    [(pvar_p, p_tm), (pvar_q, q_tm), (pvar_r, r_tm)]
                  (* pth: {p ∨ q, p ==> r, q ==> r} ⊢ r *)
        val th3 = c_eq_mp (c_deduct a_th pth) a_th
                  (* th3: A ∪ {p==>r, q==>r} ⊢ r *)
        val th4 = c_prove_hyp (do_DISCH p_tm r_tm b_th) th3
                  (* th4: A ∪ (B\{p}) ∪ {q==>r} ⊢ r *)
      in r_prove_hyp (do_DISCH q_tm r_tm c_th) th4 end
         (* result: A ∪ (B\{p}) ∪ (C\{q}) ⊢ r *)

    (* CCONTR_prf
       -----------
       HOL4 rule: p, A ⊢ F  →  A \ {~p} ⊢ p
       (Classical contradiction: if assuming ~p leads to F, then p holds)

       Pro-forma: candle$CCONTR = ⊢ (~p ==> F) ==> p

       Derivation:
         b_th: A ⊢ F  (where ~p ∈ A)
         disch_th = do_DISCH (~p) F b_th
                  : A \ {~p} ⊢ ~p ==> F
         ccontr_inst = INST candle$CCONTR [p↦p]
                     : ⊢ (~p ==> F) ==> p
         do_MP ccontr_inst (~p ==> F) p disch_th
                     : A \ {~p} ⊢ p  ✓
    *)
    | CCONTR_prf (a, b) => let
        val p_tm = tm a val b_th = th b
        val neg_tm = emit_const "~" (emit_tyop "fun" [bool_tyid, bool_tyid])
        val neg_p = emit_comb neg_tm p_tm
        val disch_th = do_DISCH neg_p const_F_tm b_th
        val ccontr_inst = c_inst (candle_load_pth "candle$CCONTR")
                            [(pvar_p, p_tm)]
        val neg_p_imp_F = emit_comb (emit_comb imp_const neg_p) const_F_tm
      in do_MP ccontr_inst neg_p_imp_F p_tm disch_th end

    (* EXISTS_prf
       -----------
       HOL4 rule: ∃v. body, witness, A ⊢ body[witness/v]  →  A ⊢ ∃v. body

       Just calls do_EXISTS helper function.
    *)
    | EXISTS_prf (a, b, c) => let
        val c_th = th c
        val witness_tm = tm b
        val exists_id = tm a
        val (_, pred_tm) = pft_dest_comb exists_id
        val (var_tm, _) = pft_dest_abs pred_tm
        val v_ty = pft_type_of var_tm
      in do_EXISTS pred_tm var_tm witness_tm v_ty c_th end

    (* CHOOSE_prf
       -----------
       HOL4 rule: v, A ⊢ ∃x. P, B ⊢ q
                  → A ∪ (B \ {P[v/x]}) ⊢ q
       Side condition: v not free in ∃x. P, q, or the remaining hypotheses of B

       Here:
         v_tm = the chosen variable v
         b_th: A ⊢ ∃x. P  (i.e., A ⊢ ?pred_tm where pred_tm = λx. P)
         c_th: B ⊢ q  (where P[v/x] ∈ B)

       The hypothesis to discharge from B is P[v/x].

       Pro-forma: candle$CHOOSE = ⊢ (?P) ==> (!x. P x ==> Q) ==> Q

       Strategy:
         1. From c_th: B ⊢ q with P[v/x] ∈ B, we need to derive
            something of the form B \ {P[v/x]} ⊢ (P v) ==> q
         2. Then GEN over v to get !v. P v ==> q
         3. Then use CHOOSE pro-forma with b_th to get q

       Let cmb = (λx. P) v (an application, NOT the same as P[v/x]).

       Derivation:
         c_assume cmb
             : {cmb} ⊢ cmb
             : {(λx. P) v} ⊢ (λx. P) v

         do_beta_reduce pred_tm v_tm
             : ⊢ (λx. P) v = P[v/x]

         c_eq_mp (do_beta_reduce pred_tm v_tm) (c_assume cmb)
             : EQ_MP (⊢ cmb = P[v/x]) ({cmb} ⊢ cmb)
             : {cmb} ⊢ P[v/x]
             : {(λx. P) v} ⊢ P[v/x]

         c_with_cmb = c_prove_hyp (...) c_th
             : PROVE_HYP ({cmb} ⊢ P[v/x]) (B ⊢ q)
             : {cmb} ∪ (B \ {P[v/x]}) ⊢ q
             : {(λx. P) v} ∪ (B \ {P[v/x]}) ⊢ q

         th_disch = do_DISCH cmb q_tm c_with_cmb
             : ({cmb} ∪ (B \ {P[v/x]})) \ {cmb} ⊢ cmb ==> q
             : B \ {P[v/x]} ⊢ (λx. P) v ==> q

         th_disch_bv = c_inst th_disch [(v_tm, bv)]
             : (B \ {P[v/x]})[bv/v] ⊢ ((λx. P) v ==> q)[bv/v]
             : B \ {P[v/x]} ⊢ (λx. P) bv ==> q
             (since v not free in B \ {P[v/x]} or q by side condition)

         eqt_pth = INST candle$EQT_INTRO [t ↦ ((λx.P) bv ==> q)]
             : ⊢ ((λx.P) bv ==> q) = (((λx.P) bv ==> q) = T)

         c_eq_mp eqt_pth th_disch_bv
             : B \ {P[v/x]} ⊢ ((λx.P) bv ==> q) = T

         abs_eq = c_abs bv (...)
             : B \ {P[v/x]} ⊢ (λbv. (λx.P) bv ==> q) = (λbv. T)
             (bv not free in B \ {P[v/x]} by side condition + fresh binder)

         gen_inst = INST (INST_TYPE candle$GEN ['a↦v_ty]) [P ↦ (λbv. cmb_bv ==> q)]
             : ⊢ ((λbv. cmb_bv ==> q) = (λx. T)) = !(λbv. cmb_bv ==> q)

         gen_v = c_eq_mp gen_inst abs_eq
             : B \ {P[v/x]} ⊢ !bv. (λx.P) bv ==> q

         choose_inst = INST (INST_TYPE candle$CHOOSE ['a↦v_ty])
                            [P ↦ pred_tm, Q ↦ q]
             : ⊢ (?pred_tm) ==> (!bv. pred_tm bv ==> q) ==> q
             : ⊢ (∃x. P) ==> (!bv. (λx.P) bv ==> q) ==> q

         mp_choose1 = do_MP choose_inst exists_P_tm imp_forall_q b_th
             : A ⊢ (!bv. (λx.P) bv ==> q) ==> q

         do_MP mp_choose1 forall_v_imp q_tm gen_v
             : A ∪ (B \ {P[v/x]}) ⊢ q  ✓
    *)
    | CHOOSE_prf (a, b, c) => let
        val v_tm = tm a val b_th = th b val c_th = th c
                   (* v_tm: the chosen variable
                      b_th: A ⊢ ∃x. P
                      c_th: B ⊢ q  (with P[v/x] ∈ B) *)
        val q_tm = tm (heap_concl c)
        val exists_P_tm = tm (heap_concl b)
                          (* exists_P_tm: ?pred_tm = ∃x. P *)
        val (_, pred_tm) = pft_dest_comb exists_P_tm
                           (* pred_tm: λx. P *)
        val (bv_tm, _) = pft_dest_abs pred_tm
        val v_ty = pft_type_of bv_tm
        (* Create fresh binder for the forall term to satisfy PFTRename. *)
        val bv = emit_binder "v" v_ty
        val cmb = emit_comb pred_tm v_tm
                  (* cmb: (λx. P) v *)
        val cmb_bv = emit_comb pred_tm bv
                     (* cmb_bv: (λx. P) bv *)
        val c_with_cmb = c_prove_hyp
                            (c_eq_mp (do_beta_reduce pred_tm v_tm) (c_assume cmb)) c_th
                         (* c_with_cmb: {cmb} ∪ (B \ {P[v/x]}) ⊢ q *)
        val imp_cmb_q = emit_comb (emit_comb imp_const cmb) q_tm
        val imp_cmb_q_bv = emit_comb (emit_comb imp_const cmb_bv) q_tm
        val th_disch = do_DISCH cmb q_tm c_with_cmb
                       (* th_disch: B \ {P[v/x]} ⊢ cmb ==> q *)
        val th_disch_bv = c_inst th_disch [(v_tm, bv)]
                          (* th_disch_bv: B \ {P[v/x]} ⊢ cmb_bv ==> q *)
        val eqt_pth = c_inst (candle_load_pth "candle$EQT_INTRO")
                         [(pvar_t, imp_cmb_q_bv)]
        val abs_eq = c_abs bv (c_eq_mp eqt_pth th_disch_bv)
                     (* abs_eq: B \ {P[v/x]} ⊢ (λbv. cmb_bv ==> q) = (λbv. T) *)
        val Ab_v = emit_tyop "fun" [v_ty, bool_tyid]
        val gen_inst = c_inst (c_inst_type (candle_load_pth "candle$GEN")
                         [(tyvar_A, v_ty)])
                         [(emit_var "P" Ab_v, emit_abs bv imp_cmb_q_bv)]
        val gen_v = c_eq_mp gen_inst abs_eq
                    (* gen_v: B \ {P[v/x]} ⊢ !bv. cmb_bv ==> q *)
        val choose_inst = c_inst (c_inst_type (candle_load_pth "candle$CHOOSE")
                            [(tyvar_A, v_ty)])
                            [(emit_var "P" Ab_v, pred_tm), (pvar_Q, q_tm)]
                          (* choose_inst: ⊢ (?pred_tm) ==> (!bv. pred_tm bv ==> q) ==> q *)
        val forall_v_imp = emit_comb
          (emit_const "!" (emit_tyop "fun" [Ab_v, bool_tyid])) (emit_abs bv imp_cmb_q_bv)
        val imp_forall_q = emit_comb (emit_comb imp_const forall_v_imp) q_tm
        val mp_choose1 = do_MP choose_inst exists_P_tm imp_forall_q b_th
                         (* mp_choose1: A ⊢ forall_v_imp ==> q *)
      in do_MP mp_choose1 forall_v_imp q_tm gen_v end
         (* result: A ∪ (B \ {P[v/x]}) ⊢ q *)

    (* SUBST_prf
       ----------
       HOL4 rule: [(v1, ⊢ l1 = r1), ...], template, A ⊢ P[l1/v1, ...]
                  →  A ⊢ P[r1/v1, ...]

       The template P contains free variables v1, v2, ... as placeholders.
       The source theorem c_th proves A ⊢ P with l1, l2, ... in place of v1, v2, ...
       Each subst pair provides vi and a theorem ⊢ li = ri.

       Derivation:
         rconv walks the template and source in parallel:
         - At a placeholder vi: return the corresponding theorem ⊢ li = ri
         - At a COMB: recursively walk both children, combine with MK_COMB
         - At an ABS: recursively walk the body with updated binder map, wrap with ABS_THM
         - At other leaves: REFL

         The result is ⊢ source = result where result has ri in place of li.
         Then EQ_MP gives A ⊢ result.
    *)
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
            else if DArray.sub(tm_part1, tmpl_id) >= 0 then
              let val (sv, sb) = pft_dest_abs src_id
                  val (tv, tb) = pft_dest_abs tmpl_id
              in c_abs sv (rconv ((tv, sv) :: binder_map) sb tb)
              end
            else if src_id = tmpl_id then c_refl src_id
            else raise Fail ("rconv: leaf mismatch: src "
                             ^ Int.toString src_id
                             ^ " vs tmpl " ^ Int.toString tmpl_id)
      in r_eq_mp (rconv [] source_id template_id) c_th end

    (* GEN_ABS_prf
       -------------
       HOL4 rule: (a) NONE, [v1,...,vn], A ⊢ l = r
                      →  A ⊢ (λv1...λvn. l) = (λv1...λvn. r)
                  (b) SOME c, [v1,...,vn], A ⊢ l = r
                      →  A ⊢ (c (λv1. c (λv2. ... c (λvn. l)...))) = (same for r)
                      where c is a binder constant like ! or ?

       Side condition: v1,...,vn not free in A

       Note: Fresh binders must be used for PFTRename compliance.

       Derivation:
         For each variable vi, working from innermost to outermost:
         - Create fresh binder bv
         - INST th_acc [(vi, bv)] to replace free vi with bv
         - If NONE: c_abs bv (th_acc')  (gives ⊢ (λbv. l) = (λbv. r))
         - If SOME c: c_mk_comb (REFL c) (c_abs bv th_acc')
                      (gives ⊢ c (λbv. l) = c (λbv. r))
    *)
    | GEN_ABS_prf (a, b, c) => let
        val vars = list heap tm b
        val c_th = th c
        (* HOL4's GEN_ABS retypes the binder per variable (Thm.list_mk_binder
           / Logging.GEN_ABS_prf), so we must too — otherwise mixed-type
           variable lists yield ill-typed MK_COMB terms.
           We create fresh binders and INST to satisfy PFTRename's
           uniqueness assumption. *)
        val step = case option heap (fn p => p) a of
            NONE => (fn (v_tm, th_acc) => let
              val v_ty = pft_type_of v_tm
              val bv = emit_binder "v" v_ty
              val th_acc' = c_inst th_acc [(v_tm, bv)]
            in c_abs bv th_acc' end)
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
            in fn (v_tm, th_acc) => let
                 val v_ty = pft_type_of v_tm
                 val bv = emit_binder "v" v_ty
                 val th_acc' = c_inst th_acc [(v_tm, bv)]
               in c_mk_comb (refl_at v_ty) (c_abs bv th_acc') end
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
              (* Use a fresh binder for the synthesized witness predicate,
                 then alpha-rename body_c accordingly. This preserves the
                 binder-uniqueness invariant expected by downstream tools
                 (e.g., PFTRename), instead of reusing v_id as binder for
                 multiple ABS nodes. *)
              val bv = emit_binder "v" v_ty
              val body_c_bv = pft_rename_free v_id bv body_c
              val pred_c = emit_abs bv body_c_bv
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
              val f = DArray.sub(tm_part1, tm_id)
            in if f < 0 then c_refl tm_id  (* VAR or CONST, not a v_i *)
               else let val x = DArray.sub(tm_part2, tm_id)
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
            (let val f = DArray.sub(tm_part1, tm_id)
             in f >= 0 andalso
                  let val x = DArray.sub(tm_part2, tm_id)
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

        (* Per-scope binder variables: each distinct ABS and each do_GEN
           gets a unique emit_binder so that PFTRename promise 2 holds:
           each binder VAR ID is the first argument of exactly one ABS and
           is referenced only within that ABS's body.
           Free occurrences of 'x', 'x\'', 'x\'\'' use emit_var so that
           they are distinct from all binder IDs (no 'pft%' suffix). *)
        val x_free = emit_var "x" rep_ty
        val phi_x = emit_comb pred_id x_free
        val abs_x = emit_comb abs_c x_free

        (* --- Injectivity proof (th_conj1) --- *)
        val bv_x'_inj = emit_binder "x'" new_ty
        val bv_x''_inj = emit_binder "x''" new_ty
        val rep_x'_inj = emit_comb rep_c bv_x'_inj
        val rep_x''_inj = emit_comb rep_c bv_x''_inj
        val ar_x'_inj = c_inst tydef_id [(var_a, bv_x'_inj)] (* ⊢ abs (rep x') = x' *)
        val ar_x''_inj = c_inst tydef_id [(var_a, bv_x''_inj)] (* ⊢ abs (rep x'') = x'' *)
        val rr = emit_comb (emit_comb eq_rep rep_x'_inj) rep_x''_inj (* rep x' = rep x'' *)
        val arr = do_AP_TERM abs_c (c_assume rr) (* rep x' = rep x'' ⊢ abs (rep x') = abs (rep x'') *)
        val th_inj = c_trans (c_trans (c_sym ar_x'_inj) arr) ar_x''_inj (* rep x' = rep x'' ⊢ x' = x'' *)
        val x'_eq_x'' = emit_comb (emit_comb eq_new bv_x'_inj) bv_x''_inj (* x' = x'' *)
        val inj_body = emit_comb (emit_comb (imp_const) rr) x'_eq_x'' (* rep x' = rep x'' ⇒ x' = x'' *)
        val forall_new = emit_const "!" Abb_new
        val th_conj1 = do_GEN bv_x'_inj new_ty
          (emit_comb forall_new (emit_abs bv_x''_inj inj_body))
          (do_GEN bv_x''_inj new_ty inj_body (do_DISCH rr x'_eq_x'' th_inj))
          (* ⊢ (∀x' x''. rep x' = rep x'' ⇒ x' = x'') *)

        (* --- Characterization proof (forward + backward) --- *)
        val ra_x = c_inst tydef_id2 [(var_r_rep, x_free)] (* ⊢ P x = (rep (abs x) = x) *)
        val sym_ra_x = c_sym ra_x (* ⊢ (rep (abs x) = x) = P x *)

        (* pred_exists: λx'_ex. x = rep x'_ex
           x'_ex is the binder of exactly one ABS (pred_exists).
           ar_x'_ex gives abs(rep x'_ex) = x'_ex, used in forward/backward. *)
        val bv_x'_ex = emit_binder "x'" new_ty
        val rep_x'_ex = emit_comb rep_c bv_x'_ex
        val x_eq_rep_x' = emit_comb (emit_comb eq_rep x_free) rep_x'_ex (* x = rep x' *)
        val pred_exists = emit_abs bv_x'_ex x_eq_rep_x' (* λx'. x = rep x' *)
        val exist_x_eq = emit_comb (emit_const "?" Abb_new) pred_exists (* ∃x'. x = rep x' *)
        val ar_x'_fwd = c_inst tydef_id [(var_a, bv_x'_ex)] (* ⊢ abs (rep x') = x' *)

        (* Forward: {phi x} |- ?x'. x = rep x' *)
        val sym_repabs = c_sym (c_eq_mp ra_x (c_assume phi_x)) (* P x ⊢ x = rep (abs x) *)
        val th_fwd = do_EXISTS pred_exists bv_x'_ex abs_x new_ty sym_repabs
        (* P x ⊢ ∃x'. x = rep x' *)

        (* Backward: {?x'. x = rep x'} |- phi x *)
        (* bv_x'_bwd is the argument to pred_exists in the beta-redex
           (λx'_ex. ...) bv_x'_bwd, and the binder of ∀x'_bwd. ... *)
        val bv_x'_bwd = emit_binder "x'" new_ty
        val rep_x'_bwd = emit_comb rep_c bv_x'_bwd
        val x_eq_rep_x'_bwd = emit_comb (emit_comb eq_rep x_free) rep_x'_bwd
        val assume_xeq = c_assume x_eq_rep_x'_bwd (* x = rep x' ⊢ x = rep x' *)
        val ar_x'_bwd = c_inst tydef_id [(var_a, bv_x'_bwd)] (* ⊢ abs (rep x') = x' for bv_x'_bwd *)
        val abs_x_eq_x' = c_trans (do_AP_TERM abs_c assume_xeq) ar_x'_bwd (* x = rep x' ⊢ abs x = x' *)
        val th_repabsx = c_trans (do_AP_TERM rep_c abs_x_eq_x') (c_sym assume_xeq) (* x = rep x' ⊢ rep (abs x) = x *)
        val th_phi_from_xeq = c_eq_mp sym_ra_x th_repabsx (* x = rep x' ⊢ P x *)
        (* pred_x' = (λx'_ex. x = rep x') x'_bwd — alpha-variant beta-redex *)
        val pred_x' = emit_comb pred_exists bv_x'_bwd (* (λx'. x = rep x') x' *)
        val beta_pred_x' = do_beta_reduce pred_exists bv_x'_bwd (* ⊢ (λx'. x = rep x') x' = x = rep x' *)
        val th_phi_from_pred_x' = c_prove_hyp
            (c_eq_mp beta_pred_x' (c_assume pred_x'))
            th_phi_from_xeq (* (λx'. x = rep x') x' ⊢ P x *)
        val pred_x'_imp_phi = emit_comb (emit_comb imp_const pred_x') phi_x (* (λx'. x = rep x') x' ⇒ P x *)
        val var_P_Ab_new = emit_var "P" Ab_new
        val choose_inst_bwd = c_inst (c_inst_type (candle_load_pth "candle$CHOOSE")
                                [(tyvar_A, new_ty)])
                                [(var_P_Ab_new, pred_exists), (pvar_Q, phi_x)]
                              (* ⊢ (∃x'. x = rep x') ⇒ (∀x''. (λx'. x = rep x') x'' ⇒ P x) ⇒ P x *)
        (* forall_new_imp: ∀x'_bwd. (λx'_ex. ...) x'_bwd ⇒ P x
           bv_x'_bwd is binder of exactly this one ABS. *)
        val forall_new_imp = emit_comb forall_new
            (emit_abs bv_x'_bwd pred_x'_imp_phi) (* ∀x'. (λx'. x = rep x') x' ⇒ P x *)
        val th_bwd1 = do_MP choose_inst_bwd exist_x_eq
                        (emit_comb (emit_comb imp_const forall_new_imp) phi_x)
                        (c_assume exist_x_eq)
                      (* ∃x'. x = rep x' ⊢ (∀x'. (λx'. x = rep x') x' ⇒ P x) ⇒ P x *)
        val th_bwd2 = do_DISCH pred_x' phi_x th_phi_from_pred_x' (* ⊢ (λx'. x = rep x') x' ⇒ P x *)
        val th_bwd3 = do_GEN bv_x'_bwd new_ty pred_x'_imp_phi th_bwd2 (* ⊢ ∀x'. (λx'. x = rep x') x' ⇒ P x *)
        val th_bwd = do_MP th_bwd1 forall_new_imp phi_x th_bwd3
                     (* ∃x'. x = rep x' ⊢ P x *)

        val th_char_x = c_deduct th_bwd th_fwd (* ⊢ P x = ∃x'. x = rep x' *)
        val phi_eq_exists = emit_comb (emit_comb (eq_bool_const) phi_x) exist_x_eq (* P x = ∃x'. x = rep x' *)

        (* th_conj2: generalize over x.  bv_x_c2 is binder of do_GEN's ABS. *)
        val bv_x_c2 = emit_binder "x" rep_ty
        val phi_x_c2 = emit_comb pred_id bv_x_c2
        (* Build exist_x_eq_c2 with bv_x_c2 in place of x_free, using a fresh binder *)
        val bv_x'_c2 = emit_binder "x'" new_ty
        val rep_x'_c2 = emit_comb rep_c bv_x'_c2
        val x_eq_rep_x'_c2 = emit_comb (emit_comb eq_rep bv_x_c2) rep_x'_c2
        val pred_exists_c2 = emit_abs bv_x'_c2 x_eq_rep_x'_c2
        val exist_x_eq_c2 = emit_comb (emit_const "?" Abb_new) pred_exists_c2
        val phi_eq_exists_c2 = emit_comb (emit_comb (eq_bool_const) phi_x_c2) exist_x_eq_c2
        val th_char_x_c2 = (* alpha-variant of th_char_x with bv_x_c2 for x_free *)
          c_inst th_char_x [(x_free, bv_x_c2)]
        val th_conj2 = do_GEN bv_x_c2 rep_ty phi_eq_exists_c2 th_char_x_c2
                       (* ⊢ ∀x. P x = ∃x'. x = rep x' *)

        val forall_rep = emit_const "!" (emit_tyop "fun" [Ab, bool_tyid])
        (* conj1_body: fresh binders for its two nested ABSes. *)
        val bv_x'_c1 = emit_binder "x'" new_ty
        val bv_x''_c1 = emit_binder "x''" new_ty
        val rep_x'_c1 = emit_comb rep_c bv_x'_c1
        val rep_x''_c1 = emit_comb rep_c bv_x''_c1
        val rr_c1 = emit_comb (emit_comb eq_rep rep_x'_c1) rep_x''_c1
        val x'_eq_x''_c1 = emit_comb (emit_comb eq_new bv_x'_c1) bv_x''_c1
        val inj_body_c1 = emit_comb (emit_comb (imp_const) rr_c1) x'_eq_x''_c1
        val conj1_body = emit_comb forall_new
          (emit_abs bv_x'_c1 (emit_comb forall_new (emit_abs bv_x''_c1 inj_body_c1)))
          (* ∀x' x''. rep x' = rep x'' ⇒ x' = x'' *)
        (* conj2_body: fresh binder. *)
        val bv_x_c2b = emit_binder "x" rep_ty
        val phi_x_c2b = emit_comb pred_id bv_x_c2b
        (* Build exist_x_eq_c2b with bv_x_c2b in place of x_free, using a fresh binder *)
        val bv_x'_c2b = emit_binder "x'" new_ty
        val rep_x'_c2b = emit_comb rep_c bv_x'_c2b
        val x_eq_rep_x'_c2b = emit_comb (emit_comb eq_rep bv_x_c2b) rep_x'_c2b
        val pred_exists_c2b = emit_abs bv_x'_c2b x_eq_rep_x'_c2b
        val exist_x_eq_c2b = emit_comb (emit_const "?" Abb_new) pred_exists_c2b
        val phi_eq_exists_c2b = emit_comb (emit_comb (eq_bool_const) phi_x_c2b) exist_x_eq_c2b
        val conj2_body = emit_comb forall_rep (emit_abs bv_x_c2b phi_eq_exists_c2b)
          (* ∀x. P x = ∃x'. x = rep x' *)
        val conj_th = do_CONJ conj1_body conj2_body th_conj1 th_conj2
          (* ⊢ (∀x' x''. rep x' = rep x'' ⇒ x' = x'') ∧
               (∀x. P x = ∃x'. x = rep x' *)

        (* --- Instantiate TYPE_DEFINITION_THM_FREE via INST_TYPE + INST --- *)

        val tydef_free = ensure_tydef_thm_free ()
        val tydef_inst = c_inst_type tydef_free
                           [(tyvar_A, rep_ty),
                            (tyvar_B, new_ty)]
        val tydef_inst2 = c_inst tydef_inst
                           [(emit_var "P" Ab, pred_id),
                            (emit_var "rep" rep_fn_ty, rep_c)]
        val tydef_proved = c_eq_mp (c_sym tydef_inst2) conj_th
         (* ⊢ TYPE_DEFINITION pred_id rep_c *)

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
        val bv_t_eta = emit_binder "t" Ab
        val bv_x_eta = emit_binder "x" rep_ty
        val abs_x_t_x = emit_abs bv_x_eta (emit_comb bv_t_eta bv_x_eta)
        val eta_eq_body = emit_comb (emit_comb eq_Ab abs_x_t_x) bv_t_eta
        val abs_eta_eq = emit_abs bv_t_eta eta_eq_body
        val forall_Ab = emit_const "!"
          (emit_tyop "fun" [emit_tyop "fun" [Ab, bool_tyid], bool_tyid])
        val P_uneta_eq = do_SPEC pred_uneta abs_eta_eq
                           (emit_comb forall_Ab abs_eta_eq) Ab eta_inst
         (* ⊢ (λx. P x) = P *)

        val rep_fn_ty_bool = emit_tyop "fun" [rep_fn_ty, bool_tyid]
        val tydef_ty = emit_tyop "fun" [Ab, rep_fn_ty_bool]
        val tydef_c = emit_const "bool$TYPE_DEFINITION" tydef_ty

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

        val bv_rep_v = emit_binder "rep" rep_fn_ty
        val tydef_P_bv_rep =
          emit_comb (emit_comb tydef_c pred_uneta) bv_rep_v
        val exist_pred_rep_uneta = emit_abs bv_rep_v tydef_P_bv_rep
         (* λrep. TYPE_DEFINITION P rep *)
      in do_EXISTS exist_pred_rep_uneta bv_rep_v rep_c rep_fn_ty tydef_uneta end

    | compute_prf (a, b) =>
        let
          (* Ensure compute preamble is emitted (once per trace) *)
          val () = if !compute_preamble_emitted then ()
                   else (PFTCandleComputePreamble.emit {
                           out = out,
                           alloc_ty = alloc_ty,
                           alloc_tm = alloc_tm,
                           alloc_th = alloc_th,
                           load_theorem = candle_load_pth
                         };
                         compute_preamble_emitted := true)

          (* Ensure COMPUTE_INIT is emitted (once after preamble) *)
          val ci_id =
            if !candle_compute_init_id >= 0 then !candle_compute_init_id
            else let
              val cid = emit_candle_compute_init ()
            in candle_compute_init_id := cid; cid end

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

          (* Call COMPUTE: ci_id, candle_input_tm, code_eqn_ths
             Returns theorem: candle_input_tm = candle_result *)
          val compute_th_id = alloc_th ()
          val () = PFTWriter.Candle.compute out compute_th_id ci_id
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

  (* Emit COMPUTE_INIT with the 62 characteristic equations from preamble *)
  and emit_candle_compute_init () : int = let
    (* Load all 62 characteristic equations from preamble *)
    val eq_ids = List.tabulate (62, fn i =>
      candle_load_pth ("candle$COMPUTE_EQ_" ^ Int.toString (i + 1)))
    val ci_id = alloc_ci ()
    val () = PFTWriter.Candle.compute_init out ci_id eq_ids
  in ci_id end

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
      val (f_id, x_id) = (DArray.sub(tm_part1, bits_id), DArray.sub(tm_part2, bits_id))
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
      (* translate_term_numerals_hol4_to_candle: Abs case
         -------------------------------------------------
         Input: tm_ptr points to Abs (var_ptr, body_ptr) in heap
                tm_id is already-emitted term ID for this Abs
         
         We need to translate numerals in the body. If the body changes,
         we produce:
           abs_th: (λv. body) = (λv. body')  (where body' has Candle numerals)
           result_tm: the term ID for (λv. body')

         The theorem uses ABS_THM: if ⊢ body = body', then ⊢ (λv.body) = (λv.body')
         provided v not free in the hypotheses (which is satisfied since both are ⊢).

         CRITICAL: We must use a FRESH binder for the new ABS term to satisfy
         PFTRename assumption #2 (each binder VAR ID is first arg of exactly one ABS).
         The original var_id is already the binder of tm_id's ABS.

         Strategy:
           1. Get original binder var_id from tm_id
           2. Recursively translate body
           3. If body changed (body_th ≠ ~1):
              a. Create fresh binder new_bv
              b. INST body_th [var_id ↦ new_bv] to get ⊢ body[new_bv/v] = body'[new_bv/v]
              c. ABS_THM new_bv on that to get ⊢ (λnew_bv. body[new_bv/v]) = (λnew_bv. body'[new_bv/v])
              d. Build result term using new_bv as binder
              e. Chain with alpha-equivalence (REFL) on both sides if needed
              
         Actually simpler: ABS_THM var_id body_th gives ⊢ (λvar_id. body) = (λvar_id. body').
         The result term (λvar_id. body') is alpha-equivalent to what we want, but we
         need a term ID for it. We can't reuse var_id as binder for a NEW abs term.
         
         Solution: Create fresh binder, substitute in both body and body', use that
         for the new ABS. The result is alpha-equivalent to the original. *)
      | Abs (var_ptr, body_ptr) =>
          let
            val (var_id, body_id_orig) = pft_dest_abs tm_id
            val body_id = emit_term body_ptr
            val (body_c, body_th) = translate_term_numerals_hol4_to_candle body_ptr body_id
          in
            if body_th < 0 then (tm_id, ~1)
            else
              let
                (* Create fresh binder for the new ABS term *)
                val var_ty = pft_type_of var_id
                val new_bv = emit_binder "v" var_ty
                (* Substitute the fresh binder for the original binder in body_th *)
                val body_th_subst = let val id = alloc_th ()
                  in PFTWriter.Candle.inst out id body_th [(var_id, new_bv)]; id end
                (* body_th_subst: ⊢ body[new_bv/var_id] = body'[new_bv/var_id] *)
                val abs_th = let val id = alloc_th ()
                  in PFTWriter.Candle.abs_thm out id new_bv body_th_subst; id end
                (* abs_th: ⊢ (λnew_bv. body[new_bv/v]) = (λnew_bv. body'[new_bv/v]) *)
                val body_c_subst = pft_subst_tm var_id new_bv body_c
                val result_tm = emit_abs new_bv body_c_subst
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
            tm_types_set id ty_id; id
         end
    end

  (* Like emit_var but uses fresh_binder_name for unique binder names.
     Used for synthesized lambda binders in Candle translations. *)
  and emit_binder name ty_id =
    let val id = alloc_tm ()
        val bname = fresh_binder_name name
    in PFTWriter.var out id bname ty_id;
       tm_types_set id ty_id; id
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
    else let val f = DArray.sub(tm_part1, tm_id)
    in if f < 0 then tm_id (* VAR or CONST — no children *)
       else let val x = DArray.sub(tm_part2, tm_id)
                val f' = pft_subst_tm old_id new_id f
                val x' = pft_subst_tm old_id new_id x
            in if f' = f andalso x' = x then tm_id
               else case IntPairTable.lookup comb_ht (f, x) of
                      SOME _ => emit_comb f' x'
                    | NONE   => emit_abs f' x'
            end
    end

  (* Rename free occurrences of old_id to new_id in tm_id.
     Unlike pft_subst_tm, this is binder-aware and does not rewrite
     occurrences of old_id that are bound by an enclosing ABS old_id.
     This is used for alpha-renaming synthesized binders while preserving
     PFTRename's binder-uniqueness invariant. *)
  and pft_rename_free old_id new_id tm_id =
    let
      fun go shadowed t =
        if t = old_id then (if shadowed then t else new_id)
        else let val f = DArray.sub(tm_part1, t)
        in if f < 0 then t (* VAR or CONST *)
           else let
             val x = DArray.sub(tm_part2, t)
           in
             if isSome (IntPairTable.lookup comb_ht (f, x)) then
               let val f' = go shadowed f
                   val x' = go shadowed x
               in if f' = f andalso x' = x then t else emit_comb f' x' end
             else
               (* ABS f x: entering body shadows old_id iff binder = old_id *)
               let val x' = go (shadowed orelse f = old_id) x
               in if x' = x then t else emit_abs f x' end
           end
        end
    in
      go false tm_id
    end

  (* ======================================================================= *)
  (* compute (HOL4)                                                          *)
  (* ======================================================================= *)

  and emit_compute thm_id ((compute_args_ptr, ths_ptr), tm_p) = let
    val ci_id = emit_compute_init compute_args_ptr
    val th_id_list = list heap emit_thm ths_ptr
    val tm_id = emit_term tm_p
  in PFTWriter.HOL4.compute out thm_id ci_id tm_id th_id_list end

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
       val ci_id = alloc_ci ()
       val () = PFTWriter.HOL4.compute_init out ci_id num_ty cval_ty
           char_eqns cval_terms
       val () = ci_memo_set k ci_id
     in ci_id end
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
  val n_ci = !next_ci

in
  PFTWriter.closeOut out
    {n_ty = n_ty, n_tm = n_tm, n_th = n_th, n_ci = n_ci}
end

end
