structure PFTEmit :> PFTEmit = struct

open Lib Redblackset Redblackmap ProofTraceParser

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

(* When processing boolTheory in Candle mode, certain constants and axioms
   are already provided by the preamble.  Their definitions/axioms must be
   skipped and replaced by LOADs from the preamble.

   candle_preamble_def: maps the unqualified constant name (as it appears
     in the bool theory heap, e.g. "T") to the preamble SAVE name for
     the definition theorem that has the HOL4-compatible conclusion.

   candle_preamble_axiom: maps the axiom name string (from the trace) to
     the preamble SAVE name for the corresponding theorem. *)
val candle_preamble_def : (string * string) list = [
  ("T",   "candle$T_DEF"),
  ("/\\", "candle$AND_DEF_HOL4"),
  ("!",   "candle$FORALL_DEF"),
  ("?",   "candle$EXISTS_DEF_HOL4"),
  ("\\/", "candle$OR_DEF"),
  ("F",   "candle$F_DEF"),
  ("~",   "candle$NOT_DEF")
]

val candle_preamble_axiom : (string * string) list = [
  ("SELECT_AX", "candle$SELECT_AX"),
  ("ETA_AX",    "candle$ETA_AX"),
  ("BOOL_CASES_AX", "candle$BOOL_CASES_AX")
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
        val () = if Thy = thyname andalso not (is_const_done Name)
                 then (mark_const Name;
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

    (* TYVAR "A" for INST_TYPE on polymorphic pro-formas *)
    val tyvar_A = mk_tyvar_cached "A"

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
      val (bv_id, _) = pft_dest_abs pred_id
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
      val var_x_v = emit_var "x" v_ty
      val forall_inner = emit_comb (emit_const "!" (emit_tyop "fun" [Ab, bool_tyid]))
        (emit_abs var_x_v (emit_comb (emit_comb (imp_const) (emit_comb pred_id var_x_v)) pred_witness))
      val imp_forall_pw = emit_comb (emit_comb (imp_const) forall_inner) pred_witness
      val mp1 = do_MP choose_inst exists_concl_id imp_forall_pw exists_th
      val result = do_MP mp1 forall_inner pred_witness sel_inst
    in (result, pred_id, Ab, v_ty) end

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

    | Mk_abs_prf (a, _, c) => let
        val a_th = th a val c_th = th c
        val concl_id = tm (heap_concl a)
        val (_, rhs_id) = pft_dest_comb concl_id
        val (v_id, _) = pft_dest_abs rhs_id
      in r_trans a_th (c_abs v_id c_th) end

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
        fun rconv binder_map src_id tmpl_id =
          if src_id = tmpl_id then c_refl src_id
          else
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
              let val (sf, sx) = pft_dest_comb src_id
                  val (tf, tx) = pft_dest_comb tmpl_id
              in c_mk_comb (rconv binder_map sf tf) (rconv binder_map sx tx)
              end
              handle Fail _ =>
              let val (sv, sb) = pft_dest_abs src_id
                  val (tv, tb) = pft_dest_abs tmpl_id
              in c_abs sv (rconv ((tv, sv) :: binder_map) sb tb)
              end
      in r_eq_mp (rconv [] source_id template_id) c_th end

    | GEN_ABS_prf (a, b, c) => let
        val opt_c = option heap tm a
        val vars = list heap tm b
        val c_th = th c
        fun fold_one (v_tm, th_acc) =
          let val abs_th = c_abs v_tm th_acc
          in case opt_c of
               NONE => abs_th
             | SOME c_tm => c_mk_comb (c_refl c_tm) abs_th
          end
        val rev_vars = List.rev vars
        fun loop [] acc = acc
          | loop (v :: rest) acc = loop rest (fold_one (v, acc))
        val r = loop rev_vars c_th
      in r end

    (* === Definition commands === *)
    | Def_const_prf (a, b) => let
        val (Thy, Name) = get_const_id b
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
             val () = mark_const Name
           in candle_load_pth load_name end
         | NONE => let
             val rhs_id = emit_term a
             val rhs_ty_id = pft_type_of rhs_id
             val bool_ty_c = emit_tyop "bool" []
             val eq_ty = emit_tyop "fun" [rhs_ty_id, emit_tyop "fun" [rhs_ty_id, bool_ty_c]]
             val cname = tr_name (thyname ^ "$" ^ Name)
             val eq_tm = emit_comb (emit_comb (emit_const "=" eq_ty)
                           (emit_var cname rhs_ty_id)) rhs_id
             val () = mark_const Name
           in PFTWriter.Candle.new_specification out result_id
                (c_assume eq_tm) [cname]; result_id end
      end

    | Def_const_list_prf (a, b) => let
        val ids = list heap get_const_id b
        val preamble_name =
          if thyname = "bool" then
            case ids of [(_, nm)] =>
              List.find (fn (k,_) => k = nm) candle_preamble_def
            | _ => NONE
          else NONE
      in case preamble_name of
           SOME (_, load_name) =>
             (mark_const (#2 (hd ids)); candle_load_pth load_name)
         | NONE => let
             val a_th = th a
             val names = List.map (fn (Thy,nm) => tr_name (Thy ^ "$" ^ nm)) ids
             val () = List.app (fn (_,nm) => mark_const nm) ids
           in PFTWriter.Candle.new_specification out result_id a_th names;
              result_id end
      end

    | Def_spec_prf (a, b) => let
        val const_ptrs = list heap (fn p => p) b
        val input_th = th a
        val input_concl_id = tm (heap_concl a)

        (* Iterate over constants, stripping one existential per
           constant and replacing each witness with a fresh variable
           whose name matches the constant being defined.  After the
           loop we have {c1=w1,...,cn=wn} ⊢ P c1 ... cn which is
           exactly the input that new_specification expects. *)
        fun strip_one (const_ptr, (th_acc, exists_tm, names)) = let
          val (_, pred_id) = pft_dest_comb exists_tm
          val (bv_id, body_id) = pft_dest_abs pred_id
          val v_ty = pft_type_of bv_id
          val Ab = emit_tyop "fun" [v_ty, bool_tyid]
          val select_c = emit_const "@" (emit_tyop "fun" [Ab, v_ty])
          val witness = emit_comb select_c pred_id
          val (Thy, Name) = get_const_id const_ptr
          val cname = tr_name (Thy ^ "$" ^ Name)
          val var_i = emit_var cname v_ty
          val () = mark_const Name

          (* Build equality var_i = witness and assume it *)
          val eq_ty = emit_tyop "fun" [v_ty, emit_tyop "fun" [v_ty, bool_tyid]]
          val eq_tm = emit_comb (emit_comb (emit_const "=" eq_ty) var_i) witness
          val sym_eq = c_sym (c_assume eq_tm)
          (* sym_eq: {var_i = witness} ⊢ witness = var_i *)

          (* Strip one existential using EXISTS_DEF_HOL4:
               ⊢ ? = λP. P(@P)  (at type A)
             INST_TYPE A := v_ty, then AP_THM with pred_id:
               ⊢ ?pred = (λP. P(@P)) pred
             beta-reduce and TRANS:
               ⊢ ?pred = pred(@pred)  i.e. ?pred = pred(witness)
             EQ_MP with th_acc:
               ... ⊢ pred(witness) *)
          val exists_def = c_inst_type
                (candle_load_pth "candle$EXISTS_DEF_HOL4")
                [(tyvar_A, v_ty)]
          (* exists_def: ⊢ ?(v_ty) = λP:(v_ty→bool). P(@P) *)
          val ap_th = c_mk_comb exists_def (c_refl pred_id)
          (* ap_th: ⊢ ?pred = (λP. P(@P)) pred *)
          val lam_body = emit_comb (emit_var "P" Ab)
                (emit_comb select_c (emit_var "P" Ab))
          val lam_P_select = emit_abs (emit_var "P" Ab) lam_body
          val beta1 = do_beta_reduce lam_P_select pred_id
          (* beta1: ⊢ (λP. P(@P)) pred = pred(@pred) *)
          val strip_eq = c_trans ap_th beta1
          (* strip_eq: ⊢ ?pred = pred(witness) *)
          val th1 = c_eq_mp strip_eq th_acc
          (* th1: ... ⊢ pred(witness) *)

          (* Replace witness with variable:
               AP_TERM pred (witness = var_i): {ci=wi} ⊢ pred(wi) = pred(ci)
               EQ_MP: {ci=wi,...} ⊢ pred(ci) *)
          val th2 = c_eq_mp (do_AP_TERM pred_id sym_eq) th1
          (* th2: {..., ci=wi} ⊢ pred(var_i) *)

          (* Beta-reduce: ⊢ pred(var_i) = body[var_i/bv]
             EQ_MP: {..., ci=wi} ⊢ body[var_i/bv] *)
          val th3 = c_eq_mp (do_beta_reduce pred_id var_i) th2

          (* Update exists_tm for next iteration *)
          val next_exists_tm = pft_subst_tm bv_id var_i body_id
        in (th3, next_exists_tm, cname :: names) end

      in case const_ptrs of
           [] => input_th
         | _ => let
             val (final_th, _, rev_names) =
               List.foldl strip_one (input_th, input_concl_id, []) const_ptrs
             val names = List.rev rev_names
           in PFTWriter.Candle.new_specification out result_id final_th names;
              result_id
           end
      end

    | Def_tyop_prf (a, b, c) => let
        val _ = list heap ty a
        val () = if thyname = "bool"
                 then check_def tm_defs thyname "TYPE_DEFINITION" else ()
        val b_th = th b
        val (Thy, Tyop) = get_type_id c
        val () = mark_type Tyop
        val tyname = tr_name (Thy ^ "$" ^ Tyop)
        val (th_pw, pred_id, Ab, rep_ty) =
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
        val var_x_rep = emit_var "x" rep_ty
        val var_x' = emit_var "x'" new_ty
        val var_x'' = emit_var "x''" new_ty
        val rep_x' = emit_comb rep_c var_x'
        val rep_x'' = emit_comb rep_c var_x''
        val abs_x = emit_comb abs_c var_x_rep
        val phi_x = emit_comb pred_id var_x_rep

        val ar_x' = c_inst tydef_id [(var_a, var_x')] (* ⊢ abs (rep x') = x' *)
        val ar_x'' = c_inst tydef_id [(var_a, var_x'')] (* ⊢ abs (rep x'') = x'' *)
        val rr = emit_comb (emit_comb eq_rep rep_x') rep_x'' (* rep x' = rep x'' *)
        val arr = do_AP_TERM abs_c (c_assume rr) (* rep x' = rep x'' ⊢ abs (rep x') = abs (rep x'') *)
        val th_inj = c_trans (c_trans (c_sym ar_x') arr) ar_x'' (* rep x' = rep x'' ⊢ x' = x'' *)
        val x'_eq_x'' = emit_comb (emit_comb eq_new var_x') var_x'' (* x' = x'' *)
        val inj_body = emit_comb (emit_comb (imp_const) rr) x'_eq_x'' (* rep x' = rep x'' ⇒ x' = x'' *)
        val forall_new = emit_const "!" Abb_new
        val th_conj1 = do_GEN var_x' new_ty
          (emit_comb forall_new (emit_abs var_x'' inj_body))
          (do_GEN var_x'' new_ty inj_body (do_DISCH rr x'_eq_x'' th_inj))
          (* ⊢ (∀x' x''. rep x' = rep x'' ⇒ x' = x'') *)

        val ra_x = c_inst tydef_id2 [(var_r_rep, var_x_rep)] (* ⊢ P x = (rep (abs x) = x) *)
        val sym_ra_x = c_sym ra_x (* ⊢ (rep (abs x) = x) = P x *)
        val x_eq_rep_x' = emit_comb (emit_comb eq_rep var_x_rep) rep_x' (* x = rep x' *)
        val pred_exists = emit_abs var_x' x_eq_rep_x' (* λx'. x = rep x' *)
        val exist_x_eq = emit_comb (emit_const "?" Abb_new) pred_exists (* ∃x'. x = rep x' *)

        (* Forward: {phi x} |- ?x'. x = rep x' *)
        val sym_repabs = c_sym (c_eq_mp ra_x (c_assume phi_x)) (* P x ⊢ x = rep (abs x) *)
        val th_fwd = do_EXISTS pred_exists var_x' abs_x new_ty sym_repabs
        (* P x ⊢ ∃x'. x = rep x' *)

        (* Backward: {?x'. x = rep x'} |- phi x *)
        val pred_x' = emit_comb pred_exists var_x' (* (λx'. x = rep x') x' *)
        val assume_xeq = c_assume x_eq_rep_x' (* x = rep x' ⊢ x = rep x' *)
        val abs_x_eq_x' = c_trans (do_AP_TERM abs_c assume_xeq) ar_x' (* x = rep x' ⊢ abs x = x' *)
        val th_repabsx = c_trans (do_AP_TERM rep_c abs_x_eq_x') (c_sym assume_xeq) (* x = rep x' ⊢ rep (abs x) = x *)
        val th_phi_from_xeq = c_eq_mp sym_ra_x th_repabsx (* x = rep x' ⊢ P x *)
        val beta_pred_x' = do_beta_reduce pred_exists var_x' (* ⊢ (λx'. x = rep x') x' = x = rep x' *)
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
            (emit_abs var_x' pred_x'_imp_phi) (* ∀x'. (λx'. x = rep x') x' ⇒ P x *)
        val th_bwd1 = do_MP choose_inst_bwd exist_x_eq
                        (emit_comb (emit_comb imp_const forall_new_imp) phi_x)
                        (c_assume exist_x_eq)
                      (* ∃x'. x = rep x' ⊢ (∀x'. (λx'. x = rep x') x' ⇒ P x) ⇒ P x *)
        val th_bwd2 = do_DISCH pred_x' phi_x th_phi_from_pred_x' (* ⊢ (λx'. x = rep x') x' ⇒ P x *)
        val th_bwd3 = do_GEN var_x' new_ty pred_x'_imp_phi th_bwd2 (* ⊢ ∀x'. (λx'. x = rep x') x' ⇒ P x *)
        val th_bwd = do_MP th_bwd1 forall_new_imp phi_x th_bwd3
                     (* ∃x'. x = rep x' ⊢ P x *)

        val th_char_x = c_deduct th_bwd th_fwd (* ⊢ P x = ∃x'. x = rep x' *)
        val phi_eq_exists = emit_comb (emit_comb (eq_bool_const) phi_x) exist_x_eq (* P x = ∃x'. x = rep x' *)
        val th_conj2 = do_GEN var_x_rep rep_ty phi_eq_exists th_char_x
                       (* ⊢ ∀x. P x = ∃x'. x = rep x' *)

        val forall_rep = emit_const "!" (emit_tyop "fun" [Ab, bool_tyid])
        val conj1_body = emit_comb forall_new
          (emit_abs var_x' (emit_comb forall_new (emit_abs var_x'' inj_body)))
          (* ∀x' x''. rep x' = rep x'' ⇒ x' = x'' *)
        val conj2_body = emit_comb forall_rep (emit_abs var_x_rep phi_eq_exists)
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
                           [(mk_tyvar_cached "'a", rep_ty),
                            (mk_tyvar_cached "'b", new_ty)]
          (* ∀P rep. TYPE_DEFINITION P rep ⇔
                     (∀x' x''. rep x' = rep x'' ⇒ x' = x'') ∧
                     (∀x. P x ⇔ ∃x'. x = rep x') *)
        val var_P_v = emit_var "P" Ab
        val var_rep_v = emit_var "rep" rep_fn_ty
        val rep_fn_ty_bool = emit_tyop "fun" [rep_fn_ty, bool_tyid]
        val tydef_ty = emit_tyop "fun" [Ab, rep_fn_ty_bool]
        val tydef_c = emit_const "bool$TYPE_DEFINITION" tydef_ty
        val forall_rep_fn = emit_const "!"
          (emit_tyop "fun" [rep_fn_ty_bool, bool_tyid])

        (* Build the TYPE_DEFINITION body with generic P, rep variables.
           TYPE_DEFINITION P rep ≡
             (∀x' x''. rep x' = rep x'' ⇒ x' = x'') ∧
             (∀x. P x = ∃x'. x = rep x') *)
        val rep_v_x' = emit_comb var_rep_v var_x' (* rep x' *)
        val rep_v_x'' = emit_comb var_rep_v var_x'' (* rep x'' *)
        val inj_body_v = emit_comb forall_new
          (emit_abs var_x' (emit_comb forall_new (emit_abs var_x''
            (emit_comb (emit_comb imp_const
              (emit_comb (emit_comb eq_rep rep_v_x') rep_v_x''))
              (emit_comb (emit_comb eq_new var_x') var_x'')))))
           (* ∀x' x''. rep x' = rep x'' ⇒ x' = x'' *)
        val exist_v = emit_comb (emit_const "?" (emit_tyop "fun" [Ab_new, bool_tyid]))
          (emit_abs var_x' (emit_comb (emit_comb eq_rep var_x_rep) rep_v_x'))
           (* ∃x'. x = rep x' *)
        fun mk_char_body P_x = emit_comb forall_rep
          (emit_abs var_x_rep (emit_comb (emit_comb eq_bool_const P_x) exist_v))
           (* ∀x. ^P_x = ∃x'. x = rep x' *)
        val and_inj_body_v = emit_comb and_const inj_body_v
        val tydef_body_v = emit_comb and_inj_body_v
                             (mk_char_body (emit_comb var_P_v var_x_rep))
           (* (∀x' x''. rep x' = rep x'' ⇒ x' = x'') ∧
              (∀x. P x = ∃x'. x = rep x') *)
        val tydef_eq_v = emit_comb (emit_comb eq_bool_const
          (emit_comb (emit_comb tydef_c var_P_v) var_rep_v)) tydef_body_v
           (* TYPE_DEFINITION P rep = ... *)
        val inner_forall = emit_comb forall_rep_fn (emit_abs var_rep_v tydef_eq_v)
           (* ∀rep. TYPE_DEFINITION P rep = ... *)
        val outer_lam = emit_abs var_P_v inner_forall
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
        val tydef_phi_var_rep = emit_comb (emit_comb tydef_c pred_id) var_rep_v
        val tydef_phi_eq = emit_comb
                             (emit_comb eq_bool_const tydef_phi_var_rep)
                                 tydef_phi_body
        val lam_rep_tydef_phi_eq = emit_abs var_rep_v tydef_phi_eq
        val inner_forall2 = emit_comb forall_rep_fn lam_rep_tydef_phi_eq
                            (* ∀rep. TYPE_DEFINITION P rep = ... *)
        val spec2 = do_SPEC rep_c lam_rep_tydef_phi_eq
                      inner_forall2 rep_fn_ty spec1
         (* ⊢ TYPE_DEFINITION P rep = ... *)

        val tydef_proved = c_eq_mp (c_sym spec2) conj_th
         (* ⊢ TYPE_DEFINITION P rep *)

        val exist_pred_rep = emit_abs var_rep_v tydef_phi_var_rep
      in do_EXISTS exist_pred_rep var_rep_v rep_c rep_fn_ty tydef_proved end

    | compute_prf (a, b) => raise Fail "emit_thm_candle: compute not yet implemented"

    | save_dep_prf _ => raise Fail "unreachable"
    | deleted_prf => raise Fail "emit_thm_candle: deleted"
    | Axiom_prf => raise Fail "unreachable: handled in emit_thm"
    | Disk_prf _ => raise Fail "unreachable: handled in emit_thm"
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
           in th_memo_set k actual_id; actual_id end
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
              val () = List.app (fn (_,nm) => mark_const nm) ids
            in PFTWriter.HOL4.def_spec_gen out id a names end
          | Def_const_prf (a, b) => emit_def_const id (a, b)
          | Def_spec_prf (a, b) => let
              val a = emit_thm a
              val ids = list heap get_const_id b
              val names = List.map (fn (Thy,nm) => tr_name (Thy ^ "$" ^ nm)) ids
              val () = List.app (fn (_,nm) => mark_const nm) ids
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
    val () = mark_const Name
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
  in if is_const_done Name then ()
     else let
       val ty_id = emit_type ty_ptr
       val () = mark_const Name
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
