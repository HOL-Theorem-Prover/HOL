structure PFTMerge :> PFTMerge = struct

datatype thm_ref = NamedThm of string | AnonThm of int

datatype target = ThyThm of string * string * bool
                | ThyAll of string * bool

open PFTOpcodes

(* ========================================================================= *)
(* Namespaces                                                                *)
(* ========================================================================= *)

val NS_TY = 0 val NS_TM = 1 val NS_TH = 2 val NS_CI = 3 val NUM_NS = 4

fun ns_idx "ty" = NS_TY | ns_idx "tm" = NS_TM
  | ns_idx "th" = NS_TH | ns_idx "ci" = NS_CI
  | ns_idx s = raise Fail ("PFTMerge: bad namespace " ^ s)

val ns_names = Vector.fromList ["ty","tm","th","ci"]
fun ns_name i = Vector.sub(ns_names, i)

(* ========================================================================= *)
(* ID Free-list Allocator                                                    *)
(* ========================================================================= *)

structure IdAlloc = struct
  type t = {next: int ref, free: int list ref, peak: int ref}

  fun new () : t = {next = ref 0, free = ref [], peak = ref 0}

  fun alloc ({next, free, peak}: t) =
    case !free of
      id :: rest => (free := rest; id)
    | [] => let val id = !next
            in next := id + 1;
               if id >= !peak then peak := id + 1 else ();
               id end

  fun release ({free, ...}: t) id = free := id :: (!free)

  fun peakCount ({peak, ...}: t) = !peak

  (* Allocate n consecutive IDs, bypassing the free list *)
  fun alloc_consecutive ({next, peak, ...}: t) n =
    let val id = !next
    in next := id + n;
       if id + n > !peak then peak := id + n else ();
       id end
end

(* ========================================================================= *)
(* Pass 1: Ingest and build dependency graph                                 *)
(* ========================================================================= *)

datatype cmd_kind =
    CmdNormal
  | CmdSave of string
  | CmdLoad of string
  | CmdDel
  | CmdDef
  | CmdNewConst
  | CmdNewType
  | CmdAxiom

type cmd_meta = {
  produced : (int * int) list, (* (ns_idx, id) *)
  consumed : (int * int) list, (* (ns_idx, id) *)
  kind : cmd_kind,
  opcode : int,
  ref_name : string option     (* name referenced by CONST/TYOP *)
}

val empty_meta : cmd_meta =
  {produced=[], consumed=[], kind=CmdNormal, opcode=0, ref_name=NONE}

(* Consume arguments from stream according to descriptors, collecting
   the (ns_idx, id) pairs of all referenced IDs and any introduced
   type/constant names from definition commands. *)
fun collect_consumed (sr: PFTReader.stream_reader) (specs: arg_spec list)
    : (int * int) list * {new_types: string list, new_consts: string list} =
  let
    val vi = #readVarint sr
    val vs = #readString sr
    val acc = ref ([] : (int * int) list)
    val new_types = ref ([] : string list)
    val new_consts = ref ([] : string list)
    fun add ns id = acc := (ns_idx ns, id) :: (!acc)
    fun one ({shape, role, ...}: arg_spec) =
      (case shape of
         AId ns          => add ns (vi ())
       | AVal            => ignore (vi ())
       | AIdList ns      => List.app (add ns) (#readVarintList sr ())
       | AIdPairs (n1,n2) => List.app (fn (a,b) => (add n1 a; add n2 b))
                               (#readVarintPairs sr ())
       | AStrIdPairs ns  => List.app (fn (_,id) => add ns id)
                               (#readStringVarintPairs sr ())
       | AName           => (case role of
                               RNewType  => new_types := vs () :: !new_types
                             | RNewConst => new_consts := vs () :: !new_consts
                             | _         => ignore (vs ()))
       | ANameList       => (case role of
                               RNewConsts => new_consts :=
                                 !new_consts @ #readStringList sr ()
                             | _          => ignore (#readStringList sr ())))
  in List.app one specs;
     (List.rev (!acc),
      {new_types = List.rev (!new_types),
       new_consts = List.rev (!new_consts)})
  end

(* Per-file state *)
type file_state = {
  file_idx : int,
  cmds : cmd_meta DArray.darray,
  producers : int DArray.darray vector
}

fun ensure_darray_size da n =
  let fun loop () =
        if DArray.size da >= n then ()
        else (DArray.push(da, ~1); loop ())
  in loop () end

fun set_producer producers ns id ci =
  let val da = Vector.sub(producers, ns)
  in ensure_darray_size da (id + 1);
     DArray.update(da, id, ci)
  end

fun get_producer producers ns id =
  let val da = Vector.sub(producers, ns)
  in if id < DArray.size da then DArray.sub(da, id) else ~1 end

fun new_file_state fi : file_state = {
  file_idx = fi,
  cmds = DArray.new(1024, empty_meta),
  producers = Vector.tabulate(NUM_NS, fn _ => DArray.new(1024, ~1))
}

fun add_cmd (fs: file_state) (meta: cmd_meta) =
  let val ci = DArray.size (#cmds fs)
  in DArray.push(#cmds fs, meta);
     List.app (fn (ns, id) =>
       set_producer (#producers fs) ns id ci)
       (#produced meta);
     ci
  end

fun find_producer (fs: file_state) (ns, id) =
  let val ci = get_producer (#producers fs) ns id
  in if ci >= 0 then ci
     else raise Fail ("PFTMerge: no producer for " ^ ns_name ns ^ "#" ^
                      Int.toString id ^ " in file " ^
                      Int.toString (#file_idx fs))
  end

type save_entry = {file_idx: int, cmd_idx: int, th_id: int}

fun pass1_read_file (descs_ref: (int * opcode_desc) list ref)
                    (file_idx: int) (file: string)
                    (save_table: (string, save_entry) Redblackmap.dict ref)
                    (const_introducer: (string, int * int) Redblackmap.dict ref)
                    (type_introducer: (string, int * int) Redblackmap.dict ref)
    : file_state =
  let
    val fs = new_file_state file_idx
    fun cmd p c k o' rn = ignore (add_cmd fs {produced=p, consumed=c,
                                              kind=k, opcode=o',
                                              ref_name=rn})
    fun add_const_introducer name ci =
      const_introducer :=
        Redblackmap.insert(!const_introducer, name, (file_idx, ci))
    fun add_type_introducer name ci =
      type_introducer :=
        Redblackmap.insert(!type_introducer, name, (file_idx, ci))
    val fh : PFTReader.format_handler = {
      tyvar = fn (id, _) =>
        cmd [(NS_TY,id)] [] CmdNormal 0x01 NONE,
      tyop = fn (id, name, args) =>
        cmd [(NS_TY,id)] (map (fn a => (NS_TY,a)) args) CmdNormal 0x02
            (SOME name),
      var = fn (id, _, ty) =>
        cmd [(NS_TM,id)] [(NS_TY,ty)] CmdNormal 0x03 NONE,
      const = fn (id, name, ty) =>
        cmd [(NS_TM,id)] [(NS_TY,ty)] CmdNormal 0x04 (SOME name),
      comb = fn (id, a, b) =>
        cmd [(NS_TM,id)] [(NS_TM,a),(NS_TM,b)] CmdNormal 0x05 NONE,
      abs = fn (id, a, b) =>
        cmd [(NS_TM,id)] [(NS_TM,a),(NS_TM,b)] CmdNormal 0x06 NONE,
      new_const = fn (name, ty) => let
        val ci = add_cmd fs {produced=[], consumed=[(NS_TY,ty)],
                             kind=CmdNewConst, opcode=0x07, ref_name=NONE}
        in add_const_introducer name ci end,
      new_type = fn (name, _) => let
        val ci = add_cmd fs {produced=[], consumed=[],
                             kind=CmdNewType, opcode=0x08, ref_name=NONE}
        in add_type_introducer name ci end,
      axiom = fn (id, tm, _) =>
        cmd [(NS_TH,id)] [(NS_TM,tm)] CmdAxiom 0x09 NONE,
      save = fn (name, th) =>
        let val ci = add_cmd fs {produced=[], consumed=[(NS_TH,th)],
                                 kind=CmdSave name, opcode=0x50,
                                 ref_name=NONE}
        in save_table :=
             Redblackmap.insert(!save_table, name,
               {file_idx=file_idx, cmd_idx=ci, th_id=th})
        end,
      load = fn (id, name) =>
        cmd [(NS_TH,id)] [] (CmdLoad name) 0x51 NONE,
      del = fn _ =>
        cmd [] [] CmdDel 0xE0 NONE,
      del_range = fn _ =>
        cmd [] [] CmdDel 0xF0 NONE,
      expect = fn _ => ()
    }
    val rh : PFTReader.ruleset_handler = fn opc => fn sr =>
      let
        val desc = lookup_desc (!descs_ref) opc
        val id = #readVarint sr ()
        val (consumed, {new_types, new_consts}) =
          collect_consumed sr (#args desc)
        val produced =
          #1 (foldl (fn (ns,(acc,n)) =>
                ((ns_idx ns, id+n)::acc, n+1))
              ([],0) (#results desc))
        val is_def = List.exists
          (fn (s: arg_spec) => case #role s of
                                 RNewType   => true
                               | RNewConst  => true
                               | RNewConsts => true
                               | RNormal    => false) (#args desc)
        val kind = if is_def then CmdDef else CmdNormal
        val ci = add_cmd fs {produced=rev produced, consumed=consumed,
                             kind=kind, opcode=opc, ref_name=NONE}
        val () = List.app (fn n => add_type_introducer n ci) new_types
        val () = List.app (fn n => add_const_introducer n ci) new_consts
      in () end
    val _ = PFTReader.read {file=file, binary=true,
                            format_handler=fh, ruleset_handler=rh}
  in fs end

(* ========================================================================= *)
(* Pass 1.5: Target resolution and reachability                              *)
(* ========================================================================= *)

fun resolve_targets (targets: target list)
                    (save_table: (string, save_entry) Redblackmap.dict)
    : (string * bool) list =
  let
    fun resolve (ThyThm(thy, name, sd)) =
        let val key = thy ^ "$" ^ name
        in case Redblackmap.peek(save_table, key) of
             SOME _ => [(key, sd)]
           | NONE => raise Fail ("PFTMerge: target not found: " ^ key)
        end
      | resolve (ThyAll(thy, sd)) =
        let val prefix = thy ^ "$"
            val plen = String.size prefix
            val matches = List.filter
              (fn (k, _) => String.size k >= plen andalso
                            String.substring(k, 0, plen) = prefix)
              (Redblackmap.listItems save_table)
        in if null matches
           then raise Fail ("PFTMerge: no exports for theory " ^ thy)
           else map (fn (k, _) => (k, sd)) matches
        end
  in List.concat (map resolve targets) end

(* DFS backward from targets to find all reachable commands. *)
fun compute_reachable
      (file_states: file_state vector)
      (save_table: (string, save_entry) Redblackmap.dict)
      (const_introducer: (string, int * int) Redblackmap.dict)
      (type_introducer: (string, int * int) Redblackmap.dict)
      (target_saves: (string * bool) list)
    : (int * int) list =
  let
    val n_files = Vector.length file_states
    val visited = Vector.tabulate(n_files, fn fi =>
      Array.array(DArray.size (#cmds (Vector.sub(file_states, fi))), false))
    val worklist = ref [] : (int * int) list ref

    fun enqueue (fi, ci) =
      let val vis = Vector.sub(visited, fi)
      in if Array.sub(vis, ci) then ()
         else (Array.update(vis, ci, true);
               worklist := (fi, ci) :: !worklist)
      end

    fun seed (name, _) =
      case Redblackmap.peek(save_table, name) of
        NONE => raise Fail ("PFTMerge: unknown target: " ^ name)
      | SOME {file_idx, cmd_idx, th_id} =>
        (enqueue (file_idx, cmd_idx);
         enqueue (file_idx,
                  find_producer (Vector.sub(file_states, file_idx))
                                (NS_TH, th_id)))
    val () = List.app seed target_saves

    fun process () =
      case !worklist of
        [] => ()
      | (fi, ci) :: rest =>
        let val () = worklist := rest
            val fs = Vector.sub(file_states, fi)
            val meta = DArray.sub(#cmds fs, ci)
        in
          (* Follow ID-level dependencies *)
          List.app (fn (ns, id) =>
            enqueue (fi, find_producer fs (ns, id)))
            (#consumed meta);
          (* Follow cross-file LOAD dependencies *)
          (case #kind meta of
             CmdLoad name =>
               (case Redblackmap.peek(save_table, name) of
                  NONE => raise Fail ("PFTMerge: unknown LOAD: " ^ name)
                | SOME {file_idx=sfi, cmd_idx=sci, th_id=sth} =>
                  let val sfs = Vector.sub(file_states, sfi)
                  in enqueue (sfi, sci);
                     enqueue (sfi, find_producer sfs (NS_TH, sth))
                  end)
           | _ => ());
          (* Follow name-level dependencies: CONST/TYOP → introducer *)
          (case #ref_name meta of
             SOME name =>
               let val table = if #opcode meta = 0x04
                               then const_introducer
                               else type_introducer
               in case Redblackmap.peek(table, name) of
                    SOME (ifi, ici) => enqueue (ifi, ici)
                  | NONE => () (* primitive — no introducer *)
               end
           | NONE => ());
          process ()
        end
    val () = process ()

    val result = ref [] : (int * int) list ref
    val () = Vector.appi (fn (fi, vis) =>
      Array.appi (fn (ci, v) =>
        if v then result := (fi, ci) :: !result else ()) vis)
      visited
  in List.rev (!result) end

(* ========================================================================= *)
(* Pass 2: Re-read and emit with renumbered IDs                              *)
(* ========================================================================= *)

fun pass2_emit (file_states: file_state vector)
               (save_table: (string, save_entry) Redblackmap.dict)
               (const_introducer: (string, int * int) Redblackmap.dict)
               (type_introducer: (string, int * int) Redblackmap.dict)
               (inputs: string list)
               (target_saves: (string * bool) list)
               (output: string)
               (version: int) (ruleset: string)
               (descs: (int * opcode_desc) list) =
  let
    val n_files = Vector.length file_states
    val incl_list = compute_reachable file_states save_table
                      const_introducer type_introducer target_saves

    (* Included set as bool arrays for O(1) lookup *)
    val included = Vector.tabulate(n_files, fn fi =>
      Array.array(DArray.size (#cmds (Vector.sub(file_states, fi))), false))
    val () = List.app (fn (fi, ci) =>
      Array.update(Vector.sub(included, fi), ci, true)) incl_list

    (* Per-namespace ID allocators *)
    val allocators = Vector.tabulate(NUM_NS, fn _ => IdAlloc.new ())
    fun alloc_id ns = IdAlloc.alloc (Vector.sub(allocators, ns))
    fun free_id ns id = IdAlloc.release (Vector.sub(allocators, ns)) id

    (* Renaming tables: per-file, per-namespace, old_id -> new_id *)
    val rename_tables =
      Vector.tabulate(n_files, fn fi =>
        let val fs = Vector.sub(file_states, fi)
            val maxes = Array.array(NUM_NS, 0)
            val () = DArray.appi (fn (_, meta) =>
              List.app (fn (ns, id) =>
                if id >= Array.sub(maxes, ns)
                then Array.update(maxes, ns, id + 1) else ())
                (#produced meta)) (#cmds fs)
        in Vector.tabulate(NUM_NS, fn ns =>
             Array.array(Array.sub(maxes, ns), NONE : int option))
        end)

    fun set_rename fi ns old_id new_id =
      Array.update(Vector.sub(Vector.sub(rename_tables, fi), ns),
                   old_id, SOME new_id)

    fun get_rename fi ns old_id =
      case Array.sub(Vector.sub(Vector.sub(rename_tables, fi), ns),
                     old_id) of
        SOME nid => nid
      | NONE => raise Fail ("PFTMerge: unmapped " ^ ns_name ns ^ "#" ^
                             Int.toString old_id ^ " in file " ^
                             Int.toString fi)

    fun lookup_save name =
      case Redblackmap.peek(save_table, name) of
        SOME e => e
      | NONE => raise Fail ("PFTMerge: unknown SAVE: " ^ name)

    (* Step 1: Allocate new IDs for all included commands *)
    val () = Vector.appi (fn (fi, fs) =>
      let val vis = Vector.sub(included, fi)
          val n = DArray.size (#cmds fs)
          fun go ci = if ci >= n then () else
            (if Array.sub(vis, ci) then
               let val meta = DArray.sub(#cmds fs, ci)
               in case #kind meta of
                    CmdLoad name =>
                      let val {file_idx=sfi, th_id=sth, ...} = lookup_save name
                      in List.app (fn (ns, id) =>
                           set_rename fi ns id (get_rename sfi NS_TH sth))
                           (#produced meta)
                      end
                  | CmdSave _ => ()
                  | CmdDel => ()
                  | _ =>
                      let val produced = #produced meta
                          val n_produced = length produced
                      in if n_produced > 1 andalso
                            List.all (fn (ns,_) => ns = #1 (hd produced))
                                     produced
                         then (* consecutive allocation required *)
                           let val ns = #1 (hd produced)
                               val base = IdAlloc.alloc_consecutive
                                            (Vector.sub(allocators, ns))
                                            n_produced
                           in List.foldl (fn ((ns, id), i) =>
                                (set_rename fi ns id (base + i); i + 1))
                              0 produced; ()
                           end
                         else
                           List.app (fn (ns, id) =>
                             set_rename fi ns id (alloc_id ns))
                             produced
                      end
               end
             else ();
             go (ci + 1))
      in go 0 end
    ) file_states

    (* Collect definition SAVEs early (before refcount computation) *)
    val def_saves =
      if not (List.exists #2 target_saves) then []
      else let val acc = ref [] : (string * int) list ref
      in Vector.appi (fn (fi, fs) =>
           let val vis = Vector.sub(included, fi)
           in DArray.appi (fn (ci, meta) =>
                if Array.sub(vis, ci) then
                  case #kind meta of
                    CmdDef =>
                      List.app (fn (ns, id) =>
                        if ns = NS_TH then
                          let val nid = get_rename fi ns id
                          in acc := ("def:" ^ Int.toString nid, nid) :: !acc
                          end
                        else ()) (#produced meta)
                  | _ => ()
                else ()) (#cmds fs)
           end) file_states;
         List.rev (!acc)
      end

    (* Step 2: Compute refcounts for DEL insertion *)
    val refcounts = Vector.tabulate(NUM_NS, fn ns =>
      Array.array(IdAlloc.peakCount (Vector.sub(allocators, ns)), 0))

    fun inc_ref ns nid =
      let val a = Vector.sub(refcounts, ns)
      in Array.update(a, nid, Array.sub(a, nid) + 1) end

    fun count_consumed fi meta =
      case #kind meta of
        CmdDel => ()
      | CmdSave _ => ()
      | CmdLoad name =>
          inc_ref NS_TH (get_rename (#file_idx (lookup_save name))
                                    NS_TH (#th_id (lookup_save name)))
      | _ =>
          List.app (fn (ns, id) =>
            inc_ref ns (get_rename fi ns id)) (#consumed meta)

    val () = Vector.appi (fn (fi, fs) =>
      let val vis = Vector.sub(included, fi)
      in DArray.appi (fn (ci, meta) =>
           if Array.sub(vis, ci) then count_consumed fi meta else ())
           (#cmds fs)
      end) file_states

    (* Refcounts for target SAVEs *)
    val () = List.app (fn (name, _) =>
      let val {file_idx, th_id, ...} = lookup_save name
      in inc_ref NS_TH (get_rename file_idx NS_TH th_id) end)
      target_saves

    (* Refcounts for definition SAVEs *)
    val () = List.app (fn (_, nid) => inc_ref NS_TH nid) def_saves

    (* Step 3: Emit *)
    val out = PFTWriter.openOut {file=output, binary=true,
                                 version=version, ruleset=ruleset}

    fun dec_ref ns nid =
      let val a = Vector.sub(refcounts, ns)
          val rc = Array.sub(a, nid) - 1
      in Array.update(a, nid, rc);
         if rc = 0 then (PFTWriter.del out (ns_name ns) nid; free_id ns nid)
         else ()
      end

    val current_fi = ref 0

    fun is_included ci = Array.sub(Vector.sub(included, !current_fi), ci)
    fun ren ns id = get_rename (!current_fi) ns id

    fun dec_consumed meta =
      case #kind meta of
        CmdDel => ()
      | CmdSave _ => ()
      | CmdLoad name =>
          let val {file_idx=sfi, th_id=sth, ...} = lookup_save name
          in dec_ref NS_TH (get_rename sfi NS_TH sth) end
      | _ =>
          List.app (fn (ns, id) => dec_ref ns (ren ns id)) (#consumed meta)

    (* Handlers for pass 2 re-read. Format and ruleset handlers share
       a command counter so they stay synchronised with pass 1 metadata. *)
    fun make_handlers () =
      let
        val ci_ref = ref 0
        fun next_ci () = let val c = !ci_ref in ci_ref := c + 1; c end

        fun when_included ci f =
          if is_included ci then
            let val meta = DArray.sub(#cmds (Vector.sub(file_states,
                                                        !current_fi)), ci)
            in f meta; dec_consumed meta end
          else ()

        val fh : PFTReader.format_handler = {
          tyvar = fn (id, name) =>
            when_included (next_ci ()) (fn _ =>
              PFTWriter.tyvar out (ren NS_TY id) name),
          tyop = fn (id, name, args) =>
            when_included (next_ci ()) (fn _ =>
              PFTWriter.tyop out (ren NS_TY id) name
                (map (ren NS_TY) args)),
          var = fn (id, name, ty) =>
            when_included (next_ci ()) (fn _ =>
              PFTWriter.var out (ren NS_TM id) name (ren NS_TY ty)),
          const = fn (id, name, ty) =>
            when_included (next_ci ()) (fn _ =>
              PFTWriter.const out (ren NS_TM id) name (ren NS_TY ty)),
          comb = fn (id, a, b) =>
            when_included (next_ci ()) (fn _ =>
              PFTWriter.comb out (ren NS_TM id) (ren NS_TM a) (ren NS_TM b)),
          abs = fn (id, a, b) =>
            when_included (next_ci ()) (fn _ =>
              PFTWriter.abs out (ren NS_TM id) (ren NS_TM a) (ren NS_TM b)),
          new_const = fn (name, ty) =>
            when_included (next_ci ()) (fn _ =>
              PFTWriter.new_const out name (ren NS_TY ty)),
          new_type = fn (name, arity) =>
            when_included (next_ci ()) (fn _ =>
              PFTWriter.new_type out name arity),
          axiom = fn (id, tm, nameOpt) =>
            when_included (next_ci ()) (fn _ =>
              PFTWriter.axiom out (ren NS_TH id) (ren NS_TM tm) nameOpt),
          save = fn _ => ignore (next_ci ()),
          load = fn _ =>
            let val ci = next_ci ()
            in if is_included ci then
                 dec_consumed (DArray.sub(#cmds (Vector.sub(file_states,
                                                           !current_fi)), ci))
               else () end,
          del = fn _ => ignore (next_ci ()),
          del_range = fn _ => ignore (next_ci ()),
          expect = fn _ => ()
        }

        (* Emit a HOL4 ruleset command with renumbered IDs *)
        fun emit_hol4 opc id (sr: PFTReader.stream_reader) =
          let val vi = #readVarint sr val vs = #readString sr
              fun rTy x = ren NS_TY x fun rTm x = ren NS_TM x
              fun rTh x = ren NS_TH x fun rCi x = ren NS_CI x
              val nid = if opc = 0x43 then 0 (* dummy: unused by COMPUTE_INIT *)
                        else rTh id
          in case opc of
              0x10 => PFTWriter.HOL4.refl out nid (rTm(vi()))
            | 0x11 => let val a = rTm(vi())
                      in PFTWriter.HOL4.alpha out nid a (rTm(vi())) end
            | 0x12 => PFTWriter.HOL4.assume out nid (rTm(vi()))
            | 0x13 => PFTWriter.HOL4.beta_conv out nid (rTm(vi()))
            | 0x14 => let val a = rTh(vi())
                      in PFTWriter.HOL4.eq_mp out nid a (rTh(vi())) end
            | 0x15 => let val a = rTh(vi())
                      in PFTWriter.HOL4.mp out nid a (rTh(vi())) end
            | 0x16 => PFTWriter.HOL4.sym out nid (rTh(vi()))
            | 0x17 => let val a = rTh(vi())
                      in PFTWriter.HOL4.trans out nid a (rTh(vi())) end
            | 0x18 => let val a = rTh(vi())
                      in PFTWriter.HOL4.conj out nid a (rTh(vi())) end
            | 0x19 => PFTWriter.HOL4.conjunct1 out nid (rTh(vi()))
            | 0x1A => PFTWriter.HOL4.conjunct2 out nid (rTh(vi()))
            | 0x1B => let val a = rTm(vi())
                      in PFTWriter.HOL4.disch out nid a (rTh(vi())) end
            | 0x1C => let val a = rTh(vi())
                      in PFTWriter.HOL4.disj1 out nid a (rTm(vi())) end
            | 0x1D => let val a = rTm(vi())
                      in PFTWriter.HOL4.disj2 out nid a (rTh(vi())) end
            | 0x1E => let val a = rTh(vi()) val b = rTh(vi())
                      in PFTWriter.HOL4.disj_cases out nid a b (rTh(vi())) end
            | 0x1F => PFTWriter.HOL4.not_elim out nid (rTh(vi()))
            | 0x20 => PFTWriter.HOL4.not_intro out nid (rTh(vi()))
            | 0x21 => let val a = rTm(vi())
                      in PFTWriter.HOL4.ccontr out nid a (rTh(vi())) end
            | 0x22 => let val a = rTm(vi()) val b = rTm(vi())
                      in PFTWriter.HOL4.exists out nid a b (rTh(vi())) end
            | 0x23 => let val a = rTm(vi()) val b = rTh(vi())
                      in PFTWriter.HOL4.choose out nid a b (rTh(vi())) end
            | 0x24 => let val a = rTm(vi())
                      in PFTWriter.HOL4.gen out nid a (rTh(vi())) end
            | 0x25 => let val a = rTm(vi())
                      in PFTWriter.HOL4.spec out nid a (rTh(vi())) end
            | 0x26 => let val a = rTm(vi())
                      in PFTWriter.HOL4.specialize out nid a (rTh(vi())) end
            | 0x27 => let val th = rTh(vi())
                      in PFTWriter.HOL4.genl out nid th
                           (map rTm (#readVarintList sr ())) end
            | 0x28 => let val th = rTh(vi())
                      in PFTWriter.HOL4.absl out nid th
                           (map rTm (#readVarintList sr ())) end
            | 0x29 => let val th = rTh(vi()) val c = rTm(vi())
                      in PFTWriter.HOL4.gen_abs out nid th c
                           (map rTm (#readVarintList sr ())) end
            | 0x30 => let val a = rTm(vi())
                      in PFTWriter.HOL4.abs_thm out nid a (rTh(vi())) end
            | 0x31 => let val a = rTm(vi())
                      in PFTWriter.HOL4.ap_term out nid a (rTh(vi())) end
            | 0x32 => let val a = rTh(vi())
                      in PFTWriter.HOL4.ap_thm out nid a (rTm(vi())) end
            | 0x33 => let val a = rTh(vi())
                      in PFTWriter.HOL4.mk_comb out nid a (rTh(vi())) end
            | 0x34 => PFTWriter.HOL4.beta_thm out nid (rTh(vi()))
            | 0x35 => let val a = rTh(vi())
                      in PFTWriter.HOL4.mk_abs_thm out nid a (rTh(vi())) end
            | 0x36 => let val a = rTh(vi()) val b = rTh(vi())
                      in PFTWriter.HOL4.mk_comb_thm out nid a b (rTh(vi())) end
            | 0x37 => PFTWriter.HOL4.eq_imp_rule1 out nid (rTh(vi()))
            | 0x38 => PFTWriter.HOL4.eq_imp_rule2 out nid (rTh(vi()))
            | 0x39 => let val th = rTh(vi())
                      in PFTWriter.HOL4.inst out nid th
                           (map (fn (a,b) => (rTm a, rTm b))
                                (#readVarintPairs sr ())) end
            | 0x3A => let val th = rTh(vi())
                      in PFTWriter.HOL4.inst_type out nid th
                           (map (fn (a,b) => (rTy a, rTy b))
                                (#readVarintPairs sr ())) end
            | 0x3B => let val t = rTm(vi()) val th = rTh(vi())
                      in PFTWriter.HOL4.subst out nid t th
                           (map (fn (a,b) => (rTm a, rTh b))
                                (#readVarintPairs sr ())) end
            | 0x3C => let val a = rTh(vi())
                      in PFTWriter.HOL4.deductAntisym out nid a (rTh(vi())) end
            | 0x40 => let val th = rTh(vi())
                      in PFTWriter.HOL4.def_tyop out nid th (vs()) end
            | 0x41 => let val th = rTh(vi())
                      in PFTWriter.HOL4.def_spec out nid th
                           (#readStringList sr ()) end
            | 0x42 => let val th = rTh(vi())
                      in PFTWriter.HOL4.def_spec_gen out nid th
                           (#readStringList sr ()) end
            | 0x43 => let val nci = rCi id
                          val ty1 = rTy(vi()) val ty2 = rTy(vi())
                          val eqns = map (fn (s,t) => (s, rTh t))
                                       (#readStringVarintPairs sr ())
                          val terms = map (fn (s,t) => (s, rTm t))
                                       (#readStringVarintPairs sr ())
                      in PFTWriter.HOL4.compute_init out nci ty1 ty2
                           eqns terms end
            | 0x44 => let val ci = rCi(vi()) val tm = rTm(vi())
                      in PFTWriter.HOL4.compute out nid ci tm
                           (map rTh (#readVarintList sr ())) end
            | _ => raise Fail ("PFTMerge: unknown HOL4 opcode 0x" ^
                               Int.fmt StringCvt.HEX opc)
          end

        (* Emit a Candle ruleset command with renumbered IDs *)
        fun emit_candle opc id (sr: PFTReader.stream_reader) =
          let val vi = #readVarint sr val vs = #readString sr
              fun rTy x = ren NS_TY x fun rTm x = ren NS_TM x
              fun rTh x = ren NS_TH x fun rCi x = ren NS_CI x
              val nid = if opc = 0x40 then 0 (* dummy: unused by COMPUTE_INIT *)
                        else rTh id
          in case opc of
              0x10 => PFTWriter.Candle.refl out nid (rTm(vi()))
            | 0x11 => let val a = rTh(vi())
                      in PFTWriter.Candle.trans out nid a (rTh(vi())) end
            | 0x12 => let val a = rTh(vi())
                      in PFTWriter.Candle.mk_comb out nid a (rTh(vi())) end
            | 0x13 => let val a = rTm(vi())
                      in PFTWriter.Candle.abs_thm out nid a (rTh(vi())) end
            | 0x14 => PFTWriter.Candle.beta out nid (rTm(vi()))
            | 0x15 => PFTWriter.Candle.assume out nid (rTm(vi()))
            | 0x16 => let val a = rTh(vi())
                      in PFTWriter.Candle.eq_mp out nid a (rTh(vi())) end
            | 0x17 => let val a = rTh(vi())
                      in PFTWriter.Candle.deduct_antisym_rule out nid a
                           (rTh(vi())) end
            | 0x18 => let val th = rTh(vi())
                      in PFTWriter.Candle.inst out nid th
                           (map (fn (a,b) => (rTm a, rTm b))
                                (#readVarintPairs sr ())) end
            | 0x19 => let val th = rTh(vi())
                      in PFTWriter.Candle.inst_type out nid th
                           (map (fn (a,b) => (rTy a, rTy b))
                                (#readVarintPairs sr ())) end
            | 0x20 => PFTWriter.Candle.sym out nid (rTh(vi()))
            | 0x21 => let val a = rTh(vi())
                      in PFTWriter.Candle.prove_hyp out nid a (rTh(vi())) end
            | 0x30 => let val th = rTh(vi())
                      in PFTWriter.Candle.new_specification out nid th
                           (#readStringList sr ()) end
            | 0x31 => let val th = rTh(vi())
                          val tyname = vs() val absname = vs()
                      in PFTWriter.Candle.new_type_definition out nid th
                           tyname absname (vs()) end
            | 0x40 => PFTWriter.Candle.compute_init out (rCi id)
                        (map rTh (#readVarintList sr ()))
            | 0x41 => let val ci = rCi(vi()) val tm = rTm(vi())
                      in PFTWriter.Candle.compute out nid ci tm
                           (map rTh (#readVarintList sr ())) end
            | _ => raise Fail ("PFTMerge: unknown Candle opcode 0x" ^
                               Int.fmt StringCvt.HEX opc)
          end

        val is_hol4 = (ruleset = "hol4")

        val rh : PFTReader.ruleset_handler = fn opc => fn sr =>
          let val ci = next_ci ()
          in if is_included ci then
               let val id = #readVarint sr ()
                   val meta = DArray.sub(#cmds (Vector.sub(file_states,
                                                           !current_fi)), ci)
               in (if is_hol4 then emit_hol4 else emit_candle) opc id sr;
                  dec_consumed meta
               end
             else
               let val _ = #readVarint sr ()
               in ignore (#1 (collect_consumed sr (#args (lookup_desc descs opc))))
               end
          end

        fun reset () = ci_ref := 0
      in (fh, rh, reset) end

    val (fh, rh, reset_ci) = make_handlers ()

    (* Process each input file *)
    val () = ignore (List.foldl (fn (file, fi) =>
      (current_fi := fi; reset_ci ();
       ignore (PFTReader.read {file=file, binary=true,
                               format_handler=fh, ruleset_handler=rh});
       fi + 1)) 0 inputs)

    (* Emit target SAVEs *)
    val () = List.app (fn (name, _) =>
      let val {file_idx, th_id, ...} = lookup_save name
          val nid = get_rename file_idx NS_TH th_id
      in PFTWriter.save out name nid; dec_ref NS_TH nid end)
      target_saves

    (* Emit definition SAVEs *)
    val () = List.app (fn (name, nid) =>
      (PFTWriter.save out name nid; dec_ref NS_TH nid)) def_saves

    (* Footer *)
    val () = PFTWriter.closeOut out {
      n_ty = IdAlloc.peakCount (Vector.sub(allocators, NS_TY)),
      n_tm = IdAlloc.peakCount (Vector.sub(allocators, NS_TM)),
      n_th = IdAlloc.peakCount (Vector.sub(allocators, NS_TH)),
      n_ci = IdAlloc.peakCount (Vector.sub(allocators, NS_CI))}
  in () end

(* ========================================================================= *)
(* Main entry point                                                          *)
(* ========================================================================= *)

fun merge {inputs, targets, output, binary} =
  let
    val () = if not binary
             then raise Fail "PFTMerge: only binary mode is supported"
             else ()
    val () = if null inputs
             then raise Fail "PFTMerge: no input files"
             else ()

    val {version = the_version, ruleset = the_ruleset} =
      PFTReader.read_header {file = hd inputs, binary = true}
    val descs_ref = ref (if the_ruleset = "candle" then candle_descs
                         else hol4_descs)
    val save_table = ref (Redblackmap.mkDict String.compare)
    val const_introducer = ref (Redblackmap.mkDict String.compare)
    val type_introducer = ref (Redblackmap.mkDict String.compare)

    (* Pass 1: read all files, build dependency graph *)
    val file_states = Vector.fromList
      (List.tabulate(length inputs, fn fi =>
         pass1_read_file descs_ref fi (List.nth(inputs, fi)) save_table
           const_introducer type_introducer))

    (* Pass 1.5: resolve targets *)
    val target_saves = resolve_targets targets (!save_table)

    (* Pass 2: re-read and emit *)
    val () = pass2_emit file_states (!save_table)
               (!const_introducer) (!type_introducer)
               inputs target_saves
               output the_version the_ruleset (!descs_ref)
  in () end

end
