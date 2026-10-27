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
  type t = int ref

  fun new () : t = ref 0

  fun alloc_consecutive (next: t) n =
    let val id = !next
    in next := id + n; id end

  fun alloc next = alloc_consecutive next 1

  fun peakCount (next: t) = !next
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
  producers : (int * int, int) Redblackmap.dict ref
}

fun pair_compare ((a1:int,b1:int), (a2,b2)) =
  case Int.compare(a1,a2) of EQUAL => Int.compare(b1,b2) | ord => ord

fun new_file_state fi : file_state = {
  file_idx = fi,
  cmds = DArray.new(1024, empty_meta),
  producers = ref (Redblackmap.mkDict pair_compare)
}

fun record_producers file_idx producers ci (meta: cmd_meta) =
  let
    fun check_input (ns, id) =
      if isSome (Redblackmap.peek (!producers, (ns, id))) then ()
      else raise Fail ("PFTMerge: missing or forward reference to " ^
                       ns_name ns ^ "#" ^ Int.toString id ^ " in file " ^
                       Int.toString file_idx)
    fun add_output (ns, id) =
      if isSome (Redblackmap.peek (!producers, (ns, id))) then
        raise Fail ("PFTMerge: reused input ID " ^ ns_name ns ^ "#" ^
                    Int.toString id ^ " in file " ^
                    Int.toString file_idx)
      else producers := Redblackmap.insert(!producers, (ns, id), ci)
  in List.app check_input (#consumed meta);
     List.app add_output (#produced meta)
  end

fun add_cmd (fs: file_state) (meta: cmd_meta) =
  let val ci = DArray.size (#cmds fs)
      val () = record_producers (#file_idx fs) (#producers fs) ci meta
  in DArray.push(#cmds fs, meta); ci end

fun find_producer (fs: file_state) (ns, id) =
  Redblackmap.find(!(#producers fs), (ns, id))
  handle Redblackmap.NotFound =>
    raise Fail ("PFTMerge: no producer for " ^ ns_name ns ^ "#" ^
                Int.toString id ^ " in file " ^ Int.toString (#file_idx fs))

type save_entry = {file_idx: int, cmd_idx: int, th_id: int}

(* Both scans use the same command numbering and descriptor decoding. *)
fun read_commands (descs_ref: (int * opcode_desc) list ref) file add
                  {save, new_const, new_type} =
  let
    fun cmd p c k o' rn = ignore (add {produced=p, consumed=c,
                                     kind=k, opcode=o', ref_name=rn})
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
        val ci = add {produced=[], consumed=[(NS_TY,ty)],
                             kind=CmdNewConst, opcode=0x07, ref_name=NONE}
        in new_const (name, ci) end,
      new_type = fn (name, _) => let
        val ci = add {produced=[], consumed=[],
                             kind=CmdNewType, opcode=0x08, ref_name=NONE}
        in new_type (name, ci) end,
      axiom = fn (id, tm, _) =>
        cmd [(NS_TH,id)] [(NS_TM,tm)] CmdAxiom 0x09 NONE,
      save = fn (name, th) =>
        let val ci = add {produced=[], consumed=[(NS_TH,th)],
                                 kind=CmdSave name, opcode=0x50,
                                 ref_name=NONE}
        in save (name, th, ci) end,
      load = fn (id, name) =>
        cmd [(NS_TH,id)] [] (CmdLoad name) 0x51 NONE,
      del = fn _ =>
        cmd [] [] CmdDel 0xE0 NONE,
      del_range = fn _ =>
        cmd [] [] CmdDel 0xF0 NONE
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
        val ci = add {produced=rev produced, consumed=consumed,
                             kind=kind, opcode=opc, ref_name=NONE}
        val () = List.app (fn n => new_type (n, ci)) new_types
        val () = List.app (fn n => new_const (n, ci)) new_consts
      in () end
  in ignore (PFTReader.read {file=file, binary=true,
                             format_handler=fh, ruleset_handler=rh}) end

fun pass1_read_file descs_ref file_idx file =
  let val fs = new_file_state file_idx
      val () = read_commands descs_ref file (add_cmd fs)
        {save=fn _ => (), new_const=fn _ => (), new_type=fn _ => ()}
  in fs end

fun scan_index_file descs_ref file_idx file
                    (save_table: (string, save_entry) Redblackmap.dict ref)
                    const_introducer type_introducer =
  let
    val ci_ref = ref 0
    (* Validate even unselected files without retaining command metadata. *)
    val producers = ref (Redblackmap.mkDict pair_compare)
    fun add meta =
      let val ci = !ci_ref
          val () = record_producers file_idx producers ci meta
      in ci_ref := ci + 1; ci end
    fun save (name, th, ci) =
      if isSome (Redblackmap.peek (!save_table, name)) then
        raise Fail ("PFTMerge: duplicate SAVE: " ^ name)
      else save_table := Redblackmap.insert(!save_table, name,
        {file_idx=file_idx, cmd_idx=ci, th_id=th})
    fun introduce table (name, ci) =
      table := Redblackmap.insert(!table, name, (file_idx, ci))
  in read_commands descs_ref file add
       {save=save, new_const=introduce const_introducer,
        new_type=introduce type_introducer}
  end

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
      n_files (ensure_file_state: int -> file_state)
      (save_table: (string, save_entry) Redblackmap.dict)
      (const_introducer: (string, int * int) Redblackmap.dict)
      (type_introducer: (string, int * int) Redblackmap.dict)
      (target_saves: (string * bool) list)
    : bool array option ref vector =
  let
    val visited = Vector.tabulate(n_files,
      fn _ => ref NONE : bool array option ref)
    fun ensure_visited fi =
      case !(Vector.sub(visited, fi)) of
        SOME a => a
      | NONE => let val fs = ensure_file_state fi
                    val a = Array.array(DArray.size (#cmds fs), false)
                in Vector.sub(visited, fi) := SOME a; a end
    val worklist = ref [] : (int * int) list ref

    fun enqueue (fi, ci) =
      let val vis = ensure_visited fi
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
                  find_producer (ensure_file_state file_idx)
                                (NS_TH, th_id)))
    val () = List.app seed target_saves

    fun process () =
      case !worklist of
        [] => ()
      | (fi, ci) :: rest =>
        let val () = worklist := rest
            val fs = ensure_file_state fi
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
                  let val sfs = ensure_file_state sfi
                      val () = if sfi < fi orelse
                                  (sfi = fi andalso sci < ci) then ()
                               else raise Fail
                                 ("PFTMerge: LOAD before SAVE: " ^ name ^
                                  "; inputs must be in dependency order")
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
                    SOME (ifi, ici) =>
                      if ifi < fi orelse (ifi = fi andalso ici <= ci) then
                        enqueue (ifi, ici)
                      else raise Fail
                        ("PFTMerge: name used before introduction: " ^ name ^
                         "; inputs must be in dependency order")
                  | NONE => () (* primitive — no introducer *)
               end
           | NONE => ());
          process ()
        end
    val () = process ()

  in visited end

(* ========================================================================= *)
(* Pass 2: Re-read and emit with renumbered IDs                              *)
(* ========================================================================= *)

fun pass2_emit (file_states: file_state option ref vector)
               (ensure_file_state: int -> file_state)
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
    val included = compute_reachable n_files ensure_file_state save_table
                     const_introducer type_introducer target_saves
    fun app_included f =
      Vector.appi (fn (fi, fs_ref) =>
        case (!(Vector.sub(included, fi)), !fs_ref) of
          (SOME vis, SOME fs) => f (fi, fs, vis)
        | _ => ()) file_states
    fun loaded_file fi =
      case !(Vector.sub(file_states, fi)) of
        SOME fs => fs
      | NONE => raise Fail "PFTMerge: pass2 on unloaded file"

    (* Per-namespace ID allocators *)
    val allocators = Vector.tabulate(NUM_NS, fn _ => IdAlloc.new ())
    fun alloc_id ns = IdAlloc.alloc (Vector.sub(allocators, ns))

    (* Renaming tables: per-file, per-namespace, old_id -> new_id *)
    val rename_tables =
      Vector.tabulate(n_files, fn fi =>
        case !(Vector.sub(file_states, fi)) of
          NONE => Vector.tabulate(NUM_NS,
                    fn _ => Array.array(0, NONE : int option))
        | SOME fs =>
        let val maxes = Array.array(NUM_NS, 0)
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
    val () = app_included (fn (fi, fs, vis) =>
      let val n = DArray.size (#cmds fs)
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
    )

    (* Collect definition SAVEs early (before refcount computation) *)
    val def_saves =
      if not (List.exists #2 target_saves) then []
      else let val acc = ref [] : (string * int) list ref
      in app_included (fn (fi, fs, vis) =>
             DArray.appi (fn (ci, meta) =>
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
                else ()) (#cmds fs));
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

    val () = app_included (fn (fi, fs, vis) =>
          DArray.appi (fn (ci, meta) =>
           if Array.sub(vis, ci) then count_consumed fi meta else ())
           (#cmds fs))

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
         if rc = 0 then PFTWriter.del out (ns_name ns) nid
         else ()
      end

    val current_fi = ref 0

    fun is_included ci =
      case !(Vector.sub(included, !current_fi)) of
        SOME vis => Array.sub(vis, ci)
      | NONE => false
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
            let val meta = DArray.sub(#cmds (loaded_file (!current_fi)), ci)
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
                 dec_consumed
                   (DArray.sub(#cmds (loaded_file (!current_fi)), ci))
               else () end,
          del = fn _ => ignore (next_ci ()),
          del_range = fn _ => ignore (next_ci ())
        }

        fun rename_arg ({shape, ...}: arg_spec, arg) =
          let fun r ns id = ren (ns_idx ns) id
          in case (shape, arg) of
               (AId ns, VId id) => VId (r ns id)
             | (AIdList ns, VIdList ids) => VIdList (map (r ns) ids)
             | (AIdPairs (a,b), VIdPairs ids) =>
                 VIdPairs (map (fn (x,y) => (r a x, r b y)) ids)
             | (AStrIdPairs ns, VStrIdPairs ids) =>
                 VStrIdPairs (map (fn (name,id) => (name, r ns id)) ids)
             | _ => arg
          end

        val rh : PFTReader.ruleset_handler = fn opc => fn sr =>
          let
            val ci = next_ci ()
            val desc = lookup_desc descs opc
            val id = #readVarint sr ()
            val args = PFTReader.read_raw_args desc sr
          in if is_included ci then
               let
                 val meta = DArray.sub
                   (#cmds (loaded_file (!current_fi)), ci)
                 val result = ren (ns_idx (hd (#results desc))) id
                 val args = ListPair.map rename_arg (#args desc, args)
               in PFTWriter.write_raw out
                    {opcode=opc, desc=desc, result=result, args=args};
                  dec_consumed meta
               end
             else ()
          end

        fun reset () = ci_ref := 0
      in (fh, rh, reset) end

    val (fh, rh, reset_ci) = make_handlers ()

    (* Process each input file *)
    val () = ignore (List.foldl (fn (file, fi) =>
      ((case !(Vector.sub(file_states, fi)) of
          NONE => ()
        | SOME _ =>
            (current_fi := fi; reset_ci ();
             ignore (PFTReader.read {file=file, binary=true,
                                    format_handler=fh, ruleset_handler=rh})));
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

    val () = if null targets then raise Fail "PFTMerge: no targets" else ()
    val () = if List.exists
                  (fn file => OS.Path.mkAbsolute
                    {path=file, relativeTo=OS.FileSys.getDir ()} =
                    OS.Path.mkAbsolute
                    {path=output, relativeTo=OS.FileSys.getDir ()}) inputs
             then raise Fail "PFTMerge: output is an input file" else ()

    val {version = the_version, ruleset = the_ruleset} =
      PFTReader.read_header {file = hd inputs, binary = true}
    val () = List.app (fn file =>
      let val {version, ruleset} =
            PFTReader.read_header {file=file, binary=true}
      in if version <> 1 then
           raise Fail ("PFTMerge: unsupported version " ^
                       Int.toString version ^ " in " ^ file ^ "; expected 1")
         else if ruleset <> the_ruleset then
           raise Fail ("PFTMerge: ruleset " ^ ruleset ^ " in " ^ file ^
                       "; expected " ^ the_ruleset)
         else ()
      end) inputs
    val descs_ref = ref (descs_for_ruleset the_ruleset)
    val save_table = ref (Redblackmap.mkDict String.compare)
    val const_introducer = ref (Redblackmap.mkDict String.compare)
    val type_introducer = ref (Redblackmap.mkDict String.compare)

    (* Index global names, retaining full metadata only for reached files. *)
    val () = ignore (List.foldl (fn (file, fi) =>
      (scan_index_file descs_ref fi file save_table
         const_introducer type_introducer;
       fi + 1)) 0 inputs)
    val file_states : file_state option ref vector =
      Vector.tabulate(length inputs, fn _ => ref NONE)
    fun ensure_file_state fi =
      case !(Vector.sub(file_states, fi)) of
        SOME fs => fs
      | NONE => let val fs = pass1_read_file descs_ref fi (List.nth(inputs, fi))
                in Vector.sub(file_states, fi) := SOME fs; fs end

    (* Pass 1.5: resolve targets *)
    val target_saves = resolve_targets targets (!save_table)

    (* Pass 2: re-read and emit *)
    val () = pass2_emit file_states ensure_file_state (!save_table)
               (!const_introducer) (!type_introducer)
               inputs target_saves
               output the_version the_ruleset (!descs_ref)
  in () end

end
