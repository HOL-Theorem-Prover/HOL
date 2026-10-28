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
  type t = {next: int ref, free: (int, unit) Redblackmap.dict ref}

  fun new () : t = {next=ref 0, free=ref (Redblackmap.mkDict Int.compare)}

  fun fresh ({next, ...}: t) n =
    let val id = !next
    in next := id + n; id end

  fun alloc (a as {free, ...}: t) =
    case Redblackmap.firsti (!free) of
      SOME (id, _) => (free := #1 (Redblackmap.remove(!free, id)); id)
    | NONE => fresh a 1

  fun release ({free, ...}: t) id =
    free := Redblackmap.insert(!free, id, ())

  fun alloc_consecutive (a as {free, ...}: t) n =
    let
      fun block [] _ _ = NONE
        | block (id::ids) start count =
            let val (start, count) =
                  if id = start + count then (start, count + 1)
                  else (id, 1)
            in if count = n then SOME start else block ids start count end
    in case block (Redblackmap.listKeys (!free)) 0 0 of
         NONE => fresh a n
       | SOME base =>
           (List.app (fn i =>
              free := #1 (Redblackmap.remove(!free, base + i)))
              (List.tabulate(n, fn i => i));
            base)
    end

  fun peakCount ({next, ...}: t) = !next
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

(* Only the descriptor decoder builds lists. Retained metadata uses flat
   slices, with full-width IDs/offsets and bytes only for small enum fields. *)
structure Metadata = struct
  type t = {
    kinds: DString.dstring, opcodes: DString.dstring,
    prod_start: int DArray.darray, cons_start: int DArray.darray,
    prod_ns: DString.dstring, prod_id: int DArray.darray,
    cons_ns: DString.dstring, cons_id: int DArray.darray,
    name_idx: int DArray.darray, names: string DArray.darray
  }

  fun new () : t =
    let val ps = DArray.new(1024, 0)
        val cs = DArray.new(1024, 0)
    in DArray.push(ps, 0); DArray.push(cs, 0);
       {kinds=DString.new 1024, opcodes=DString.new 1024,
        prod_start=ps, cons_start=cs,
        prod_ns=DString.new 1024, prod_id=DArray.new(1024, 0),
        cons_ns=DString.new 1024, cons_id=DArray.new(1024, 0),
        name_idx=DArray.new(1024, ~1), names=DArray.new(16, "")}
    end

  fun size ({kinds, ...}: t) = DString.size kinds
  fun opcode ({opcodes, ...}: t) ci = Char.ord (DString.sub(opcodes, ci))
  fun name ({name_idx, names, ...}: t) ci =
    DArray.sub(names, DArray.sub(name_idx, ci))
  fun kind (m as {kinds, ...}: t) ci =
    case Char.ord (DString.sub(kinds, ci)) of
      0 => CmdNormal
    | 1 => CmdSave "" (* The global SAVE index owns export names. *)
    | 2 => CmdLoad (name m ci)
    | 3 => CmdDel
    | 4 => CmdDef
    | 5 => CmdNewConst
    | 6 => CmdNewType
    | _ => CmdAxiom
  fun ref_name (m: t) ci =
    if opcode m ci = 0x02 orelse opcode m ci = 0x04
    then SOME (name m ci) else NONE

  fun push (m: t) (meta: cmd_meta) =
    let
      val (k, n) = case #kind meta of
          CmdNormal => (0, #ref_name meta)
        | CmdSave _ => (1, NONE)
        | CmdLoad name => (2, SOME name)
        | CmdDel => (3, NONE)
        | CmdDef => (4, NONE)
        | CmdNewConst => (5, NONE)
        | CmdNewType => (6, NONE)
        | CmdAxiom => (7, NONE)
      fun edges nsbuf ids pairs = List.app (fn (ns, id) =>
        (DString.push(nsbuf, Char.chr ns); DArray.push(ids, id))) pairs
      val ni = case n of NONE => ~1 | SOME name =>
        let val i = DArray.size (#names m)
        in DArray.push(#names m, name); i end
    in DString.push(#kinds m, Char.chr k);
       DString.push(#opcodes m, Char.chr (#opcode meta));
       DArray.push(#name_idx m, ni);
       edges (#prod_ns m) (#prod_id m) (#produced meta);
       edges (#cons_ns m) (#cons_id m) (#consumed meta);
       DArray.push(#prod_start m, DArray.size (#prod_id m));
       DArray.push(#cons_start m, DArray.size (#cons_id m))
    end

  fun app_slice starts nsbuf ids ci f =
    let val stop = DArray.sub(starts, ci + 1)
        fun loop i = if i = stop then () else
          (f (Char.ord (DString.sub(nsbuf, i)), DArray.sub(ids, i));
           loop (i + 1))
    in loop (DArray.sub(starts, ci)) end
  fun app_produced (m: t) =
    app_slice (#prod_start m) (#prod_ns m) (#prod_id m)
  fun app_consumed (m: t) =
    app_slice (#cons_start m) (#cons_ns m) (#cons_id m)
  fun prod_count ({prod_start, ...}: t) ci =
    DArray.sub(prod_start, ci + 1) - DArray.sub(prod_start, ci)
  fun first_prod_ns ({prod_start, prod_ns, ...}: t) ci =
    Char.ord (DString.sub(prod_ns, DArray.sub(prod_start, ci)))
  fun appi f m =
    let val n = size m
        fun loop ci = if ci = n then () else (f ci; loop (ci + 1))
    in loop 0 end
end

(* Common producer IDs are dense. A bounded sparse fallback preserves valid
   nonmonotonic inputs without allocating up to an arbitrary source ID. *)
structure Producers = struct
  type space = {dense: int DArray.darray,
                sparse: (int, int) Redblackmap.dict ref}
  type t = space vector
  fun new () : t = Vector.tabulate(NUM_NS, fn _ =>
    {dense=DArray.new(1024, ~1),
     sparse=ref (Redblackmap.mkDict Int.compare)})
  fun peek (p: t) (ns, id) =
    let val {dense, sparse} = Vector.sub(p, ns)
        val ci = if id < DArray.size dense then DArray.sub(dense, id)
                 else ~1
    in if ci >= 0 then SOME ci else Redblackmap.peek(!sparse, id) end
  fun insert (p: t) (ns, id) ci =
    let val {dense, sparse} = Vector.sub(p, ns)
    in if id < DArray.size dense orelse id < 1024 orelse id div 2 <= ci
       then
         let fun grow () = if DArray.size dense > id then () else
               (DArray.push(dense, ~1); grow ())
         in grow (); DArray.update(dense, id, ci) end
       else sparse := Redblackmap.insert(!sparse, id, ci)
    end
end

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
  cmds : Metadata.t,
  producers : Producers.t
}

fun pair_compare ((a1:int,b1:int), (a2,b2)) =
  case Int.compare(a1,a2) of EQUAL => Int.compare(b1,b2) | ord => ord

fun new_file_state fi : file_state = {
  file_idx = fi,
  cmds = Metadata.new (),
  producers = Producers.new ()
}

fun record_producers file_idx producers ci (meta: cmd_meta) =
  let
    fun check_input (ns, id) =
      if isSome (Producers.peek producers (ns, id)) then ()
      else raise Fail ("PFTMerge: missing or forward reference to " ^
                       ns_name ns ^ "#" ^ Int.toString id ^ " in file " ^
                       Int.toString file_idx)
    fun add_output (ns, id) =
      if isSome (Producers.peek producers (ns, id)) then
        raise Fail ("PFTMerge: reused input ID " ^ ns_name ns ^ "#" ^
                    Int.toString id ^ " in file " ^
                    Int.toString file_idx)
      else Producers.insert producers (ns, id) ci
  in List.app check_input (#consumed meta);
     List.app add_output (#produced meta)
  end

fun add_cmd (fs: file_state) (meta: cmd_meta) =
  let val ci = Metadata.size (#cmds fs)
      val () = record_producers (#file_idx fs) (#producers fs) ci meta
  in Metadata.push (#cmds fs) meta; ci end

fun find_producer (fs: file_state) (ns, id) =
  case Producers.peek (#producers fs) (ns, id) of
    SOME ci => ci
  | NONE =>
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
    val producers = Producers.new ()
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
fun compute_reachable ruleset
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
                    val a = Array.array(Metadata.size (#cmds fs), false)
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

    (* These rules construct registered connectives without a CONST operand. *)
    fun implicit_consts opcode =
      if ruleset <> "hol4" then [] else
      case List.find (fn (op', _) => op' = opcode) hol4_descs of
        NONE => []
      | SOME (_, {tag, ...}) =>
          case tag of
            "CONJ" => ["bool$/\\"]
          | "CONJUNCT1" => ["bool$/\\"]
          | "CONJUNCT2" => ["bool$/\\"]
          | "DISJ1" => ["bool$\\/"]
          | "DISJ2" => ["bool$\\/"]
          | "DISJ_CASES" => ["bool$\\/"]
          | "GEN" => ["bool$!"]
          | "GENL" => ["bool$!"]
          | "SPEC" => ["bool$!"]
          | "Specialize" => ["bool$!"]
          | "EXISTS" => ["bool$?"]
          | "CHOOSE" => ["bool$?"]
          | "DEF_SPEC" => ["bool$?"]
          | "DEF_TYOP" => ["bool$TYPE_DEFINITION", "bool$?"]
          | "NOT_INTRO" => ["bool$~", "bool$F"]
          | "NOT_ELIM" => ["bool$~", "bool$F"]
          | "CCONTR" => ["bool$~", "bool$F"]
          | _ => []

    fun process () =
      case !worklist of
        [] => ()
      | (fi, ci) :: rest =>
        let val () = worklist := rest
            val fs = ensure_file_state fi
            val cmds = #cmds fs
        in
          (* Follow ID-level dependencies *)
          Metadata.app_consumed cmds ci (fn (ns, id) =>
            enqueue (fi, find_producer fs (ns, id)));
          (* Follow cross-file LOAD dependencies *)
          (case Metadata.kind cmds ci of
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
          List.app (fn name =>
            case Redblackmap.peek(const_introducer, name) of
              NONE => () (* Supplied by the replay environment. *)
            | SOME (ifi, ici) =>
                if ifi < fi orelse (ifi = fi andalso ici < ci) then
                  enqueue (ifi, ici)
                else raise Fail
                  ("PFTMerge: implicit constant used before introduction: " ^
                   name)) (implicit_consts (Metadata.opcode cmds ci));
          (* Follow name-level dependencies: CONST/TYOP → introducer *)
          (case Metadata.ref_name cmds ci of
             SOME name =>
               let val table = if Metadata.opcode cmds ci = 0x04
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
    val included = compute_reachable ruleset n_files ensure_file_state save_table
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
            val () = Metadata.appi (fn ci =>
              Metadata.app_produced (#cmds fs) ci (fn (ns, id) =>
                if id >= Array.sub(maxes, ns)
                then Array.update(maxes, ns, id + 1) else ())) (#cmds fs)
        in Vector.tabulate(NUM_NS, fn ns =>
             Array.array(Array.sub(maxes, ns), NONE : int option))
        end)

    fun lookup_save name =
      case Redblackmap.peek(save_table, name) of
        SOME e => e
      | NONE => raise Fail ("PFTMerge: unknown SAVE: " ^ name)

    (* LOADs own no slot. Store their canonical source before metadata is
       released, so later uses never reload an already emitted file. *)
    val aliases = ref (Redblackmap.mkDict pair_compare)
    fun canonical fi ns id =
      if ns <> NS_TH then (fi, ns, id)
      else case Redblackmap.peek(!aliases, (fi, id)) of
             SOME (sfi, sid) => (sfi, ns, sid)
           | NONE => (fi, ns, id)
    val () = app_included (fn (fi, fs, vis) =>
      Metadata.appi (fn ci =>
        if not (Array.sub(vis, ci)) then ()
        else case Metadata.kind (#cmds fs) ci of
          CmdLoad name =>
            let val {file_idx, th_id, ...} = lookup_save name
                val (sfi, _, sid) = canonical file_idx NS_TH th_id
            in Metadata.app_produced (#cmds fs) ci (fn (_, id) =>
                 aliases := Redblackmap.insert(!aliases, (fi, id),
                                               (sfi, sid)))
            end
        | _ => ()) (#cmds fs))

    fun rename_array fi ns =
      Vector.sub(Vector.sub(rename_tables, fi), ns)
    fun set_rename fi ns old_id new_id =
      Array.update(rename_array fi ns, old_id, SOME new_id)
    fun get_rename fi ns old_id =
      let val (fi, ns, old_id) = canonical fi ns old_id
      in case Array.sub(rename_array fi ns, old_id) of
           SOME nid => nid
         | NONE => raise Fail ("PFTMerge: unmapped " ^ ns_name ns ^ "#" ^
                                Int.toString old_id ^ " in file " ^
                                Int.toString fi)
      end

    fun allocate fi ci =
      let val cmds = #cmds (loaded_file fi)
          val n = Metadata.prod_count cmds ci
          val same_ns = ref true
          val ns = if n = 0 then NS_TY else Metadata.first_prod_ns cmds ci
          val () = Metadata.app_produced cmds ci (fn (ns', _) =>
            if ns' = ns then () else same_ns := false)
      in if n > 1 andalso !same_ns then
           let val base = IdAlloc.alloc_consecutive
                            (Vector.sub(allocators, ns)) n
               val i = ref 0
           in Metadata.app_produced cmds ci (fn (_, id) =>
                (set_rename fi ns id (base + !i); i := !i + 1))
           end
         else Metadata.app_produced cmds ci (fn (ns, id) =>
                set_rename fi ns id (alloc_id ns))
      end

    (* Counts belong to old identities, including uses through LOAD aliases. *)
    val refcounts = Vector.map (Vector.map
      (fn a => Array.array(Array.length a, 0))) rename_tables
    fun count_array fi ns = Vector.sub(Vector.sub(refcounts, fi), ns)
    fun inc_ref fi ns id =
      let val (fi, ns, id) = canonical fi ns id
          val a = count_array fi ns
      in Array.update(a, id, Array.sub(a, id) + 1) end
    fun real_command cmds ci =
      case Metadata.kind cmds ci of CmdDel => false | CmdSave _ => false
                                 | CmdLoad _ => false | _ => true
    val () = app_included (fn (fi, fs, vis) =>
      Metadata.appi (fn ci =>
        if Array.sub(vis, ci) andalso real_command (#cmds fs) ci then
          Metadata.app_consumed (#cmds fs) ci (fn (ns, id) => inc_ref fi ns id)
        else ()) (#cmds fs))

    val def_saves =
      if not (List.exists #2 target_saves) then []
      else let val acc = ref [] : (int * int) list ref
      in app_included (fn (fi, fs, vis) =>
           Metadata.appi (fn ci =>
             if Array.sub(vis, ci) then
               case Metadata.kind (#cmds fs) ci of
                 CmdDef => Metadata.app_produced (#cmds fs) ci (fn (ns, id) =>
                   if ns = NS_TH then acc := (fi, id) :: !acc else ())
               | _ => ()
             else ()) (#cmds fs));
         List.rev (!acc)
      end
    val () = List.app (fn (name, _) =>
      let val {file_idx, th_id, ...} = lookup_save name
      in inc_ref file_idx NS_TH th_id end) target_saves
    val () = List.app (fn (fi, id) => inc_ref fi NS_TH id) def_saves

    (* Step 3: Emit *)
    val out = PFTWriter.openOut {file=output,
                                 version=version, ruleset=ruleset}

    fun release fi ns id =
      let val nid = get_rename fi ns id
      in PFTWriter.del out (ns_name ns) nid;
         IdAlloc.release (Vector.sub(allocators, ns)) nid;
         Array.update(rename_array fi ns, id, NONE)
      end
    fun dec_ref fi ns id =
      let val (fi, ns, id) = canonical fi ns id
          val a = count_array fi ns
          val rc = Array.sub(a, id) - 1
      in Array.update(a, id, rc);
         if rc = 0 then release fi ns id else ()
      end

    val current_fi = ref 0
    fun is_included ci =
      case !(Vector.sub(included, !current_fi)) of
        SOME vis => Array.sub(vis, ci)
      | NONE => false
    fun ren ns id = get_rename (!current_fi) ns id
    fun finish_command ci =
      let val fi = !current_fi
          val cmds = #cmds (loaded_file fi)
      in Metadata.app_consumed cmds ci (fn (ns, id) => dec_ref fi ns id);
         Metadata.app_produced cmds ci (fn (ns, id) =>
           if Array.sub(count_array fi ns, id) = 0 then release fi ns id
           else ())
      end

    (* Handlers for pass 2 re-read. Format and ruleset handlers share
       a command counter so they stay synchronised with pass 1 metadata. *)
    fun make_handlers () =
      let
        val ci_ref = ref 0
        fun next_ci () = let val c = !ci_ref in ci_ref := c + 1; c end

        fun when_included ci f =
          if is_included ci then
            (allocate (!current_fi) ci; f (); finish_command ci)
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
          load = fn _ => ignore (next_ci ()),
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
                 val () = allocate (!current_fi) ci
                 val result = ren (ns_idx (hd (#results desc))) id
                 val args = ListPair.map rename_arg (#args desc, args)
               in PFTWriter.write_raw out
                    {opcode=opc, desc=desc, result=result, args=args};
                  finish_command ci
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
                                    format_handler=fh, ruleset_handler=rh});
             Vector.sub(file_states, fi) := NONE;
             Vector.sub(included, fi) := NONE));
       fi + 1)) 0 inputs)

    (* Emit target SAVEs *)
    val () = List.app (fn (name, _) =>
      let val {file_idx, th_id, ...} = lookup_save name
          val nid = get_rename file_idx NS_TH th_id
      in PFTWriter.save out name nid; dec_ref file_idx NS_TH th_id end)
      target_saves

    (* Emit definition SAVEs *)
    val () = List.app (fn (fi, id) =>
      let val nid = get_rename fi NS_TH id
      in PFTWriter.save out ("def:" ^ Int.toString nid) nid;
         dec_ref fi NS_TH id
      end) def_saves

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
    val () = if OS.FileSys.access(output, []) andalso
                List.exists (fn file => OS.FileSys.fileId file =
                                        OS.FileSys.fileId output) inputs
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
