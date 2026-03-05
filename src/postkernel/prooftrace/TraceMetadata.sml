(* TraceMetadata: read/write/extract .pftm metadata summary files.

   A .pftm file contains the lightweight metadata from a .pft trace
   (exports, NAME/LOAD refs, DEF_SPEC/DEF_TYOP, C/O declarations,
   T/Y const/type refs, counts, P ID range) without the bulk P/T/Y
   entries. This lets the merge tool load file metadata without
   scanning multi-GB trace files.

   Format: text lines, same syntax as .pft where possible.
     S ny=N nt=N pmin=N pmax=N       summary counts/range
     H <path>                         heap parent
     C <thy> <name> <tyid>            const declaration
     O <thy> <name> <arity>           type declaration
     I <args...>                      compute init deps
     P <id> NAME <thy> <name>         NAME ref
     P <id> LOAD <thy> <src_id>       LOAD ref
     P <id> DEF_SPEC <thy> <names...> const definition
     P <id> DEF_TYOP <thy> <tyop>     type definition
     P <id> COMPUTE                   compute entry
     TC <tid> <thy> <name>            T entry const ref
     YO <yid> <thy> <tyop>            Y entry type ref
     N <name>                         theory name
     E <name> <id>                    export
*)

structure TraceMetadata :> TraceMetadata =
struct

val ERR = Feedback.mk_HOL_ERR "TraceMetadata"
fun its i = Int.toString i
val esc = TraceRecord.escape_string
val tokenize = ReplayTrace.tokenize
val unescape = ReplayTrace.unescape

type metadata = {
  n_types : int,
  n_terms : int,
  p_min_id : int,
  p_max_id : int,
  heap_parent : string option,
  thy_name : string,
  exports : (string * int) list,
  name_refs : (int * string * string) list,
  load_refs : (int * string * int) list,
  const_defs : (int * string * string list) list,
  type_defs : (int * string * string) list,
  const_decls : (string * string * int) list,
  type_decls : (string * string * int) list,
  t_const_refs : (int * string * string) list,
  y_tyop_refs : (int * string * string) list,
  compute_ids : int list,
  c_deps : (int list * int list * int list) option
}

fun int_of s = case Int.fromString s of
    SOME n => n
  | NONE => raise ERR "int_of" ("not an int: " ^ s)

fun metadata_path base =
  let val p = if String.isSuffix ".pft" base then base
              else base ^ ".pft"
  in p ^ "m" end

(* ------- Write ------- *)

fun write path (m : metadata) =
  let
    val s = TextIO.openOut path
    fun wr x = TextIO.output(s, x)
    fun wl x = (wr x; wr "\n")
  in
    wl ("S ny=" ^ its (#n_types m) ^
        " nt=" ^ its (#n_terms m) ^
        " pmin=" ^ its (#p_min_id m) ^
        " pmax=" ^ its (#p_max_id m));
    (case #heap_parent m of
       SOME hp => wl ("H " ^ esc hp)
     | NONE => ());
    List.app (fn (thy, name, tyid) =>
      wl ("C " ^ esc thy ^ " " ^ esc name ^ " " ^ its tyid))
      (#const_decls m);
    List.app (fn (thy, name, arity) =>
      wl ("O " ^ esc thy ^ " " ^ esc name ^ " " ^ its arity))
      (#type_decls m);
    (case #c_deps m of
       SOME (parents, terms, types) =>
         wl ("I P " ^ String.concatWith " " (map its parents) ^
             " T " ^ String.concatWith " " (map its terms) ^
             " Y " ^ String.concatWith " " (map its types))
     | NONE => ());
    List.app (fn (id, thy, name) =>
      wl ("P " ^ its id ^ " NAME " ^ esc thy ^ " " ^ esc name))
      (#name_refs m);
    List.app (fn (id, thy, src_id) =>
      wl ("P " ^ its id ^ " LOAD " ^ esc thy ^ " " ^ its src_id))
      (#load_refs m);
    List.app (fn (id, thy, names) =>
      wl ("P " ^ its id ^ " DEF_SPEC " ^ esc thy ^ " " ^
          String.concatWith " " (map esc names)))
      (#const_defs m);
    List.app (fn (id, thy, tyop) =>
      wl ("P " ^ its id ^ " DEF_TYOP " ^ esc thy ^ " " ^ esc tyop))
      (#type_defs m);
    List.app (fn id =>
      wl ("P " ^ its id ^ " COMPUTE"))
      (#compute_ids m);
    List.app (fn (tid, thy, name) =>
      wl ("TC " ^ its tid ^ " " ^ esc thy ^ " " ^ esc name))
      (#t_const_refs m);
    List.app (fn (yid, thy, tyop) =>
      wl ("YO " ^ its yid ^ " " ^ esc thy ^ " " ^ esc tyop))
      (#y_tyop_refs m);
    (if #thy_name m <> "" then
       wl ("N " ^ esc (#thy_name m))
     else ());
    List.app (fn (name, id) =>
      wl ("E " ^ esc name ^ " " ^ its id))
      (#exports m);
    TextIO.closeOut s
  end

(* ------- Read ------- *)

fun read path =
  if not (OS.FileSys.access(path, [OS.FileSys.A_READ]))
  then NONE
  else
  let
    val s = TextIO.openIn path
    val n_types = ref 0
    val n_terms = ref 0
    val p_min_id = ref ~1
    val p_max_id = ref ~1
    val heap_parent = ref (NONE : string option)
    val thy_name = ref ""
    val exports_rev = ref ([] : (string * int) list)
    val name_refs_rev = ref ([] : (int * string * string) list)
    val load_refs_rev = ref ([] : (int * string * int) list)
    val const_defs_rev = ref ([] : (int * string * string list) list)
    val type_defs_rev = ref ([] : (int * string * string) list)
    val const_decls_rev = ref ([] : (string * string * int) list)
    val type_decls_rev = ref ([] : (string * string * int) list)
    val t_const_refs_rev = ref ([] : (int * string * string) list)
    val y_tyop_refs_rev = ref ([] : (int * string * string) list)
    val compute_ids_rev = ref ([] : int list)
    val c_deps_ref = ref (NONE : (int list * int list * int list) option)

    fun process_line line =
      let val toks = tokenize line in
      case toks of
        ("S" :: rest) =>
          List.app (fn tok =>
            let val (k, v) = Substring.splitl (fn c => c <> #"=")
                               (Substring.full tok)
                val key = Substring.string k
                val value = Substring.string
                              (Substring.triml 1 v)  (* skip = *)
            in case key of
                 "ny" => n_types := int_of value
               | "nt" => n_terms := int_of value
               | "pmin" => p_min_id := int_of value
               | "pmax" => p_max_id := int_of value
               | _ => ()
            end) rest
      | ("H" :: hp :: _) =>
          heap_parent := SOME (unescape hp)
      | ("C" :: thy_s :: name_s :: ty_s :: _) =>
          const_decls_rev := (unescape thy_s, unescape name_s,
                              int_of ty_s) :: !const_decls_rev
      | ("O" :: thy_s :: name_s :: arity_s :: _) =>
          type_decls_rev := (unescape thy_s, unescape name_s,
                             int_of arity_s) :: !type_decls_rev
      | ("I" :: "P" :: rest) =>
          (* Simplified I format: I P <ids...> T <ids...> Y <ids...> *)
          let
            fun split_at _ [] = ([], [])
              | split_at tok (x :: xs) =
                  if x = tok then ([], xs)
                  else let val (a, b) = split_at tok xs in (x::a, b) end
            val (p_toks, rest1) = split_at "T" rest
            val (t_toks, y_toks) = split_at "Y" rest1
          in
            c_deps_ref := SOME (map int_of p_toks,
                                map int_of t_toks,
                                map int_of y_toks)
          end
      | ["P", id_s, "NAME", thy_s, name_s] =>
          name_refs_rev := (int_of id_s, unescape thy_s,
                            unescape name_s) :: !name_refs_rev
      | ["P", id_s, "LOAD", thy_s, src_s] =>
          load_refs_rev := (int_of id_s, unescape thy_s,
                            int_of src_s) :: !load_refs_rev
      | ("P" :: id_s :: "DEF_SPEC" :: thy_s :: names) =>
          const_defs_rev := (int_of id_s, unescape thy_s,
                             map unescape names) :: !const_defs_rev
      | ["P", id_s, "DEF_TYOP", thy_s, tyop_s] =>
          type_defs_rev := (int_of id_s, unescape thy_s,
                            unescape tyop_s) :: !type_defs_rev
      | ["P", id_s, "COMPUTE"] =>
          compute_ids_rev := int_of id_s :: !compute_ids_rev
      | ["TC", tid_s, thy_s, name_s] =>
          t_const_refs_rev := (int_of tid_s, unescape thy_s,
                               unescape name_s) :: !t_const_refs_rev
      | ["YO", yid_s, thy_s, tyop_s] =>
          y_tyop_refs_rev := (int_of yid_s, unescape thy_s,
                              unescape tyop_s) :: !y_tyop_refs_rev
      | ("N" :: name :: _) =>
          thy_name := unescape name
      | ("E" :: name :: id_s :: _) =>
          exports_rev := (unescape name, int_of id_s) :: !exports_rev
      | _ => ()
      end

    fun read_all () =
      case TextIO.inputLine s of
        NONE => ()
      | SOME line =>
          (process_line (String.substring(line, 0, size line - 1)
                         handle Subscript => line);
           read_all ())
  in
    read_all ();
    TextIO.closeIn s;
    SOME {
      n_types = !n_types,
      n_terms = !n_terms,
      p_min_id = !p_min_id,
      p_max_id = !p_max_id,
      heap_parent = !heap_parent,
      thy_name = !thy_name,
      exports = rev (!exports_rev),
      name_refs = rev (!name_refs_rev),
      load_refs = rev (!load_refs_rev),
      const_defs = rev (!const_defs_rev),
      type_defs = rev (!type_defs_rev),
      const_decls = rev (!const_decls_rev),
      type_decls = rev (!type_decls_rev),
      t_const_refs = rev (!t_const_refs_rev),
      y_tyop_refs = rev (!y_tyop_refs_rev),
      compute_ids = rev (!compute_ids_rev),
      c_deps = !c_deps_ref
    }
  end
  handle e => (Feedback.HOL_WARNING "TraceMetadata" "read"
                 ("failed to read " ^ path ^ ": " ^
                  General.exnMessage e);
               NONE)

(* ------- Extract (scan .pft) ------- *)

fun extract path =
  let
    val (instrm, close_instrm) = TraceCompress.open_trace path
    val ty_count = ref 0
    val tm_count = ref 0
    val heap_parent = ref (NONE : string option)
    val thy_name = ref ""
    val exports_rev = ref ([] : (string * int) list)
    val name_refs_rev = ref ([] : (int * string * string) list)
    val load_refs_rev = ref ([] : (int * string * int) list)
    val const_defs_rev = ref ([] : (int * string * string list) list)
    val type_defs_rev = ref ([] : (int * string * string) list)
    val const_decls_rev = ref ([] : (string * string * int) list)
    val type_decls_rev = ref ([] : (string * string * int) list)
    val t_const_refs_rev = ref ([] : (int * string * string) list)
    val y_tyop_refs_rev = ref ([] : (int * string * string) list)
    val compute_ids_rev = ref ([] : int list)
    val c_deps_ref = ref (NONE : (int list * int list * int list) option)
    val p_min_id = ref ~1
    val p_max_id = ref ~1

    (* Fast integer extraction: parse non-negative int starting at
       position i in string s, skipping leading spaces. Returns
       (value, position_after) or NONE if no int found. *)
    fun scan_int s i =
      let val len = size s
          fun skip_sp j = if j >= len then j
                          else if Char.isSpace (String.sub(s, j))
                          then skip_sp (j+1) else j
          val j = skip_sp i
          fun go k acc =
            if k >= len then
              if k > j then SOME (acc, k) else NONE
            else let val c = String.sub(s, k)
                 in if Char.isDigit c
                    then go (k+1) (acc * 10 + Char.ord c - 48)
                    else if k > j then SOME (acc, k) else NONE
                 end
      in if j >= len then NONE else go j 0 end

    (* Check whether line contains a substring starting at position i *)
    fun has_prefix line i prefix =
      let val plen = size prefix
      in i + plen <= size line andalso
         String.substring(line, i, plen) = prefix
      end

    fun process_line line =
      if size line < 2 then ()
      else
      let val c0 = String.sub(line, 0)
      in
        if c0 = #"P" then
          (* P lines: fast-path for the common case (most rules).
             Only tokenize for NAME/LOAD/DEF_SPEC/DEF_TYOP/COMPUTE. *)
          (case scan_int line 2 of
             NONE => ()
           | SOME (id, pos) =>
               let
                 val _ = if !p_min_id < 0 orelse id < !p_min_id
                         then p_min_id := id else ()
                 val _ = if id > !p_max_id then p_max_id := id else ()
               in
                 (* Check for special rules by prefix *)
                 if has_prefix line pos " NAME " then
                   let val toks = tokenize line in
                   (case toks of
                     ("P" :: _ :: "NAME" :: args) =>
                       name_refs_rev :=
                         (id, unescape (List.nth(args, 0)),
                              unescape (List.nth(args, 1)))
                         :: !name_refs_rev
                   | _ => ())
                   end
                 else if has_prefix line pos " LOAD " then
                   let val toks = tokenize line in
                   (case toks of
                     ("P" :: _ :: "LOAD" :: args) =>
                       load_refs_rev :=
                         (id, unescape (List.nth(args, 0)),
                              int_of (List.nth(args, 1)))
                         :: !load_refs_rev
                   | _ => ())
                   end
                 else if has_prefix line pos " DEF_SPEC " then
                   let val toks = tokenize line in
                   (case toks of
                     ("P" :: _ :: "DEF_SPEC" :: args) =>
                       let val thyname = unescape (List.nth(args, 1))
                           val cnames =
                             map unescape (List.drop(args, 2))
                       in const_defs_rev :=
                            (id, thyname, cnames)
                            :: !const_defs_rev
                       end
                   | _ => ())
                   end
                 else if has_prefix line pos " DEF_TYOP " then
                   let val toks = tokenize line in
                   (case toks of
                     ("P" :: _ :: "DEF_TYOP" :: args) =>
                       let val thy = unescape (List.nth(args, 1))
                           val tyop = unescape (List.nth(args, 2))
                       in type_defs_rev :=
                            (id, thy, tyop) :: !type_defs_rev
                       end
                   | _ => ())
                   end
                 else if has_prefix line pos " COMPUTE" then
                   compute_ids_rev := id :: !compute_ids_rev
                 else () (* common case: no tokenize needed *)
               end)
        else if c0 = #"T" then
          let val toks = tokenize line in
          (case toks of
            ("T" :: id_s :: "V" :: _) =>
              tm_count := Int.max(!tm_count, int_of id_s + 1)
          | ("T" :: id_s :: "C" :: thy_s :: name_s :: _) =>
              let val id = int_of id_s
                  val thy = unescape thy_s
                  val name = unescape name_s
              in tm_count := Int.max(!tm_count, id + 1);
                 if thy <> "min" then
                   t_const_refs_rev := (id, thy, name)
                                      :: !t_const_refs_rev
                 else ()
              end
          | ("T" :: id_s :: "A" :: _) =>
              tm_count := Int.max(!tm_count, int_of id_s + 1)
          | ("T" :: id_s :: "L" :: _) =>
              tm_count := Int.max(!tm_count, int_of id_s + 1)
          | _ => ())
          end
        else if c0 = #"Y" then
          let val toks = tokenize line in
          (case toks of
            ("Y" :: id_s :: "V" :: _) =>
              ty_count := Int.max(!ty_count, int_of id_s + 1)
          | ("Y" :: id_s :: "O" :: thy_s :: name_s :: _) =>
              let val id = int_of id_s
                  val thy = unescape thy_s
                  val name = unescape name_s
              in ty_count := Int.max(!ty_count, id + 1);
                 if thy <> "min" then
                   y_tyop_refs_rev := (id, thy, name)
                                      :: !y_tyop_refs_rev
                 else ()
              end
          | _ => ())
          end
        else if c0 = #"H" then
          let val toks = tokenize line in
          (case toks of ("H" :: hp :: _) =>
            heap_parent := SOME (unescape hp)
          | _ => ())
          end
        else if c0 = #"N" then
          let val toks = tokenize line in
          (case toks of ("N" :: name :: _) =>
            thy_name := unescape name
          | _ => ())
          end
        else if c0 = #"E" then
          let val toks = tokenize line in
          (case toks of ("E" :: name :: id_s :: _) =>
            exports_rev := (unescape name, int_of id_s)
                           :: !exports_rev
          | _ => ())
          end
        else if c0 = #"I" then
          let val toks = tokenize line in
          (case toks of ("I" :: args) =>
            let
              (* Skip ~k/^k stack refs — only collect explicit IDs *)
              fun is_stack_ref s = size s > 0 andalso
                (String.sub(s, 0) = #"~" orelse String.sub(s, 0) = #"^")
              fun ai n = int_of (List.nth(args, n))
              val type_ids = [ai 0, ai 1]
              val rest = List.drop(args, 2)
              val term_ids =
                List.mapPartial (fn i =>
                  let val s = List.nth(rest, 2*i + 1)
                  in if is_stack_ref s then NONE
                     else SOME (int_of s)
                  end)
                (List.tabulate(29, fn i => i))
              val rest2 = List.drop(rest, 58)
              fun get_parents [] = []
                | get_parents (_::p::r) =
                    if is_stack_ref p then get_parents r
                    else int_of p :: get_parents r
                | get_parents _ = []
              val parent_ids = get_parents rest2
            in
              c_deps_ref := SOME (parent_ids, term_ids, type_ids)
            end
          | _ => ())
          end
        else if c0 = #"C" then
          let val toks = tokenize line in
          (case toks of ("C" :: thy_s :: name_s :: ty_s :: _) =>
            const_decls_rev := (unescape thy_s, unescape name_s,
                                int_of ty_s) :: !const_decls_rev
          | _ => ())
          end
        else if c0 = #"O" then
          let val toks = tokenize line in
          (case toks of ("O" :: thy_s :: name_s :: arity_s :: _) =>
            type_decls_rev := (unescape thy_s, unescape name_s,
                               int_of arity_s) :: !type_decls_rev
          | _ => ())
          end
        else ()
      end

    fun read_all () =
      case TextIO.inputLine instrm of
        NONE => ()
      | SOME line =>
          (process_line (String.substring(line, 0, size line - 1)
                         handle Subscript => line);
           read_all ())
  in
    read_all ();
    close_instrm ();
    TraceCompress.release_temp path;
    { n_types = !ty_count,
      n_terms = !tm_count,
      p_min_id = !p_min_id,
      p_max_id = !p_max_id,
      heap_parent = !heap_parent,
      thy_name = !thy_name,
      exports = rev (!exports_rev),
      name_refs = rev (!name_refs_rev),
      load_refs = rev (!load_refs_rev),
      const_defs = rev (!const_defs_rev),
      type_defs = rev (!type_defs_rev),
      const_decls = rev (!const_decls_rev),
      type_decls = rev (!type_decls_rev),
      t_const_refs = rev (!t_const_refs_rev),
      y_tyop_refs = rev (!y_tyop_refs_rev),
      compute_ids = rev (!compute_ids_rev),
      c_deps = !c_deps_ref }
  end

end
