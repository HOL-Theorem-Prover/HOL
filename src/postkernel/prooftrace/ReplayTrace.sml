(* ReplayTrace: parse and replay .pftrace files to verify proof traces.

   Given a .pftrace file:
   1. Reconstruct type/term arrays from Y/M entries
   2. Replay proof steps using actual kernel inference rules
   3. Verify exported theorem names map to correctly reconstructed thms

   ORACLE and AXIOM steps include their theorem statement in the trace
   and are created via mk_oracle_thm. All other steps are fully replayed
   through the kernel. Ancestor theorems (DISK_THM) are recorded as
   ORACLE with tag "DISK_THM" and resolved against replayed ancestors
   during chain verification.
*)

structure ReplayTrace :> ReplayTrace =
struct

open HolKernel

val ERR = mk_HOL_ERR "ReplayTrace"

val replay_debug = ref false
val first_fail = ref (NONE : string option)


fun its i = Int.toString i

(* -----------------------------------------------------------------------
   String unescaping (inverse of TraceExport.escape_string)
   ----------------------------------------------------------------------- *)
fun unescape s =
  if size s >= 2 andalso String.sub(s, 0) = #"\"" then
    let
      val inner = String.substring(s, 1, size s - 2)
      fun go [] acc = String.implode (rev acc)
        | go (#"\\" :: #"\"" :: rest) acc = go rest (#"\"" :: acc)
        | go (#"\\" :: #"\\" :: rest) acc = go rest (#"\\" :: acc)
        | go (#"\\" :: #"n" :: rest) acc = go rest (#"\n" :: acc)
        | go (#"\\" :: #"x" :: h1 :: h2 :: rest) acc =
            (case Int.scan StringCvt.HEX Substring.getc
                    (Substring.full (String.implode [h1, h2])) of
               SOME (n, _) => go rest (Char.chr n :: acc)
             | NONE => go rest (h2 :: h1 :: #"x" :: #"\\" :: acc))
        | go (c :: rest) acc = go rest (c :: acc)
    in go (String.explode inner) [] end
  else s

(* -----------------------------------------------------------------------
   Tokenizer: split on spaces, respecting quoted strings
   ----------------------------------------------------------------------- *)
fun tokenize line =
  let
    fun skip_ws [] = []
      | skip_ws (c :: rest) = if Char.isSpace c then skip_ws rest else c :: rest
    fun read_quoted [] acc = (String.implode (rev (#"\"" :: acc)), [])
      | read_quoted (#"\\" :: c :: rest) acc =
          read_quoted rest (c :: #"\\" :: acc)
      | read_quoted (#"\"" :: rest) acc =
          (String.implode (rev (#"\"" :: acc)), rest)
      | read_quoted (c :: rest) acc = read_quoted rest (c :: acc)
    fun read_token [] acc = (String.implode (rev acc), [])
      | read_token (c :: rest) acc =
          if Char.isSpace c then (String.implode (rev acc), c :: rest)
          else read_token rest (c :: acc)
    fun go chars acc =
      case skip_ws chars of
        [] => rev acc
      | #"\"" :: rest =>
          let val (tok, rest') = read_quoted rest [#"\""]
          in go rest' (tok :: acc) end
      | chars =>
          let val (tok, rest') = read_token chars []
          in go rest' (tok :: acc) end
  in go (String.explode line) [] end

(* -----------------------------------------------------------------------
   Parse header
   ----------------------------------------------------------------------- *)

datatype header = Header of {
  version: int,
  theory: string,
  n_types: int,
  n_terms: int,
  n_steps: int
}

fun parse_header (lines : string list) =
  let
    fun get_line prefix [] = raise ERR "parse_header"
          ("missing " ^ prefix)
      | get_line prefix (l :: rest) =
          if String.isPrefix prefix l
          then (String.extract(l, size prefix, NONE), rest)
          else get_line prefix rest
    val lines = List.filter (fn l => size l > 0) lines
    val (ver_str, lines) = get_line "HOL4_PROOF_TRACE " lines
    val version = case Int.fromString ver_str of
        SOME v => v
      | NONE => raise ERR "parse_header" ("bad version: " ^ ver_str)
    val _ = if version <> 1 then
              raise ERR "parse_header"
                ("unsupported version " ^ Int.toString version)
            else ()
    val (thy_str, lines) = get_line "THEORY " lines
    val theory = unescape thy_str
    val (cnt_str, _) = get_line "COUNTS " lines
    val cnts = String.tokens Char.isSpace cnt_str
    val (n_types, n_terms, n_steps) =
      case List.mapPartial Int.fromString cnts of
        [a, b, c] => (a, b, c)
      | _ => raise ERR "parse_header" "COUNTS must have 3 integers"
  in
    Header {version=version, theory=theory,
            n_types=n_types, n_terms=n_terms, n_steps=n_steps}
  end

(* -----------------------------------------------------------------------
   Build type array from Y entries
   ----------------------------------------------------------------------- *)

(* Lazy type/term construction: parse lines into raw descriptions,
   construct actual types/terms on demand. This ensures definitions
   (DEF_TYOP, DEF_SPEC) have been replayed before the types/terms
   they define are constructed, avoiding stale kernelid issues. *)

datatype ty_desc = TyVar of string | TyOp of string * string * int list
datatype tm_desc = TmVar of string * int
                 | TmConst of string * string * int
                 | TmApp of int * int
                 | TmLam of int * int

fun parse_type_descs n_types (lines : string list) =
  let
    val arr = Array.array(n_types, TyVar "'_")
    fun process line =
      case tokenize line of
        (_ :: id_s :: "V" :: rest) =>
          Array.update(arr, valOf (Int.fromString id_s),
                       TyVar (unescape (hd rest)))
      | (_ :: id_s :: "O" :: rest) =>
          let val thy = unescape (hd rest)
              val name = unescape (hd (tl rest))
              val arg_ids = List.mapPartial Int.fromString (tl (tl rest))
          in Array.update(arr, valOf (Int.fromString id_s),
                          TyOp (thy, name, arg_ids))
          end
      | _ => raise ERR "parse_type_descs" ("bad line: " ^ line)
  in List.app process lines; arr end

fun parse_term_descs n_terms (lines : string list) =
  let
    val arr = Array.array(n_terms, TmVar ("_", 0))
    fun process line =
      case tokenize line of
        (_ :: id_s :: "V" :: name_s :: ty_s :: _) =>
          Array.update(arr, valOf (Int.fromString id_s),
                       TmVar (unescape name_s, valOf (Int.fromString ty_s)))
      | (_ :: id_s :: "C" :: thy_s :: name_s :: ty_s :: _) =>
          Array.update(arr, valOf (Int.fromString id_s),
                       TmConst (unescape thy_s, unescape name_s,
                                valOf (Int.fromString ty_s)))
      | (_ :: id_s :: "A" :: f_s :: x_s :: _) =>
          Array.update(arr, valOf (Int.fromString id_s),
                       TmApp (valOf (Int.fromString f_s),
                              valOf (Int.fromString x_s)))
      | (_ :: id_s :: "L" :: v_s :: b_s :: _) =>
          Array.update(arr, valOf (Int.fromString id_s),
                       TmLam (valOf (Int.fromString v_s),
                              valOf (Int.fromString b_s)))
      | _ => raise ERR "parse_term_descs" ("bad line: " ^ line)
  in List.app process lines; arr end

fun make_lazy_types ty_descs =
  let
    val n = Array.length ty_descs
    val cache : Type.hol_type option Array.array = Array.array(n, NONE)
    fun get i =
      case Array.sub(cache, i) of
        SOME ty => ty
      | NONE =>
        let val ty = case Array.sub(ty_descs, i) of
              TyVar s => Type.mk_vartype s
            | TyOp (thy, name, arg_ids) =>
                let val args = map get arg_ids
                in Type.mk_thy_type {Thy=thy, Tyop=name, Args=args}
                   handle HOL_ERR _ =>
                     (Type.prim_new_type {Thy=thy, Tyop=name} (length args);
                      Type.mk_thy_type {Thy=thy, Tyop=name, Args=args})
                end
        in Array.update(cache, i, SOME ty); ty end
  in get end

fun make_lazy_terms tm_descs ty_fn =
  let
    val n = Array.length tm_descs
    val cache : Term.term option Array.array = Array.array(n, NONE)
    fun get i =
      case Array.sub(cache, i) of
        SOME tm => tm
      | NONE =>
        let val tm = case Array.sub(tm_descs, i) of
              TmVar (name, ty_id) =>
                Term.mk_var(name, ty_fn ty_id)
            | TmConst (thy, name, ty_id) =>
                let val ty = ty_fn ty_id
                in Term.mk_thy_const {Thy=thy, Name=name, Ty=ty}
                   handle HOL_ERR _ =>
                     (ignore (Term.prim_new_const {Name=name, Thy=thy} ty);
                      Term.mk_thy_const {Thy=thy, Name=name, Ty=ty})
                end
            | TmApp (f_id, x_id) =>
                Term.mk_comb(get f_id, get x_id)
            | TmLam (v_id, b_id) =>
                Term.mk_abs(get v_id, get b_id)
        in Array.update(cache, i, SOME tm); tm end
  in get end

(* -----------------------------------------------------------------------
   Replay proof steps
   ----------------------------------------------------------------------- *)

(* Ancestor context: maps (theory, name) to ancestor thm.
   Used to resolve ORACLE DISK_THM entries against actually-replayed ancestors
   instead of oracle thms. *)
fun thyname_compare ((t1,n1) : string * string, (t2,n2)) =
  case String.compare(t1,t2) of
    EQUAL => String.compare(n1,n2)
  | ord => ord
type ancestor_ctx = (string * string, Thm.thm) Redblackmap.dict
val empty_ctx : ancestor_ctx = Redblackmap.mkDict thyname_compare

fun ctx_lookup_by_name (ctx : ancestor_ctx) (thy : string)
                       (name : string) : Thm.thm option =
  Redblackmap.peek(ctx, (thy, name))

(* Add exports to an ancestor context, keyed by (theory, name) *)
fun ctx_add_exports (ctx : ancestor_ctx) (thy : string)
                    (exports : (string * Thm.thm) list) : ancestor_ctx =
  List.foldl (fn ((name, th), ctx) =>
    Redblackmap.insert(ctx, (thy, name), th)) ctx exports

fun replay_steps (tm : int -> Term.term) (ty : int -> Type.hol_type)
                 (lines : string list)
                 (ctx : ancestor_ctx) =
  let
    val _ = first_fail := NONE
    val n = length lines
    val placeholder = Thm.mk_oracle_thm "PLACEHOLDER"
                        ([], Term.mk_var("_", Type.bool))
    val thm_arr = Array.array (n, placeholder)
    fun int_of s = valOf (Int.fromString s)
    fun th i = Array.sub(thm_arr, i)

    (* Compute closure, set by COMPUTE_INIT *)
    val compute_fn = ref (NONE : (thm list -> term -> thm) option)

    (* Split step line into (rule_toks, parent_ids) at "|" *)
    fun strict_int s = case Int.fromString s of
        SOME n => n
      | NONE => raise ERR "split_at_bar" ("bad parent ID: " ^ s)
    fun split_at_bar toks =
      let
        fun go acc [] = (rev acc, [])
          | go acc ("|" :: rest) = (rev acc, map strict_int rest)
          | go acc (t :: rest) = go (t :: acc) rest
      in go [] toks end

    (* Create oracle thm from statement: concl_id nhyps hyp_ids *)
    fun mk_oracle_step tag toks =
      case toks of
        concl_s :: nhyps_s :: rest =>
          let
            val c = tm (int_of concl_s)
            val nhyps = int_of nhyps_s
            val hyp_ids = List.take(List.mapPartial Int.fromString rest, nhyps)
            val hyps = map tm hyp_ids
          in
            Thm.mk_oracle_thm tag (hyps, c)
          end
      | [concl_s] =>
          Thm.mk_oracle_thm tag ([], tm (int_of concl_s))
      | _ => raise ERR "mk_oracle_step" "bad format"

    (* Parse type substitution pairs: n redex1 residue1 ... *)
    fun parse_type_subst toks =
      let
        val n = int_of (hd toks)
        fun go _ [] acc = rev acc
          | go 0 _ acc = rev acc
          | go k (r :: s :: rest) acc =
              go (k-1) rest ({redex = ty (int_of r),
                              residue = ty (int_of s)} :: acc)
          | go _ _ _ = raise ERR "parse_type_subst" "bad pairs"
      in go n (tl toks) [] end

    (* Parse term substitution pairs: n redex1 residue1 ... *)
    fun parse_term_subst toks =
      let
        val n = int_of (hd toks)
        fun go _ [] acc = rev acc
          | go 0 _ acc = rev acc
          | go k (r :: s :: rest) acc =
              go (k-1) rest ({redex = tm (int_of r),
                              residue = tm (int_of s)} :: acc)
          | go _ _ _ = raise ERR "parse_term_subst" "bad pairs"
      in go n (tl toks) [] end

    fun process line =
      let
        val toks = tokenize line
        val (id_s, id, rule, rest) =
          case toks of
            _ :: i :: r :: rs => (i, int_of i, r, rs)
          | _ => raise ERR "replay_steps"
              ("malformed step line: " ^ String.concatWith " " toks)
        val (operands, parents) = split_at_bar rest
        fun parent n = th (List.nth(parents, n))
        fun opd n = int_of (List.nth(operands, n))
        val result = case rule of
          (* --- Pure rules: fully replayed --- *)
          "REFL" => Thm.REFL (tm (opd 0))
        | "ASSUME" => Thm.ASSUME (tm (opd 0))
        | "BETA_CONV" => Thm.BETA_CONV (tm (opd 0))
        | "ALPHA" => Thm.ALPHA (tm (opd 0)) (tm (opd 1))
        | "ABS" => Thm.ABS (tm (opd 0)) (parent 0)
        | "AP_TERM" => Thm.AP_TERM (tm (opd 0)) (parent 0)
        | "AP_THM" => Thm.AP_THM (parent 0) (tm (opd 0))
        | "DISCH" => Thm.DISCH (tm (opd 0)) (parent 0)
        | "MP" => Thm.MP (parent 0) (parent 1)
        | "SYM" => Thm.SYM (parent 0)
        | "TRANS" => Thm.TRANS (parent 0) (parent 1)
        | "MK_COMB" => Thm.MK_COMB (parent 0, parent 1)
        | "EQ_MP" => Thm.EQ_MP (parent 0) (parent 1)
        | "EQ_IMP_RULE1" => #1 (Thm.EQ_IMP_RULE (parent 0))
        | "EQ_IMP_RULE2" => #2 (Thm.EQ_IMP_RULE (parent 0))
        | "SPEC" => Thm.SPEC (tm (opd 0)) (parent 0)
        | "GEN" => Thm.GEN (tm (opd 0)) (parent 0)
        | "EXISTS" => Thm.EXISTS (tm (opd 0), tm (opd 1)) (parent 0)
        | "CHOOSE" => Thm.CHOOSE (tm (opd 0), parent 0) (parent 1)
        | "CONJ" => Thm.CONJ (parent 0) (parent 1)
        | "CONJUNCT1" => Thm.CONJUNCT1 (parent 0)
        | "CONJUNCT2" => Thm.CONJUNCT2 (parent 0)
        | "DISJ1" => Thm.DISJ1 (parent 0) (tm (opd 0))
        | "DISJ2" => Thm.DISJ2 (tm (opd 0)) (parent 0)
        | "DISJ_CASES" => Thm.DISJ_CASES (parent 0) (parent 1) (parent 2)
        | "NOT_INTRO" => Thm.NOT_INTRO (parent 0)
        | "NOT_ELIM" => Thm.NOT_ELIM (parent 0)
        | "CCONTR" => Thm.CCONTR (tm (opd 0)) (parent 0)
        | "INST" => Thm.INST (parse_term_subst operands) (parent 0)
        | "INST_TYPE" => Thm.INST_TYPE (parse_type_subst operands)
                                        (parent 0)
        | "SUBST" =>
            let
              val n = opd 0
              val var_ids = List.tabulate(n, fn i => opd (1 + i))
              val tmpl_id = opd (1 + n)
              val template = tm tmpl_id
              (* parents: [residue1, ..., residueN, original_thm] *)
              val orig_thm = th (List.last parents)
              val replacements = List.tabulate(n, fn i =>
                {redex = tm (List.nth(var_ids, i)),
                 residue = th (List.nth(parents, i))})
            in Thm.SUBST replacements template orig_thm end
        | "GENL" =>
            let
              val n = opd 0
              val vs = List.tabulate(n, fn i => tm (opd (1 + i)))
            in Thm.GENL vs (parent 0) end
        | "GEN_ABS" =>
            let
              val opt_s = List.nth(operands, 0)
              val opt = if opt_s = "~" then NONE
                        else SOME (tm (int_of opt_s))
              val n = int_of (List.nth(operands, 1))
              val vs = List.tabulate(n, fn i =>
                tm (int_of (List.nth(operands, 2 + i))))
            in Thm.GEN_ABS opt vs (parent 0) end
        | "Beta" => Thm.Beta (parent 0)
        | "Mk_comb" =>
            let val (_, _, mkthm) = Thm.Mk_comb (parent 0)
            in mkthm (parent 1) (parent 2) end
        | "Mk_abs" =>
            let val (_, _, mkthm) = Thm.Mk_abs (parent 0)
            in mkthm (parent 1) end
        | "Specialize" => Thm.SPEC (tm (opd 0)) (parent 0)

        (* --- Opaque steps: oracle with recorded statement --- *)
        | "ORACLE" =>
            let val tag = hd operands
                val rest = tl operands
            in
              if tag = "DISK_THM" then
                (* Format: ORACLE DISK_THM <thy> <name>
                   In per-theory traces, resolve via ancestor context.
                   In merged traces, these have been replaced by direct
                   step references and should not appear. *)
                let val thy = unescape (List.nth(rest, 0))
                    val name = unescape (List.nth(rest, 1))
                in
                  case ctx_lookup_by_name ctx thy name of
                    SOME th => th
                  | NONE => Thm.mk_oracle_thm "REPLAY_ORACLE"
                              ([], Term.mk_var(thy ^ "$" ^ name, Type.bool))
                end
              else
                mk_oracle_step tag rest
            end
        | "AXIOM" =>
            Thm.mk_axiom_thm (Nonce.mk "REPLAY", tm (opd 0))
        | "DEF_SPEC" =>
            let
              val thyname = unescape (List.nth(operands, 0))
              val n = int_of (List.nth(operands, 1))
              val cnames = List.tabulate(n, fn i =>
                unescape (List.nth(operands, 2 + i)))
              val witness = parent 0
              val has_hyps = not (null (Thm.hyp witness))
            in
              if has_hyps
              then #2 (Thm.gen_prim_specification thyname witness)
              else Thm.prim_specification thyname cnames witness
            end
        | "DEF_TYOP" =>
            let val thy = unescape (List.nth(operands, 0))
                val tyop = unescape (List.nth(operands, 1))
                val witness = parent 0
            in
              Thm.prim_type_definition ({Thy=thy, Tyop=tyop}, witness)
            end
        | "COMPUTE_INIT" =>
            (* operands: n_cval (name term_id){n_cval} cval_type_id
               num_type_id n_char (name){n_char}
               parents: char_eqn thms *)
            let
              val n_cval = opd 0
              val cval_terms = List.tabulate(n_cval, fn i =>
                (unescape (List.nth(operands, 1 + 2*i)),
                 tm (int_of (List.nth(operands, 2 + 2*i)))))
              val base = 1 + 2 * n_cval
              val cval_type = ty (int_of (List.nth(operands, base)))
              val num_type = ty (int_of (List.nth(operands, base + 1)))
              val n_char = int_of (List.nth(operands, base + 2))
              val char_names = List.tabulate(n_char, fn i =>
                unescape (List.nth(operands, base + 3 + i)))
              val char_thms = List.tabulate(n_char, fn i => parent i)
              val char_eqns = ListPair.zip(char_names, char_thms)
              val cached = Thm.compute {
                cval_terms = cval_terms,
                cval_type = cval_type,
                num_type = num_type,
                char_eqns = char_eqns
              }
            in
              compute_fn := SOME cached;
              (* COMPUTE_INIT doesn't produce a theorem;
                 store a dummy placeholder *)
              Thm.mk_oracle_thm "COMPUTE_INIT" ([], Term.mk_var("_init", Type.bool))
            end
        | "COMPUTE" =>
            (* operands: input_term_id; parents: code_eqn thms *)
            let val input = tm (opd 0)
                val code_eqs = List.tabulate(length parents, parent)
            in
              case !compute_fn of
                SOME cached => cached code_eqs input
              | NONE => raise ERR "replay_steps"
                  "COMPUTE step before COMPUTE_INIT"
            end
        | other => raise ERR "replay_steps" ("unknown rule: " ^ other)
      in
        Array.update(thm_arr, id, result)
      end
      handle e =>
        let val toks = tokenize line
            val id = Int.fromString (List.nth(toks, 1))
                       |> valOf handle _ => ~1
            val rule = List.nth(toks, 2) handle _ => "?"
            (* On failure, create a placeholder oracle thm.
               This happens when retired/transient constants create
               type mismatches in INST/SUBST/mk_comb. *)
            val fallback = Thm.mk_oracle_thm "REPLAY_FALLBACK"
                             ([], Term.mk_var("_step" ^
                                    Int.toString id, Type.bool))
            val msg = "REPLAY_FAIL step " ^ Int.toString id ^
                      " " ^ rule ^ ": " ^ General.exnMessage e
            val _ = if not (isSome (!first_fail)) then
                      first_fail := SOME msg
                    else ()
            val _ = if !replay_debug then print (msg ^ "\n")
                    else ()
        in
          Array.update(thm_arr, id, fallback)
        end

    (* Single pass: replay all steps in order.
       With lazy type/term construction, definitions are replayed before
       the types/terms they define are constructed. *)
    val _ = List.app process lines
  in
    thm_arr
  end

(* -----------------------------------------------------------------------
   Parse exports
   ----------------------------------------------------------------------- *)

fun parse_exports (lines : string list) =
  map (fn line =>
    case tokenize line of
      _ :: name :: id_s :: _ =>
        (unescape name, valOf (Int.fromString id_s))
    | toks => raise ERR "parse_exports"
        ("malformed export line: " ^ String.concatWith " " toks))
  lines

(* -----------------------------------------------------------------------
   Main entry points
   ----------------------------------------------------------------------- *)

(* Read and parse a .pftrace[.gz] file, returning categorized lines
   and parsed header. *)
fun shell_quote s =
  "'" ^ String.translate (fn #"'" => "'\\''" | c => str c) s ^ "'"

fun read_trace_file path =
  let
    val is_zst = String.isSuffix ".zst" path
    val is_gz = String.isSuffix ".gz" path
    val qpath = shell_quote path
    val (instrm, gz_proc) =
      if is_zst then
        let val proc : (TextIO.instream, TextIO.outstream) Unix.proc =
              Unix.execute("/bin/sh", ["-c", "zstd -dc -q " ^ qpath])
        in (Unix.textInstreamOf proc, SOME proc) end
      else if is_gz then
        let val proc : (TextIO.instream, TextIO.outstream) Unix.proc =
              Unix.execute("/bin/sh", ["-c", "gunzip -c " ^ qpath])
        in (Unix.textInstreamOf proc, SOME proc) end
      else (TextIO.openIn path, NONE)
    fun cleanup () =
      case gz_proc of
        SOME p =>
          let val st = Unix.reap p
          in if not (OS.Process.isSuccess st)
             then raise ERR "read_trace_file"
                    ("decompressor failed for " ^ path)
             else ()
          end
      | NONE => TextIO.closeIn instrm
    fun read_all acc =
      case TextIO.inputLine instrm of
        NONE => rev acc
      | SOME line =>
          let val l = String.substring(line, 0, size line - 1)
          in read_all (l :: acc) end
    val all_lines = read_all [] handle e => (cleanup (); raise e)
    val _ = cleanup ()

    val header_lines = List.filter
      (fn l => String.isPrefix "HOL4_PROOF_TRACE" l orelse
               String.isPrefix "THEORY " l orelse
               String.isPrefix "COUNTS " l) all_lines
    val type_lines = List.filter (fn l => String.isPrefix "Y " l) all_lines
    val term_lines = List.filter (fn l => String.isPrefix "M " l) all_lines
    val step_lines = List.filter (fn l => String.isPrefix "P " l) all_lines
    val export_lines = List.filter (fn l => String.isPrefix "E " l) all_lines

    val header = parse_header header_lines
  in
    {header = header,
     type_lines = type_lines,
     term_lines = term_lines,
     step_lines = step_lines,
     export_lines = export_lines}
  end

fun replay_file_ctx path (ctx : ancestor_ctx) =
  let
    val saved_varcomplain = Feedback.current_trace "Vartype Format Complaint"
    val _ = Feedback.set_trace "Vartype Format Complaint" 0
    fun restore () =
      Feedback.set_trace "Vartype Format Complaint" saved_varcomplain

    val result =
      let
        val {header, type_lines, term_lines, step_lines, export_lines} =
          read_trace_file path
        val Header {theory, n_types, n_terms, n_steps, ...} = header

        val _ = if length type_lines > n_types then
                  raise ERR "replay_file_ctx" ("type count " ^
                    its (length type_lines) ^ " exceeds dimension " ^
                    its n_types)
                else ()
        val _ = if length term_lines > n_terms then
                  raise ERR "replay_file_ctx" ("term count " ^
                    its (length term_lines) ^ " exceeds dimension " ^
                    its n_terms)
                else ()

        val ty_descs = parse_type_descs n_types type_lines
        val tm_descs = parse_term_descs n_terms term_lines
        val ty_fn = make_lazy_types ty_descs
        val tm_fn = make_lazy_terms tm_descs ty_fn
        val thm_arr = replay_steps tm_fn ty_fn step_lines ctx

        val exports = parse_exports export_lines
      in
        map (fn (name, step_id) =>
          (name, Array.sub(thm_arr, step_id))) exports
      end
      handle e => (restore (); raise e)
  in
    restore (); result
  end

fun replay_file path = replay_file_ctx path empty_ctx

fun verify_file path =
  let
    val replayed = replay_file path

    (* Extract theory name from filename: <thy>Theory.pftrace[.gz|.zst] *)
    val basename = OS.Path.file path
    val thyname =
      let val b = if String.isSuffix "Theory.pftrace.zst" basename
                  then String.substring(basename, 0,
                         size basename - size "Theory.pftrace.zst")
                  else if String.isSuffix "Theory.pftrace.gz" basename
                  then String.substring(basename, 0,
                         size basename - size "Theory.pftrace.gz")
                  else if String.isSuffix "Theory.pftrace" basename
                  then String.substring(basename, 0,
                         size basename - size "Theory.pftrace")
                  else raise ERR "verify_file"
                    ("cannot extract theory name from " ^ basename)
      in b end

    (* Compare each replayed export against actual theory theorem.
       Caller must ensure the theory is loaded first. *)
    val n_ok = ref 0
    val failures = ref ([] : {name: string, reason: string} list)

    fun check_export (name, replayed_thm) =
      let
        val actual_thm = DB.fetch thyname name
        val replayed_concl = Thm.concl replayed_thm
        val actual_concl = Thm.concl actual_thm
        val replayed_hyps = Thm.hyp replayed_thm
        val actual_hyps = Thm.hyp actual_thm
        val concl_ok = Term.aconv replayed_concl actual_concl
        val hyps_ok =
          length replayed_hyps = length actual_hyps andalso
          List.all (fn h =>
            List.exists (fn h' => Term.aconv h h') actual_hyps)
            replayed_hyps
      in
        if concl_ok andalso hyps_ok
        then n_ok := !n_ok + 1
        else
          let val reason =
                (if not concl_ok then "conclusion mismatch" else "") ^
                (if not hyps_ok then
                   (if not concl_ok then "; " else "") ^
                   "hypothesis mismatch (replayed " ^
                   Int.toString (length replayed_hyps) ^
                   " vs actual " ^
                   Int.toString (length actual_hyps) ^ ")"
                 else "")
          in failures := {name=name, reason=reason} :: !failures end
      end
      handle e =>
        failures := {name=name,
                     reason="exception: " ^ exn_to_string e} :: !failures
  in
    List.app check_export replayed;
    (!n_ok, rev (!failures))
  end

fun verify_verbose path =
  let
    val _ = print ("Verifying: " ^ path ^ " ... ")
    val (n_ok, failures) = verify_file path
  in
    if null failures then
      (print ("OK (" ^ Int.toString n_ok ^ " thms)\n"); true)
    else
      (print ("FAIL: " ^ Int.toString (length failures) ^ "/" ^
              Int.toString (n_ok + length failures) ^ " exports failed\n");
       List.app (fn {name, reason} =>
         print ("  " ^ name ^ ": " ^ reason ^ "\n")) failures;
       false)
  end
  handle e =>
    (print ("ERROR [" ^ exnName e ^ "]: " ^
            General.exnMessage e ^ "\n"); false)

(* Find all .pftrace files under a directory.
   Preference order: .pftrace.zst > .pftrace.gz > .pftrace *)
fun find_traces dir =
  let
    fun walk d acc =
      let
        val ds = OS.FileSys.openDir d
        fun loop acc =
          case OS.FileSys.readDir ds of
            NONE => (OS.FileSys.closeDir ds; acc)
          | SOME entry =>
            let val p = OS.Path.concat(d, entry)
            in
              if OS.FileSys.isDir p
              then loop (walk p acc)
              else if String.isSuffix "Theory.pftrace.zst" entry
              then
                let
                  val thy = String.substring(entry, 0,
                              size entry - size "Theory.pftrace.zst")
                in loop ((thy, p) :: acc) end
              else if String.isSuffix "Theory.pftrace.gz" entry
              then
                let
                  val thy = String.substring(entry, 0,
                              size entry - size "Theory.pftrace.gz")
                in loop ((thy, p) :: acc) end
              else if String.isSuffix "Theory.pftrace" entry
              then
                let
                  val thy = String.substring(entry, 0,
                              size entry - size "Theory.pftrace")
                in loop ((thy, p) :: acc) end
              else loop acc
            end
      in loop acc end
    (* Deduplicate: if both .zst and .gz exist, keep .zst *)
    val all = walk dir []
    val m = List.foldl (fn ((thy, path), m) =>
      case Redblackmap.peek(m, thy) of
        SOME existing =>
          if String.isSuffix ".zst" path andalso
             not (String.isSuffix ".zst" existing)
          then Redblackmap.insert(m, thy, path)
          else if String.isSuffix ".gz" path andalso
                  String.isSuffix ".pftrace" existing andalso
                  not (String.isSuffix ".gz" existing) andalso
                  not (String.isSuffix ".zst" existing)
          then Redblackmap.insert(m, thy, path)
          else m
      | NONE => Redblackmap.insert(m, thy, path))
      (Redblackmap.mkDict String.compare) all
  in
    Redblackmap.listItems m
  end

fun verify_all dir =
  let
    val traces = find_traces dir
    val _ = print ("Found " ^ Int.toString (length traces) ^
                   " .pftrace files\n")
    val n_ok = ref 0
    val n_fail = ref 0
    val errors = ref ([] : string list)
  in
    List.app (fn (thy, path) =>
      if verify_verbose path
      then n_ok := !n_ok + 1
      else (n_fail := !n_fail + 1;
            errors := (thy ^ ": " ^ path) :: !errors))
      traces;
    print ("\n=== Summary: " ^ Int.toString (!n_ok) ^ " OK, " ^
           Int.toString (!n_fail) ^ " FAILED ===\n");
    if not (null (!errors)) then
      (print "Failed theories:\n";
       List.app (fn e => print ("  " ^ e ^ "\n")) (rev (!errors)))
    else ();
    {ok = !n_ok, fail = !n_fail, errors = rev (!errors)}
  end

(* -----------------------------------------------------------------------
   Chain verification: replay a theory and all its ancestors from
   .pftrace.gz files, without requiring theories loaded in HOL session.
   Ancestors are replayed in topological order and their exports are
   passed as context for ORACLE DISK_THM entries in descendant theories.
   ----------------------------------------------------------------------- *)

(* verify_chain is removed — use the merge tool + from-scratch replay instead *)
fun verify_chain _ _ =
  (print "verify_chain is no longer supported.\n\
         \Use the merge tool to produce a self-contained trace,\n\
         \then replay from scratch.\n";
   {ok = 0, fail = 0, errors = ["verify_chain removed"]})

fun parse_trace_stats path =
  let val {type_lines, term_lines, step_lines, export_lines, ...} =
        read_trace_file path
  in {n_types = length type_lines, n_terms = length term_lines,
      n_steps = length step_lines, n_exports = length export_lines}
  end

end (* structure *)
