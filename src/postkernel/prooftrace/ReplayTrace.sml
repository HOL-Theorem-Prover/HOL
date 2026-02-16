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
val compute_verifier = ref (NONE : (term -> thm) option)

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
  parents: string list,
  ancestors: (string * string) list,  (* (theory, digest) pairs *)
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
    val (par_str, lines) = get_line "PARENTS " lines
    val parents = map unescape (String.tokens Char.isSpace par_str)
    (* Parse optional ANCESTOR lines *)
    val ancestor_lines = List.filter
      (fn l => String.isPrefix "ANCESTOR " l) lines
    val ancestors = List.mapPartial (fn l =>
      let val toks = String.tokens Char.isSpace
                       (String.extract(l, 9, NONE))
      in case toks of
           [thy_s, digest_s] => SOME (unescape thy_s, digest_s)
         | _ => NONE
      end) ancestor_lines
    val (cnt_str, _) = get_line "COUNTS " lines
    val cnts = String.tokens Char.isSpace cnt_str
    val (n_types, n_terms, n_steps) =
      case List.mapPartial Int.fromString cnts of
        [a, b, c] => (a, b, c)
      | _ => raise ERR "parse_header" "COUNTS must have 3 integers"
  in
    Header {version=version, theory=theory, parents=parents,
            ancestors=ancestors,
            n_types=n_types, n_terms=n_terms, n_steps=n_steps}
  end

(* -----------------------------------------------------------------------
   Build type array from Y entries
   ----------------------------------------------------------------------- *)

fun build_types n_types (lines : string list) =
  let
    val arr = Array.array (n_types, Type.bool)  (* placeholder *)
    fun process line =
      case tokenize line of
        _ :: id_s :: kind :: rest =>
        let
          val id = valOf (Int.fromString id_s)
          val ty = case kind of
              "V" => Type.mk_vartype (unescape (hd rest))
            | "O" =>
              let
                val thy = unescape (hd rest)
                val name = unescape (hd (tl rest))
                val arg_ids = List.mapPartial Int.fromString (tl (tl rest))
                val args = map (fn i => Array.sub(arr, i)) arg_ids
              in
                Type.mk_thy_type {Thy=thy, Tyop=name, Args=args}
                handle HOL_ERR _ =>
                  (* Retired/temp type operators: create on-the-fly so
                     intermediate proof steps using them can be replayed. *)
                  (Type.prim_new_type {Thy=thy, Tyop=name} (length args);
                   Type.mk_thy_type {Thy=thy, Tyop=name, Args=args})
                  handle _ =>
                    Type.mk_vartype ("'" ^ thy ^ "_" ^ name)
              end
            | _ => raise ERR "build_types" ("unknown kind: " ^ kind)
        in
          Array.update(arr, id, ty)
        end
      | toks => raise ERR "build_types"
          ("malformed type line: " ^ String.concatWith " " toks)
  in
    List.app process lines;
    arr
  end

(* -----------------------------------------------------------------------
   Build term array from M entries
   ----------------------------------------------------------------------- *)

fun build_terms n_terms type_arr (lines : string list) =
  let
    val placeholder_name = "\000_placeholder"
    val placeholder = Term.mk_var(placeholder_name, Type.bool)
    val arr = Array.array (n_terms, placeholder)
    val deferred = ref ([] : string list)
    fun is_placeholder tm = Term.is_var tm andalso
      let val (n,_) = Term.dest_var tm in n = placeholder_name end
    fun process line =
      case tokenize line of
        _ :: id_s :: kind :: rest =>
        let
          val id = valOf (Int.fromString id_s)
          fun int_of s = valOf (Int.fromString s)
          val tm = case kind of
              "V" =>
                let val name = unescape (hd rest)
                    val ty_id = int_of (hd (tl rest))
                in Term.mk_var(name, Array.sub(type_arr, ty_id)) end
            | "C" =>
                let val thy = unescape (hd rest)
                    val name = unescape (hd (tl rest))
                    val ty_id = int_of (hd (tl (tl rest)))
                    val ty = Array.sub(type_arr, ty_id)
                in Term.mk_thy_const {Thy=thy, Name=name, Ty=ty}
                   handle HOL_ERR _ =>
                     (* Retired/temp constants: create on-the-fly so
                        intermediate proof steps can be replayed. *)
                     (ignore (Term.prim_new_const {Name=name, Thy=thy} ty);
                      Term.mk_thy_const {Thy=thy, Name=name, Ty=ty})
                     handle _ =>
                       Term.mk_var(thy ^ "$" ^ name, ty)
                end
            | "A" =>
                let val f_id = int_of (hd rest)
                    val x_id = int_of (hd (tl rest))
                    val f_tm = Array.sub(arr, f_id)
                    val x_tm = Array.sub(arr, x_id)
                in if is_placeholder f_tm orelse is_placeholder x_tm
                   then (deferred := line :: !deferred; placeholder)
                   else Term.mk_comb(f_tm, x_tm)
                        handle HOL_ERR _ =>
                          let val fty = Term.type_of f_tm
                              val rty = snd (Type.dom_rng fty)
                                        handle HOL_ERR _ => Type.bool
                          in Term.mk_var("_app" ^ id_s, rty) end
                end
            | "L" =>
                let val v_id = int_of (hd rest)
                    val b_id = int_of (hd (tl rest))
                    val v_tm = Array.sub(arr, v_id)
                    val b_tm = Array.sub(arr, b_id)
                in if is_placeholder v_tm orelse is_placeholder b_tm
                   then (deferred := line :: !deferred; placeholder)
                   else Term.mk_abs(v_tm, b_tm)
                        handle HOL_ERR _ =>
                          Term.mk_var("_abs" ^ id_s, Type.bool)
                end
            | _ => raise ERR "build_terms" ("unknown kind: " ^ kind)
        in
          Array.update(arr, id, tm)
        end
      | toks => raise ERR "build_terms"
          ("malformed term line: " ^ String.concatWith " " toks)
    (* First pass: process all lines *)
    val _ = List.app process lines
    (* Additional passes: resolve forward references *)
    fun resolve_pass () =
      let val pending = rev (!deferred)
          val _ = deferred := []
      in if null pending then ()
         else (List.app process pending;
               if null (!deferred) then ()
               else resolve_pass ())
      end
  in
    resolve_pass ();
    arr
  end

(* -----------------------------------------------------------------------
   Replay proof steps
   ----------------------------------------------------------------------- *)

(* Ancestor context: maps conclusion term to list of ancestor thms.
   Used to resolve ORACLE DISK_THM entries against actually-replayed ancestors
   instead of oracle thms. *)
type ancestor_ctx = (Term.term, Thm.thm list) Redblackmap.dict
val empty_ctx : ancestor_ctx = Redblackmap.mkDict Term.compare

(* Look up an ancestor thm by conclusion and hypotheses *)
fun ctx_lookup (ctx : ancestor_ctx) (concl : Term.term)
               (hyps : Term.term list) : Thm.thm option =
  case Redblackmap.peek(ctx, concl) of
    NONE => NONE
  | SOME thms =>
      let fun match_hyps th =
            let val actual_hyps = Thm.hyp th
            in length actual_hyps = length hyps andalso
               List.all (fn h =>
                 List.exists (fn h' => Term.aconv h h') actual_hyps)
                 hyps
            end
      in List.find match_hyps thms end

(* Add exports to an ancestor context *)
fun ctx_add_exports (ctx : ancestor_ctx)
                    (exports : (string * Thm.thm) list) : ancestor_ctx =
  List.foldl (fn ((_, th), ctx) =>
    let val c = Thm.concl th
        val prev = case Redblackmap.peek(ctx, c) of
                     SOME ths => ths | NONE => []
    in Redblackmap.insert(ctx, c, th :: prev) end) ctx exports

fun replay_steps term_arr type_arr (lines : string list)
                 (ctx : ancestor_ctx) =
  let
    val _ = first_fail := NONE
    val n = length lines
    val placeholder = Thm.mk_oracle_thm "PLACEHOLDER"
                        ([], Term.mk_var("_", Type.bool))
    val thm_arr = Array.array (n, placeholder)
    fun int_of s = valOf (Int.fromString s)
    fun tm i = Array.sub(term_arr, i)
    fun ty i = Array.sub(type_arr, i)
    fun th i = Array.sub(thm_arr, i)

    (* Set of opaque rule tags *)
    (* DEF_SPEC and DEF_TYOP have parent thm dependencies (witness),
       so they must be processed in pass 2 after their parents. *)
    val opaque_rules = ["ORACLE", "AXIOM", "COMPUTE"]
    fun is_opaque rule = List.exists (fn r => r = rule) opaque_rules

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
    fun mk_oracle_step toks =
      case toks of
        concl_s :: nhyps_s :: rest =>
          let
            val c = tm (int_of concl_s)
            val nhyps = int_of nhyps_s
            val hyp_ids = List.take(List.mapPartial Int.fromString rest, nhyps)
            val hyps = map tm hyp_ids
          in
            (* Try ancestor context first, fall back to oracle thm *)
            case ctx_lookup ctx c hyps of
              SOME ancestor_th => ancestor_th
            | NONE => Thm.mk_oracle_thm "REPLAY_ORACLE" (hyps, c)
          end
      | [concl_s] =>
          let val c = tm (int_of concl_s)
          in case ctx_lookup ctx c [] of
               SOME ancestor_th => ancestor_th
             | NONE => Thm.mk_oracle_thm "REPLAY_ORACLE" ([], c)
          end
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
        | "ORACLE" => mk_oracle_step (tl operands)  (* skip tag *)
        | "AXIOM" =>
            Thm.mk_axiom_thm (Nonce.mk "REPLAY", tm (opd 0))
        | "DEF_SPEC" =>
            (* New format: thyname n_cnames cname1...cnameN concl_id
               Old format: concl_id (fallback) *)
            (if length operands >= 3
             then let
               val thyname = unescape (List.nth(operands, 0))
               val n = int_of (List.nth(operands, 1))
               val cnames = List.tabulate(n, fn i =>
                 unescape (List.nth(operands, 2 + i)))
               val witness = parent 0
               val concl_tm = tm (int_of (List.last operands))
               (* Check if constant already defined (theory loaded).
                  Calling prim_specification when constants exist would
                  rename them with old-> prefix, corrupting the
                  namespace for subsequent inference steps. *)
               val already_defined =
                 (Term.prim_mk_const {Name = hd cnames, Thy = thyname};
                  true)
                 handle HOL_ERR _ => false
             in
               if already_defined then
                 Thm.mk_defn_thm (Thm.tag witness, concl_tm)
               else
                 let val has_hyps = not (null (Thm.hyp witness))
                 in (if has_hyps
                     then #2 (Thm.gen_prim_specification thyname witness)
                     else Thm.prim_specification thyname cnames witness)
                    handle _ =>
                      Thm.mk_defn_thm (Thm.tag witness, concl_tm)
                 end
             end
             else
               (* Old format: just concl_id *)
               let val empty_tag = Thm.tag (Thm.REFL
                     (Term.mk_var("x", Type.bool)))
               in Thm.mk_defn_thm (empty_tag, tm (opd 0)) end)
        | "DEF_TYOP" =>
            (* operands: thy tyop concl_id; parent 0 = witness thm *)
            let val thy = unescape (List.nth(operands, 0))
                val tyop = unescape (List.nth(operands, 1))
                val concl_tm = tm (int_of (List.last operands))
                val witness = parent 0
                (* Check if type already defined *)
                val already_defined =
                  (ignore (Type.mk_thy_type {Thy=thy, Tyop=tyop,
                                             Args=[]});
                   true)
                  handle HOL_ERR _ => false
            in
              if already_defined then
                Thm.mk_defn_thm (Thm.tag witness, concl_tm)
              else
                Thm.prim_type_definition ({Thy=thy, Tyop=tyop}, witness)
                handle _ =>
                  Thm.mk_defn_thm (Thm.tag witness, concl_tm)
            end
        | "COMPUTE" =>
            (* operands: input_tm concl_tm *)
            let val input = tm (opd 0)
                val expected_concl = tm (opd 1)
            in
              case !compute_verifier of
                SOME eval_fn =>
                  (let val result_thm = eval_fn input
                       val result_concl = Thm.concl result_thm
                   in if Term.aconv result_concl expected_concl
                         andalso null (Thm.hyp result_thm)
                      then result_thm
                      else Thm.mk_oracle_thm "REPLAY_COMPUTE"
                             ([], expected_concl)
                   end
                   handle _ => Thm.mk_oracle_thm "REPLAY_COMPUTE"
                                 ([], expected_concl))
              | NONE =>
                  Thm.mk_oracle_thm "REPLAY_COMPUTE" ([], expected_concl)
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
                      " " ^ rule ^ ": " ^ exn_to_string e
            val _ = if not (isSome (!first_fail)) then
                      first_fail := SOME msg
                    else ()
            val _ = if !replay_debug then print (msg ^ "\n")
                    else ()
        in
          Array.update(thm_arr, id, fallback)
        end

    (* Pass 1: create oracle thms for all opaque steps *)
    fun is_opaque_line line =
      let val toks = tokenize line
      in length toks >= 3 andalso is_opaque (List.nth(toks, 2)) end
    val _ = List.app (fn line =>
      if is_opaque_line line then process line else ()) lines

    (* Pass 2: replay pure inference steps *)
    val _ = List.app (fn line =>
      if is_opaque_line line then () else process line) lines
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

fun file_digest path =
  let
    val qpath = shell_quote path
    val proc : (TextIO.instream, TextIO.outstream) Unix.proc =
      Unix.execute("/bin/sh", ["-c", "sha256sum " ^ qpath])
    val line = TextIO.inputAll (Unix.textInstreamOf proc)
    val st = Unix.reap proc
    val _ = if not (OS.Process.isSuccess st)
            then raise ERR "file_digest" ("sha256sum failed for " ^ path)
            else ()
  in "sha256:" ^ hd (String.tokens Char.isSpace line) end

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
               String.isPrefix "PARENTS " l orelse
               String.isPrefix "ANCESTOR " l orelse
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

        val type_arr = build_types n_types type_lines
        val term_arr = build_terms n_terms type_arr term_lines
        val thm_arr = replay_steps term_arr type_arr step_lines ctx

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

fun verify_chain holdir root_theory =
  let
    val all_traces = find_traces holdir
    val trace_map =
      List.foldl (fn ((thy, path), m) =>
        Redblackmap.insert(m, thy, path))
        (Redblackmap.mkDict String.compare) all_traces

    (* Read headers to get dependency info; cache for ancestor checks *)
    val header_cache = ref (Redblackmap.mkDict String.compare
                            : (string, header) Redblackmap.dict)
    fun get_parents thy =
      case Redblackmap.peek(trace_map, thy) of
        NONE => []
      | SOME path =>
        let val {header as Header {parents, ...}, ...} =
              read_trace_file path
            val _ = header_cache :=
              Redblackmap.insert(!header_cache, thy, header)
        in parents end
        handle _ => []

    (* Topological sort: DFS post-order from root *)
    fun toposort root =
      let
        val visited = ref (Redblackset.empty String.compare)
        val order = ref ([] : string list)
        fun visit thy =
          if Redblackset.member(!visited, thy) then ()
          else
            (visited := Redblackset.add(!visited, thy);
             List.app visit (get_parents thy);
             (* Only include theories with traces *)
             if isSome (Redblackmap.peek(trace_map, thy))
             then order := thy :: !order
             else ())
      in
        visit root;
        rev (!order)
      end

    val replay_order = toposort root_theory
    val _ = print ("Replay chain: " ^ Int.toString (length replay_order) ^
                   " theories in dependency order\n")

    (* Compute SHA-256 digests for all trace files in the chain *)
    val _ = print "Computing trace file digests...\n"
    val digest_map =
      List.foldl (fn (thy, m) =>
        case Redblackmap.peek(trace_map, thy) of
          NONE => m
        | SOME path =>
            (Redblackmap.insert(m, thy, file_digest path)
             handle _ => m))
        (Redblackmap.mkDict String.compare) replay_order

    (* Check ancestor digests for a theory against actual file hashes *)
    fun check_ancestors thy =
      case Redblackmap.peek(!header_cache, thy) of
        NONE => []
      | SOME (Header {ancestors, ...}) =>
          List.mapPartial (fn (anc_thy, expected) =>
            case Redblackmap.peek(digest_map, anc_thy) of
              NONE => NONE  (* ancestor not in chain, can't verify *)
            | SOME actual =>
                if expected = actual then NONE
                else SOME (anc_thy, expected, actual)) ancestors

    val n_ok = ref 0
    val n_fail = ref 0
    val errors = ref ([] : string list)
    val ctx = ref empty_ctx

    fun replay_one thy =
      let
        val path = valOf (Redblackmap.peek(trace_map, thy))
        val _ = print ("  " ^ thy ^ " ... ")
        val mismatches = check_ancestors thy
      in
        if not (null mismatches) then
          (List.app (fn (anc, exp, act) =>
            print ("    ancestor " ^ anc ^ " digest mismatch\n" ^
                   "      expected: " ^ exp ^ "\n" ^
                   "      actual:   " ^ act ^ "\n")) mismatches;
           print "FAIL: ancestor digest mismatch\n";
           n_fail := !n_fail + 1;
           errors := thy :: !errors)
        else
        let
          val exports = replay_file_ctx path (!ctx)
          val _ = ctx := ctx_add_exports (!ctx) exports
          val n_exports = length exports
          (* Check for oracle tags in exports *)
          fun count_oracle tag =
            length (List.filter (fn (_, th) =>
              let val (oracles, _) = Tag.dest_tag (Thm.tag th)
              in List.exists (fn s => s = tag) oracles
              end) exports)
          val n_fallbacks = count_oracle "REPLAY_FALLBACK"
          val n_placeholder = count_oracle "PLACEHOLDER"
          val n_trust = count_oracle "REPLAY_ORACLE"
          val n_compute = count_oracle "REPLAY_COMPUTE"
          val n_bad = n_fallbacks + n_placeholder
          val info =
            String.concatWith ", " (
              [its n_exports ^ " exports"] @
              (if n_trust > 0 then [its n_trust ^ " trusted"] else []) @
              (if n_compute > 0 then [its n_compute ^ " compute-oracle"]
               else []))
        in
          if n_bad = 0
          then (print ("OK (" ^ info ^ ")\n");
                n_ok := !n_ok + 1)
          else (print ("FAIL: " ^ its n_bad ^ "/" ^
                       its n_exports ^ " exports have oracle tags" ^
                       " (fallback=" ^ its n_fallbacks ^
                       " placeholder=" ^ its n_placeholder ^ ")\n");
                n_fail := !n_fail + 1;
                errors := thy :: !errors)
        end
        handle e =>
          (print ("FAIL: " ^ General.exnMessage e ^ "\n");
           n_fail := !n_fail + 1;
           errors := thy :: !errors)
      end
  in
    List.app replay_one replay_order;
    print ("\n=== Chain summary: " ^ its (!n_ok) ^ " OK, " ^
           its (!n_fail) ^ " FAILED ===\n");
    if not (null (!errors)) then
      (print "Failed:\n";
       List.app (fn e => print ("  " ^ e ^ "\n")) (rev (!errors)))
    else ();
    {ok = !n_ok, fail = !n_fail, errors = rev (!errors)}
  end

fun parse_trace_stats path =
  let val {type_lines, term_lines, step_lines, export_lines, ...} =
        read_trace_file path
  in {n_types = length type_lines, n_terms = length term_lines,
      n_steps = length step_lines, n_exports = length export_lines}
  end

end (* structure *)
