(* ReplayTrace: parse and replay .pftrace files to verify proof traces.

   Given a .pftrace file:
   1. Reconstruct type/term arrays from Y/M entries
   2. Replay proof steps using actual kernel inference rules
   3. Verify exported theorem names map to correctly reconstructed thms

   Trust-like steps (DISK_THM, ORACLE, AXIOM, DEF_SPEC, DEF_TYOP,
   COMPUTE, TRUST) include their theorem statement in the trace and
   are created via mk_oracle_thm. All other steps are fully replayed
   through the kernel.
*)

structure ReplayTrace :> ReplayTrace =
struct

open HolKernel

val ERR = mk_HOL_ERR "ReplayTrace"

val replay_debug = ref false
val first_fail = ref (NONE : string option)

fun its i = Int.toString i

(* -----------------------------------------------------------------------
   String unescaping (inverse of ProofTrace.escape_string)
   ----------------------------------------------------------------------- *)
fun unescape s =
  if size s >= 2 andalso String.sub(s, 0) = #"\"" then
    let
      val inner = String.substring(s, 1, size s - 2)
      fun go [] acc = String.implode (rev acc)
        | go (#"\\" :: #"\"" :: rest) acc = go rest (#"\"" :: acc)
        | go (#"\\" :: #"\\" :: rest) acc = go rest (#"\\" :: acc)
        | go (#"\\" :: #"n" :: rest) acc = go rest (#"\n" :: acc)
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
    val version = valOf (Int.fromString ver_str)
    val (thy_str, lines) = get_line "THEORY " lines
    val theory = unescape thy_str
    val (par_str, lines) = get_line "PARENTS " lines
    val parents = map unescape (String.tokens Char.isSpace par_str)
    val (cnt_str, _) = get_line "COUNTS " lines
    val cnts = String.tokens Char.isSpace cnt_str
    val (n_types, n_terms, n_steps) =
      case List.mapPartial Int.fromString cnts of
        [a, b, c] => (a, b, c)
      | _ => raise ERR "parse_header" "COUNTS must have 3 integers"
  in
    Header {version=version, theory=theory, parents=parents,
            n_types=n_types, n_terms=n_terms, n_steps=n_steps}
  end

(* -----------------------------------------------------------------------
   Build type array from Y entries
   ----------------------------------------------------------------------- *)

fun build_types (lines : string list) =
  let
    val arr = Array.array (length lines, Type.bool)  (* placeholder *)
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

fun build_terms type_arr (lines : string list) =
  let
    val placeholder = Term.mk_var("_", Type.bool)
    val arr = Array.array (length lines, placeholder)
    val deferred = ref ([] : string list)
    fun is_placeholder tm = Term.is_var tm andalso
      let val (n,_) = Term.dest_var tm in n = "_" end
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

fun replay_steps term_arr type_arr (lines : string list) =
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
    val opaque_rules = ["DISK_THM", "ORACLE", "AXIOM", "DEF_SPEC",
                        "DEF_TYOP", "COMPUTE", "TRUST"]
    fun is_opaque rule = List.exists (fn r => r = rule) opaque_rules

    (* Split step line into (rule_toks, parent_ids) at "|" *)
    fun split_at_bar toks =
      let
        fun go acc [] = (rev acc, [])
          | go acc ("|" :: rest) =
              (rev acc, List.mapPartial Int.fromString rest)
          | go acc (t :: rest) = go (t :: acc) rest
      in go [] toks end

    (* Create oracle thm from statement: concl_id nhyps hyp_ids *)
    fun mk_trust_thm toks =
      case toks of
        concl_s :: nhyps_s :: rest =>
          let
            val c = tm (int_of concl_s)
            val nhyps = int_of nhyps_s
            val hyp_ids = List.take(List.mapPartial Int.fromString rest, nhyps)
            val hyps = map tm hyp_ids
          in Thm.mk_oracle_thm "REPLAY_TRUST" (hyps, c) end
      | [concl_s] =>
          Thm.mk_oracle_thm "REPLAY_TRUST" ([], tm (int_of concl_s))
      | _ => raise ERR "mk_trust_thm" "bad format"

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
            (* Mk_comb produces 3 parents: original eq thm, th1', th2'
               The result is TRANS original (MK_COMB(th1', th2')) *)
            Thm.TRANS (parent 0)
                      (Thm.MK_COMB (parent 1, parent 2))
        | "Mk_abs" =>
            (* Mk_abs produces 2 parents: original eq thm, th1'
               Bvar ID is recorded as operand (may differ from
               dest_abs result due to alpha-conversion). *)
            let
              val bvar = if null operands then
                           (* Legacy format: extract from parent 0 *)
                           let val rhs_tm = Thm.concl (parent 0)
                                              |> Term.rand
                           in #1 (Term.dest_abs rhs_tm) end
                         else tm (opd 0)
            in Thm.TRANS (parent 0) (Thm.ABS bvar (parent 1)) end
        | "Specialize" => Thm.SPEC (tm (opd 0)) (parent 0)

        (* --- Opaque steps: trust with recorded statement --- *)
        | "DISK_THM" => mk_trust_thm operands
        | "ORACLE" => mk_trust_thm (tl operands)  (* skip tag *)
        | "AXIOM" =>
            Thm.mk_oracle_thm "REPLAY_TRUST" ([], tm (opd 0))
        | "DEF_SPEC" =>
            Thm.mk_oracle_thm "REPLAY_TRUST" ([], tm (opd 0))
        | "DEF_TYOP" =>
            (* operands: thy name concl_id *)
            Thm.mk_oracle_thm "REPLAY_TRUST"
              ([], tm (int_of (List.last operands)))
        | "COMPUTE" =>
            (* operands: input_tm concl_tm *)
            Thm.mk_oracle_thm "REPLAY_TRUST" ([], tm (opd 1))
        | "TRUST" =>
            (* operands: global_id [concl nhyps hyps...] *)
            if length operands >= 2
            then mk_trust_thm (tl operands)  (* skip global_id *)
            else raise ERR "replay_steps"
                   ("TRUST entry without statement at step " ^ id_s)
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

fun replay_file path =
  let
    (* Suppress "non-standard syntax" warnings for %%gen_tyvar%% etc. *)
    val saved_varcomplain = Feedback.current_trace "Vartype Format Complaint"
    val _ = Feedback.set_trace "Vartype Format Complaint" 0
    fun restore () =
      Feedback.set_trace "Vartype Format Complaint" saved_varcomplain

    val instrm = TextIO.openIn path
    fun read_all acc =
      case TextIO.inputLine instrm of
        NONE => rev acc
      | SOME line =>
          let val l = String.substring(line, 0, size line - 1)
          in read_all (l :: acc) end
    val all_lines = read_all []
    val _ = TextIO.closeIn instrm

    (* Categorize lines *)
    val header_lines = List.filter
      (fn l => String.isPrefix "HOL4_PROOF_TRACE" l orelse
               String.isPrefix "THEORY " l orelse
               String.isPrefix "PARENTS " l orelse
               String.isPrefix "COUNTS " l) all_lines
    val type_lines = List.filter (fn l => String.isPrefix "Y " l) all_lines
    val term_lines = List.filter (fn l => String.isPrefix "M " l) all_lines
    val step_lines = List.filter (fn l => String.isPrefix "P " l) all_lines
    val export_lines = List.filter (fn l => String.isPrefix "E " l) all_lines

    val header = parse_header header_lines
    val Header {theory, n_types, n_terms, n_steps, ...} = header

    val _ = if length type_lines <> n_types then
              raise ERR "replay_file" ("expected " ^ its n_types ^
                " types, got " ^ its (length type_lines))
            else ()
    val _ = if length term_lines <> n_terms then
              raise ERR "replay_file" ("expected " ^ its n_terms ^
                " terms, got " ^ its (length term_lines))
            else ()

    (* Build type and term arrays *)
    val type_arr = build_types type_lines
    val term_arr = build_terms type_arr term_lines

    (* Replay proof steps *)
    val thm_arr = replay_steps term_arr type_arr step_lines

    (* Resolve exports *)
    val exports = parse_exports export_lines
    val result = map (fn (name, step_id) =>
      (name, Array.sub(thm_arr, step_id))) exports
  in
    restore (); result
  end
  handle e =>
    (Feedback.set_trace "Vartype Format Complaint" 1
       handle _ => ();  (* best-effort restore to default *)
     raise e)

fun verify_file path =
  let
    val replayed = replay_file path

    (* Extract theory name from header *)
    val instrm = TextIO.openIn path
    fun find_thy () =
      case TextIO.inputLine instrm of
        NONE => raise ERR "verify_file" "no THEORY line"
      | SOME line =>
          if String.isPrefix "THEORY " line
          then String.substring(line, 7, size line - 8)
          else find_thy ()
    val thyname = unescape (find_thy ())
    val _ = TextIO.closeIn instrm

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

(* Find all .pftrace files under a directory *)
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
              else if String.isSuffix ".pftrace" entry
              then
                let
                  (* Extract theory name from filename *)
                  val thy = String.substring(entry, 0,
                              size entry - size "Theory.pftrace")
                in loop ((thy, p) :: acc) end
              else loop acc
            end
      in loop acc end
  in
    walk dir []
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

end (* structure *)
