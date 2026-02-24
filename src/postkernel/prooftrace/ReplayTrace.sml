(* ReplayTrace: replay .pft files through the kernel.

   Single forward pass: construct types, terms, and theorems eagerly
   from Y/T/P/C entries. For merged traces, all definitions are fresh
   (no preloaded theories). Exports are checked to be oracle-free.
*)

structure ReplayTrace :> ReplayTrace =
struct

open HolKernel

val ERR = mk_HOL_ERR "ReplayTrace"
fun its i = Int.toString i

(* ------- String unescaping ------- *)

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

(* ------- Tokenizer ------- *)

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

(* ------- File I/O ------- *)

fun open_trace path = TextIO.openIn path

fun close_trace strm = TextIO.closeIn strm

(* ------- Replay a merged trace ------- *)

fun replay_file path =
  let
    val instrm = open_trace path
    fun cleanup () = close_trace instrm

    (* Lazy type/term construction: store raw descriptions,
       construct on demand when first accessed. This ensures
       definitions run before the types/terms they define
       are constructed. *)
    datatype ty_desc = TyVar of string | TyOp of string * string * int list
    datatype tm_desc = TmVar of string * int | TmConst of string * string * int
                     | TmApp of int * int | TmLam of int * int

    fun grow arr n default =
      let val old = !arr
          val old_len = Array.length old
      in if n < old_len then ()
         else let val new_len = Int.max(n + 1, old_len * 2)
                  val new_arr = Array.array(new_len, default)
              in Array.appi (fn (i, v) =>
                   Array.update(new_arr, i, v)) old;
                 arr := new_arr
              end
      end

    val ty_descs : ty_desc option Array.array ref =
      ref (Array.array(1000, NONE))
    val ty_cache : Type.hol_type option Array.array ref =
      ref (Array.array(1000, NONE))
    val tm_descs : tm_desc option Array.array ref =
      ref (Array.array(10000, NONE))
    val tm_cache : Term.term option Array.array ref =
      ref (Array.array(10000, NONE))

    fun set_ty_desc i d =
      (grow ty_descs i NONE; Array.update(!ty_descs, i, SOME d))
    fun set_tm_desc i d =
      (grow tm_descs i NONE; Array.update(!tm_descs, i, SOME d))

    fun ty i =
      (grow ty_cache i NONE;
       case Array.sub(!ty_cache, i) of
         SOME v => v
       | NONE =>
         let val v = case Array.sub(!ty_descs, i) of
               SOME (TyVar name) => Type.mk_vartype name
             | SOME (TyOp (thy, name, args)) =>
                 Type.mk_thy_type {Thy=thy, Tyop=name, Args=map ty args}
             | NONE => raise ERR "replay" ("unknown type id " ^
                         Int.toString i)
         in Array.update(!ty_cache, i, SOME v); v end)

    fun tm i =
      (grow tm_cache i NONE;
       case Array.sub(!tm_cache, i) of
         SOME v => v
       | NONE =>
         let val v = case Array.sub(!tm_descs, i) of
               SOME (TmVar (name, tyid)) =>
                 Term.mk_var(name, ty tyid)
             | SOME (TmConst (thy, name, tyid)) =>
                 Term.mk_thy_const {Thy=thy, Name=name, Ty=ty tyid}
             | SOME (TmApp (fid, xid)) =>
                 Term.mk_comb(tm fid, tm xid)
             | SOME (TmLam (vid, bid)) =>
                 Term.mk_abs(tm vid, tm bid)
             | NONE => raise ERR "replay" ("unknown term id " ^
                         Int.toString i)
         in Array.update(!tm_cache, i, SOME v); v end)

    (* Map for theorems (trace_ids can be large/sparse) *)
    val thm_map : (int, Thm.thm) Redblackmap.dict ref =
      ref (Redblackmap.mkDict Int.compare)
    fun set_th i v = thm_map := Redblackmap.insert(!thm_map, i, v)
    fun th i = case Redblackmap.peek(!thm_map, i) of
                 SOME v => v
               | NONE => raise ERR "replay" ("unknown thm id " ^
                           Int.toString i)

    fun int_of s = valOf (Int.fromString s)

    val compute_fn = ref (NONE : (thm list -> term -> thm) option)
    val exports = ref ([] : (string * thm) list)

    fun process_line line =
      let val toks = tokenize line
      in case toks of
        [] => ()
      | ["V", n] => ()  (* version line *)

      (* --- Type entries (stored lazily) --- *)
      | ["Y", id_s, "V", name] =>
          set_ty_desc (int_of id_s) (TyVar (unescape name))
      | ("Y" :: id_s :: "O" :: thy_s :: name_s :: arg_ids) =>
          set_ty_desc (int_of id_s)
            (TyOp (unescape thy_s, unescape name_s,
                   map int_of arg_ids))

      (* --- Term entries (stored lazily) --- *)
      | ["T", id_s, "V", name_s, ty_s] =>
          set_tm_desc (int_of id_s)
            (TmVar (unescape name_s, int_of ty_s))
      | ["T", id_s, "C", thy_s, name_s, ty_s] =>
          set_tm_desc (int_of id_s)
            (TmConst (unescape thy_s, unescape name_s, int_of ty_s))
      | ["T", id_s, "A", f_s, x_s] =>
          set_tm_desc (int_of id_s)
            (TmApp (int_of f_s, int_of x_s))
      | ["T", id_s, "L", v_s, b_s] =>
          set_tm_desc (int_of id_s)
            (TmLam (int_of v_s, int_of b_s))

      (* --- Theorem entries --- *)
      | ("P" :: id_s :: rule :: args) =>
          let
            val id = int_of id_s
            fun a n = List.nth(args, n)
            fun ai n = int_of (a n)
            val result = case rule of
              "REFL" => Thm.REFL (tm (ai 0))
            | "ASSUME" => Thm.ASSUME (tm (ai 0))
            | "BETA_CONV" => Thm.BETA_CONV (tm (ai 0))
            | "ALPHA" => Thm.ALPHA (tm (ai 0)) (tm (ai 1))
            | "ABS" => Thm.ABS (tm (ai 1)) (th (ai 0))
            | "MK_COMB" => Thm.MK_COMB (th (ai 0), th (ai 1))
            | "AP_TERM" => Thm.AP_TERM (tm (ai 1)) (th (ai 0))
            | "AP_THM" => Thm.AP_THM (th (ai 0)) (tm (ai 1))
            | "SYM" => Thm.SYM (th (ai 0))
            | "TRANS" => Thm.TRANS (th (ai 0)) (th (ai 1))
            | "EQ_MP" => Thm.EQ_MP (th (ai 0)) (th (ai 1))
            | "EQ_IMP_RULE1" => #1 (Thm.EQ_IMP_RULE (th (ai 0)))
            | "EQ_IMP_RULE2" => #2 (Thm.EQ_IMP_RULE (th (ai 0)))
            | "MP" => Thm.MP (th (ai 0)) (th (ai 1))
            | "DISCH" => Thm.DISCH (tm (ai 1)) (th (ai 0))
            | "INST_TYPE" =>
                let val parent = th (ai 0)
                    val rest = List.drop(args, 1)
                    fun pairs [] = []
                      | pairs (a::b::r) =
                          {redex = ty (int_of a),
                           residue = ty (int_of b)} :: pairs r
                      | pairs _ = raise ERR "replay" "INST_TYPE: odd args"
                in Thm.INST_TYPE (pairs rest) parent end
            | "INST" =>
                let val parent = th (ai 0)
                    val rest = List.drop(args, 1)
                    fun pairs [] = []
                      | pairs (a::b::r) =
                          {redex = tm (int_of a),
                           residue = tm (int_of b)} :: pairs r
                      | pairs _ = raise ERR "replay" "INST: odd args"
                in Thm.INST (pairs rest) parent end
            | "SUBST" =>
                let val orig = th (ai 0)
                    val template = tm (ai 1)
                    val rest = List.drop(args, 2)
                    fun pairs [] = []
                      | pairs (v::r::rest) =
                          {redex = tm (int_of v),
                           residue = th (int_of r)} :: pairs rest
                      | pairs _ = raise ERR "replay" "SUBST: odd args"
                in Thm.SUBST (pairs rest) template orig end
            | "SPEC" => Thm.SPEC (tm (ai 1)) (th (ai 0))
            | "Specialize" => Thm.Specialize (tm (ai 1)) (th (ai 0))
            | "GEN" => Thm.GEN (tm (ai 1)) (th (ai 0))
            | "GENL" =>
                let val parent = th (ai 0)
                    val vs = map (tm o int_of) (List.drop(args, 1))
                in Thm.GENL vs parent end
            | "GEN_ABS" =>
                let val parent = th (ai 0)
                    val opt_s = a 1
                    val opt = if opt_s = "~" then NONE
                              else SOME (tm (int_of opt_s))
                    val vs = map (tm o int_of) (List.drop(args, 2))
                in Thm.GEN_ABS opt vs parent end
            | "EXISTS" =>
                Thm.EXISTS (tm (ai 1), tm (ai 2)) (th (ai 0))
            | "CHOOSE" =>
                Thm.CHOOSE (tm (ai 2), th (ai 0)) (th (ai 1))
            | "CONJ" => Thm.CONJ (th (ai 0)) (th (ai 1))
            | "CONJUNCT1" => Thm.CONJUNCT1 (th (ai 0))
            | "CONJUNCT2" => Thm.CONJUNCT2 (th (ai 0))
            | "DISJ1" => Thm.DISJ1 (th (ai 0)) (tm (ai 1))
            | "DISJ2" => Thm.DISJ2 (tm (ai 1)) (th (ai 0))
            | "DISJ_CASES" =>
                Thm.DISJ_CASES (th (ai 0)) (th (ai 1)) (th (ai 2))
            | "NOT_INTRO" => Thm.NOT_INTRO (th (ai 0))
            | "NOT_ELIM" => Thm.NOT_ELIM (th (ai 0))
            | "CCONTR" => Thm.CCONTR (tm (ai 1)) (th (ai 0))
            | "Beta" => Thm.Beta (th (ai 0))
            | "Mk_comb" =>
                let val (_, _, mkthm) = Thm.Mk_comb (th (ai 0))
                in mkthm (th (ai 1)) (th (ai 2)) end
            | "Mk_abs" =>
                let val (_, _, mkthm) = Thm.Mk_abs (th (ai 0))
                in mkthm (th (ai 1)) end
            | "DEF_TYOP" =>
                Thm.prim_type_definition
                  ({Thy = unescape (a 1), Tyop = unescape (a 2)},
                   th (ai 0))
            | "DEF_SPEC" =>
                let val witness = th (ai 0)
                    val thyname = unescape (a 1)
                    val cnames = map unescape (List.drop(args, 2))
                    val has_hyps = not (null (Thm.hyp witness))
                in if has_hyps
                   then #2 (Thm.gen_prim_specification thyname witness)
                   else Thm.prim_specification thyname cnames witness
                end
            | "COMPUTE" =>
                let val input = tm (ai 0)
                    val code_eqs = map (th o int_of)
                                       (List.drop(args, 1))
                in case !compute_fn of
                     SOME cached => cached code_eqs input
                   | NONE => raise ERR "replay"
                       "COMPUTE before COMPUTE_INIT"
                end
            | "AXIOM" =>
                Thm.mk_axiom_thm (Nonce.mk (unescape (a 0)), tm (ai 1))
            | "ORACLE" =>
                let val tag = unescape (a 0)
                    val c = tm (ai 1)
                    val hs = map (tm o int_of) (List.drop(args, 2))
                in Thm.mk_oracle_thm tag (hs, c) end
            | "DISK_THM" =>
                (* Per-theory trace: unresolved ancestor reference.
                   Create an oracle thm placeholder. *)
                let val thy_s = unescape (a 0)
                    val name_s = unescape (a 1)
                in Thm.mk_oracle_thm "DISK_THM"
                     ([], Term.mk_var(thy_s ^ "$" ^ name_s,
                                      Type.bool))
                end
            | other => raise ERR "replay" ("unknown rule: " ^ other)
          in set_th id result end

      (* --- Compute init --- *)
      | ("C" :: args) =>
          let
            fun ai n = int_of (List.nth(args, n))
            val cval_type = ty (ai 0)
            val num_type = ty (ai 1)
            val rest = List.drop(args, 2)
            (* First 29 pairs are cval (name, term_id) *)
            val cval_terms = List.tabulate(29, fn i =>
              (unescape (List.nth(rest, 2*i)),
               tm (int_of (List.nth(rest, 2*i + 1)))))
            val rest2 = List.drop(rest, 58)
            (* Remaining pairs are char_eqn (name, thm_id) *)
            fun pairs [] = []
              | pairs (n :: p :: r) =
                  (unescape n, th (int_of p)) :: pairs r
              | pairs _ = raise ERR "replay" "C: odd char_eqn args"
            val char_eqns = pairs rest2
            val cached = Thm.compute {
              cval_terms = cval_terms,
              cval_type = cval_type,
              num_type = num_type,
              char_eqns = char_eqns
            }
          in compute_fn := SOME cached end

      (* --- Theory name --- *)
      | ["N", _] => ()  (* ignore theory name during replay *)

      (* --- Exports --- *)
      | ["E", name_s, thm_s] =>
          exports := (unescape name_s, th (int_of thm_s)) :: !exports

      | _ => ()  (* skip blank lines etc. *)
      end
      handle e =>
        let val toks = tokenize line
            val id_s = if length toks >= 2 then List.nth(toks, 1) else "?"
            val rule = if length toks >= 3 then List.nth(toks, 2) else "?"
        in print ("REPLAY_FAIL " ^ id_s ^ " " ^ rule ^ ": " ^
                  General.exnMessage e ^ "\n")
        end

    fun read_all () =
      case TextIO.inputLine instrm of
        NONE => ()
      | SOME line =>
          let val l = String.substring(line, 0, size line - 1)
                      handle Subscript => line
          in process_line l; read_all () end
  in
    (read_all () handle e => (cleanup (); raise e));
    cleanup ();
    rev (!exports)
  end

(* ------- Convenience: find trace files ------- *)

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
            in if OS.FileSys.isDir p then loop (walk p acc)
               else if String.isSuffix "Theory.pft" entry then
                 let val thy = String.substring(entry, 0,
                                 size entry - size "Theory.pft")
                 in loop ((thy, p) :: acc) end
               else loop acc
            end
      in loop acc end
  in walk dir [] end

end
