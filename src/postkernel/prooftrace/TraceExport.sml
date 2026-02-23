(* TraceExport: write per-theory .pftrace files from recorded trace data.

   This module is NOT in the trust boundary. Its output is independently
   verified by replaying the trace through the kernel (ReplayTrace).
*)

structure TraceExport :> TraceExport =
struct

open HolKernel

val ERR = mk_HOL_ERR "TraceExport"
fun its i = Int.toString i

(* -----------------------------------------------------------------------
   String escaping for the trace format
   ----------------------------------------------------------------------- *)

fun escape_string s =
  if CharVector.all (fn c => Char.isPrint c andalso c <> #" ") s
  then s
  else "\"" ^ String.translate
     (fn #"\"" => "\\\""
       | #"\\" => "\\\\"
       | #"\n" => "\\n"
       | c => if Char.ord c < 0x20
              then "\\x" ^ StringCvt.padLeft #"0" 2
                     (Int.fmt StringCvt.HEX (Char.ord c))
              else str c) s ^ "\""

(* -----------------------------------------------------------------------
   Type/term writing
   ----------------------------------------------------------------------- *)

fun write_type_entry ostrm i ty =
  if Type.is_vartype ty then
    TextIO.output(ostrm,
      "Y " ^ its i ^ " V " ^ escape_string (Type.dest_vartype ty) ^ "\n")
  else
    let val {Thy, Tyop, Args} = Type.dest_thy_type ty
    in TextIO.output(ostrm,
         "Y " ^ its i ^ " O " ^ escape_string Thy ^ " " ^
         escape_string Tyop ^
         (if null Args then ""
          else " " ^ String.concatWith " "
            (map (fn a =>
              its (valOf (Redblackmap.peek(!(ref (Redblackmap.mkDict Type.compare)), a))))
              Args)) ^ "\n")
    end

(* We need a type lookup map for writing type entries *)
fun write_types ostrm types =
  let
    val ty_map = ref (Redblackmap.mkDict Type.compare)
    fun ty_id ty = valOf (Redblackmap.peek(!ty_map, ty))
  in
    ignore (List.foldl (fn (ty, i) =>
      (ty_map := Redblackmap.insert(!ty_map, ty, i);
       if Type.is_vartype ty then
         TextIO.output(ostrm,
           "Y " ^ its i ^ " V " ^ escape_string (Type.dest_vartype ty) ^ "\n")
       else
         let val {Thy, Tyop, Args} = Type.dest_thy_type ty
         in TextIO.output(ostrm,
              "Y " ^ its i ^ " O " ^ escape_string Thy ^ " " ^
              escape_string Tyop ^
              (if null Args then ""
               else " " ^ String.concatWith " " (map (its o ty_id) Args)) ^
              "\n")
         end;
       i + 1)) 0 types)
  end

fun write_terms ostrm types terms =
  let
    val ty_map = ref (Redblackmap.mkDict Type.compare)
    val _ = ignore (List.foldl (fn (ty, i) =>
      (ty_map := Redblackmap.insert(!ty_map, ty, i); i + 1)) 0 types)
    fun ty_id ty = valOf (Redblackmap.peek(!ty_map, ty))

    val tm_map = ref (Redblackmap.mkDict Term.compare)
    fun tm_id tm = valOf (Redblackmap.peek(!tm_map, tm))
  in
    ignore (List.foldl (fn (tm, i) =>
      (tm_map := Redblackmap.insert(!tm_map, tm, i);
       (case Term.dest_term tm of
          Term.VAR (name, ty) =>
            TextIO.output(ostrm,
              "M " ^ its i ^ " V " ^ escape_string name ^ " " ^
              its (ty_id ty) ^ "\n")
        | Term.CONST {Thy, Name, Ty} =>
            TextIO.output(ostrm,
              "M " ^ its i ^ " C " ^ escape_string Thy ^ " " ^
              escape_string Name ^ " " ^ its (ty_id Ty) ^ "\n")
        | Term.COMB (f, x) =>
            TextIO.output(ostrm,
              "M " ^ its i ^ " A " ^ its (tm_id f) ^ " " ^
              its (tm_id x) ^ "\n")
        | Term.LAMB (v, b) =>
            TextIO.output(ostrm,
              "M " ^ its i ^ " L " ^ its (tm_id v) ^ " " ^
              its (tm_id b) ^ "\n"));
       i + 1)) 0 terms)
  end

(* -----------------------------------------------------------------------
   Compression helpers
   ----------------------------------------------------------------------- *)

fun shell_quote s =
  "'" ^ String.translate (fn #"'" => "'\\''" | c => str c) s ^ "'"

fun detect_compressor () =
  let fun try cmd =
        let val st = OS.Process.system (cmd ^ " --version > /dev/null 2>&1")
        in OS.Process.isSuccess st end
        handle _ => false
  in
    if try "zstd" then SOME "zstd"
    else if try "gzip" then SOME "gzip"
    else NONE
  end

datatype output_handle =
    OH_Plain of TextIO.outstream
  | OH_Compressed of TextIO.outstream *
                     (TextIO.instream, TextIO.outstream) Unix.proc

fun open_output path =
  let val compressor = detect_compressor ()
  in case compressor of
       SOME "zstd" =>
         let val outpath = path ^ ".zst"
             val proc : (TextIO.instream, TextIO.outstream) Unix.proc =
               Unix.execute("/bin/sh",
                 ["-c", "zstd -q -o " ^ shell_quote outpath])
         in OH_Compressed (Unix.textOutstreamOf proc, proc) end
     | SOME "gzip" =>
         let val outpath = path ^ ".gz"
             val proc : (TextIO.instream, TextIO.outstream) Unix.proc =
               Unix.execute("/bin/sh",
                 ["-c", "gzip > " ^ shell_quote outpath])
         in OH_Compressed (Unix.textOutstreamOf proc, proc) end
     | _ => OH_Plain (TextIO.openOut path)
  end

fun out_stream (OH_Plain s) = s
  | out_stream (OH_Compressed (s, _)) = s

fun close_output (OH_Plain s) = TextIO.closeOut s
  | close_output (OH_Compressed (s, p)) =
      (TextIO.closeOut s; ignore (Unix.reap p))

(* -----------------------------------------------------------------------
   Export: write .pftrace file
   ----------------------------------------------------------------------- *)

type export_args = {
  thyname    : string,
  exports    : (string * thm) list,
  types      : hol_type list,
  terms      : term list,
  n_steps    : int,
  steps_path : string,
  thm_line   : thm -> int
}

fun export ({thyname, exports = all_thms,
             types, terms, n_steps, steps_path, thm_line}) =
  let
    val n_types = length types
    val n_terms = length terms
    val objdir = OS.FileSys.getDir()
    val outbase = objdir ^ "/" ^ thyname ^ "Theory.pftrace"
    val oh = open_output outbase
    val ostrm = out_stream oh
  in
    (* Header *)
    TextIO.output(ostrm, "HOL4_PROOF_TRACE 1\n");
    TextIO.output(ostrm, "THEORY " ^ escape_string thyname ^ "\n");
    TextIO.output(ostrm, "COUNTS " ^ its n_types ^ " " ^
      its n_terms ^ " " ^ its n_steps ^ "\n");
    TextIO.output(ostrm, "\n");

    (* Types *)
    write_types ostrm types;
    TextIO.output(ostrm, "\n");

    (* Terms *)
    write_terms ostrm types terms;
    TextIO.output(ostrm, "\n");

    (* Steps: copy temp file, adding P <line_number> prefix *)
    let val instrm = TextIO.openIn steps_path
        fun copy ln =
          case TextIO.inputLine instrm of
            NONE => ()
          | SOME line =>
            (TextIO.output(ostrm,
               "P " ^ its ln ^ " " ^
               String.substring(line, 0, size line - 1) ^ "\n");
             copy (ln + 1))
    in copy 0; TextIO.closeIn instrm end;
    TextIO.output(ostrm, "\n");

    (* Exports *)
    List.app (fn (name, th) =>
      let val ln = thm_line th
      in if ln >= 0 then
           TextIO.output(ostrm,
             "E " ^ escape_string name ^ " " ^ its ln ^ "\n")
         else
           Feedback.HOL_WARNING "TraceExport" "export"
             ("export " ^ name ^ " has no recorded step")
      end) all_thms;

    close_output oh;
    Feedback.HOL_MESG ("Proof trace: " ^
      (case oh of
         OH_Compressed _ => outbase ^ ".zst"
       | OH_Plain _ => outbase) ^
      " (" ^ its n_steps ^ " steps, " ^
      its n_terms ^ " terms, " ^ its n_types ^ " types)")
  end
  handle IO.Io e =>
    Feedback.HOL_WARNING "TraceExport" "export"
      ("I/O error: " ^ #function e ^ " " ^ #name e)
  | e =>
    Feedback.HOL_WARNING "TraceExport" "export"
      ("export failed: " ^ General.exnMessage e)

end (* structure *)
