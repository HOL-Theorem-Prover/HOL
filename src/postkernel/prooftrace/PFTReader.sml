structure PFTReader :> PFTReader = struct

type format_handler = {
  tyvar: int * string -> unit, tyop: int * string * int list -> unit,
  var: int * string * int -> unit, const: int * string * int -> unit,
  comb: int * int * int -> unit, abs: int * int * int -> unit,
  new_const: string * int -> unit, new_type: string * int -> unit,
  axiom: int * int * string option -> unit,
  save: string * int -> unit, load: int * string -> unit,
  del: string * int -> unit, del_range: string * int * int -> unit,
  expect: int * int list * int -> unit
}

type stream_reader = {
  readVarint : unit -> int,
  readString : unit -> string,
  readVarintList : unit -> int list,
  readVarintPairs : unit -> (int * int) list,
  readStringVarintPairs : unit -> (string * int) list,
  readStringList : unit -> string list
}

type ruleset_handler = int -> stream_reader -> unit

fun read_raw_args (desc: PFTOpcodes.opcode_desc) (sr: stream_reader) =
  let
    open PFTOpcodes
    fun one (spec: arg_spec) =
      case #shape spec of
        AId _          => VId (#readVarint sr ())
      | AVal           => VVal (#readVarint sr ())
      | AIdList _      => VIdList (#readVarintList sr ())
      | AIdPairs _     => VIdPairs (#readVarintPairs sr ())
      | AStrIdPairs _  => VStrIdPairs (#readStringVarintPairs sr ())
      | AName          => VName (#readString sr ())
      | ANameList      => VNameList (#readStringList sr ())
  in List.map one (#args desc) end

(* ========================================================================= *)
(* Binary I/O primitives with position tracking                              *)
(* ========================================================================= *)

type bin_reader = {
  readByte: unit -> int,
  readBytes: int -> Word8Vector.vector,
  pos: unit -> int,
  close: unit -> unit
}

fun open_bin_reader file : bin_reader = let
  val inp = BinIO.openIn file
  val p = ref 0
  fun rb () = case BinIO.input1 inp of
      SOME b => (p := !p + 1; Word8.toInt b)
    | NONE => raise Fail "PFTReader: unexpected EOF"
  fun rbs n = let val v = BinIO.inputN(inp, n) in
    if Word8Vector.length v = n then (p := !p + n; v)
    else raise Fail "PFTReader: unexpected EOF"
  end
in {readByte = rb, readBytes = rbs,
    pos = fn () => !p, close = fn () => BinIO.closeIn inp} end

fun skip_to (r: bin_reader) target = let
  val n = target - #pos r ()
in if n > 0 then (ignore (#readBytes r n)) else () end

fun mk_readVarint (r: bin_reader) () = let
  val rb = #readByte r
  fun loop acc shift = let val b = rb ()
  in if b < 128 then acc + b * shift
     else loop (acc + (b - 128) * shift) (shift * 128) end
in loop 0 1 end

fun mk_readString (r: bin_reader) () = let
  val len = mk_readVarint r ()
  val bytes = #readBytes r len
in Byte.bytesToString bytes end

fun mk_readList (r: bin_reader) f () = let
  val n = mk_readVarint r ()
  fun loop 0 acc = List.rev acc
    | loop k acc = loop (k - 1) (f () :: acc)
in loop n [] end

fun mk_readPairs (r: bin_reader) f g () = let
  val n = mk_readVarint r ()
  fun loop 0 acc = List.rev acc
    | loop k acc = let val a = f () val b = g ()
                   in loop (k - 1) ((a, b) :: acc) end
in loop n [] end

fun mk_stream_reader (r: bin_reader) : stream_reader = let
  val vi = mk_readVarint r
  val vs = mk_readString r
in {
  readVarint = vi,
  readString = vs,
  readVarintList = mk_readList r vi,
  readVarintPairs = mk_readPairs r vi vi,
  readStringVarintPairs = mk_readPairs r vs vi,
  readStringList = mk_readList r vs
} end

(* ========================================================================= *)
(* Binary footer reader                                                      *)
(* ========================================================================= *)

fun read_footer_raw file = let
  val file_size = Position.toInt (OS.FileSys.fileSize file)
  val r = open_bin_reader file
  val () = skip_to r (file_size - 2)
  val lo = #readByte r ()
  val hi = #readByte r ()
  val footer_len = hi * 256 + lo
  val () = #close r ()
  val r = open_bin_reader file
  val () = skip_to r (file_size - footer_len - 2)
  val opc = #readByte r ()
  val () = if opc = 0xFF then ()
           else raise Fail "PFTReader: bad footer opcode"
  val vi = mk_readVarint r
  val n_ty = vi () val n_tm = vi () val n_th = vi ()
  val () = #close r ()
in {n_ty = n_ty, n_tm = n_tm, n_th = n_th,
    footer_len = footer_len, file_size = file_size} end

(* ========================================================================= *)
(* JSONL limits reader: scan backwards from EOF for last line                *)
(* ========================================================================= *)

fun read_limits_jsonl file = let
  val file_size = Position.toInt (OS.FileSys.fileSize file)
  val inp = BinIO.openIn file
  (* Read last 1KB — limits line is short *)
  val chunk_size = Int.min(file_size, 1024)
  val _ = BinIO.inputN(inp, file_size - chunk_size)
  val chunk = Byte.bytesToString (BinIO.inputN(inp, chunk_size))
  val () = BinIO.closeIn inp
  (* Find last newline-delimited line *)
  val len = String.size chunk
  fun find_nl i =
    if i < 0 then 0
    else if String.sub(chunk, i) = #"\n" andalso i < len - 1 then i + 1
    else find_nl (i - 1)
  val last_line = String.extract(chunk, find_nl (len - 2), NONE)
  (* Extract integer field from JSON object via Substring.position *)
  fun getField s field = let
    val key = "\"" ^ field ^ "\":"
    val (_, rest) = Substring.position key (Substring.full s)
  in if Substring.size rest = 0
     then raise Fail ("PFTReader: no " ^ field ^ " in limits line")
     else let
       val after = Substring.dropl Char.isSpace
                     (Substring.triml (String.size key) rest)
       val digits = Substring.takel Char.isDigit after
     in case Int.fromString (Substring.string digits) of
          SOME n => n
        | NONE => raise Fail ("PFTReader: bad " ^ field ^ " in limits line")
     end
  end
in {n_ty = getField last_line "n_ty",
    n_tm = getField last_line "n_tm",
    n_th = getField last_line "n_th"} end

fun read_limits {file, binary} =
  if binary then let
    val {n_ty, n_tm, n_th, ...} = read_footer_raw file
  in {n_ty = n_ty, n_tm = n_tm, n_th = n_th} end
  else read_limits_jsonl file

fun read_header {file, binary} =
  if not binary
  then raise Fail "PFTReader: read_header not supported for JSONL"
  else let
    val r = open_bin_reader file
    val _ = #readBytes r 4   (* magic "PFT\0" *)
    val vi = mk_readVarint r
    val vs = mk_readString r
    val version = vs ()
    val ruleset = vs ()
    val () = #close r ()
  in {version = version, ruleset = ruleset} end

(* ========================================================================= *)
(* Binary command reader                                                     *)
(* ========================================================================= *)

fun read_binary file (fh: format_handler) (rh: ruleset_handler) = let
  val {n_ty, n_tm, n_th, footer_len, file_size} =
    read_footer_raw file
  val cmd_end = file_size - footer_len - 2
  val r = open_bin_reader file
  val vi = mk_readVarint r
  val vs = mk_readString r
  val sr = mk_stream_reader r

  (* Skip header, but capture version and ruleset *)
  val _ = #readBytes r 4   (* magic "PFT\0" *)
  val version = vs ()
  val ruleset = vs ()

  fun dispatch opc =
    if opc >= 0x10 andalso opc <= 0x4F then
      rh opc sr
    else case opc of
    (* Type commands *)
      0x01 => let val id = vi() val name = vs()
              in #tyvar fh (id, name) end
    | 0x02 => let val id = vi() val name = vs()
                  val args = mk_readList r vi ()
              in #tyop fh (id, name, args) end
    (* Term commands *)
    | 0x03 => let val id = vi() val name = vs() val ty = vi()
              in #var fh (id, name, ty) end
    | 0x04 => let val id = vi() val name = vs() val ty = vi()
              in #const fh (id, name, ty) end
    | 0x05 => let val id = vi() val a = vi() val b = vi()
              in #comb fh (id, a, b) end
    | 0x06 => let val id = vi() val a = vi() val b = vi()
              in #abs fh (id, a, b) end
    (* Kernel commands *)
    | 0x07 => let val name = vs() val ty = vi()
              in #new_const fh (name, ty) end
    | 0x08 => let val name = vs() val arity = vi()
              in #new_type fh (name, arity) end
    | 0x09 => let val id = vi() val tm = vi() val name = vs()
              in #axiom fh (id, tm,
                   if name = "" then NONE else SOME name) end
    (* Control commands *)
    | 0x50 => let val name = vs() val th = vi()
              in #save fh (name, th) end
    | 0x51 => let val id = vi() val name = vs()
              in #load fh (id, name) end
    (* DEL *)
    | 0xE0 => #del fh ("ty", vi())
    | 0xE1 => #del fh ("tm", vi())
    | 0xE2 => #del fh ("th", vi())
    | 0xF0 => let val a = vi() val b = vi() in #del_range fh ("ty",a,b) end
    | 0xF1 => let val a = vi() val b = vi() in #del_range fh ("tm",a,b) end
    | 0xF2 => let val a = vi() val b = vi() in #del_range fh ("th",a,b) end
    (* Debug commands *)
    | 0xEF => let val th = vi()
                  val n = vi()
                  fun lp 0 acc = rev acc | lp k acc = lp (k-1) (vi() :: acc)
                  val hyps = lp n []
                  val concl = vi()
              in #expect fh (th, hyps, concl) end
    | _ => raise Fail ("PFTReader: unknown opcode 0x" ^
                        Int.fmt StringCvt.HEX opc)

  fun cmd_loop () =
    if #pos r () >= cmd_end then ()
    else (dispatch (#readByte r ()); cmd_loop ())

  val () = cmd_loop ()
  val () = #close r ()
in {version = version, ruleset = ruleset,
    n_ty = n_ty, n_tm = n_tm, n_th = n_th} end

(* ========================================================================= *)
(* HOL4 ruleset handler                                                      *)
(* ========================================================================= *)

structure HOL4 = struct

type handler = {
  refl: int * int -> unit, alpha: int * int * int -> unit,
  beta_conv: int * int -> unit, sym: int * int -> unit,
  trans: int * int * int -> unit, eq_mp: int * int * int -> unit,
  mk_comb: int * int * int -> unit, abs_thm: int * int * int -> unit,
  ap_term: int * int * int -> unit, ap_thm: int * int * int -> unit,
  beta_thm: int * int -> unit,
  mk_comb_thm: int * int * int * int -> unit,
  mk_abs_thm: int * int * int -> unit,
  assume: int * int -> unit, mp: int * int * int -> unit,
  disch: int * int * int -> unit, not_intro: int * int -> unit,
  not_elim: int * int -> unit, ccontr: int * int * int -> unit,
  deductAntisym: int * int * int -> unit,
  conj: int * int * int -> unit, conjunct1: int * int -> unit,
  conjunct2: int * int -> unit,
  disj1: int * int * int -> unit, disj2: int * int * int -> unit,
  disj_cases: int * int * int * int -> unit,
  gen: int * int * int -> unit, spec: int * int * int -> unit,
  specialize: int * int * int -> unit,
  genl: int * int * int list -> unit,
  exists: int * int * int * int -> unit,
  choose: int * int * int * int -> unit,
  absl: int * int * int list -> unit,
  gen_abs: int * int * int * int list -> unit,
  inst: int * int * (int * int) list -> unit,
  inst_type: int * int * (int * int) list -> unit,
  subst: int * int * int * (int * int) list -> unit,
  eq_imp_rule1: int * int -> unit, eq_imp_rule2: int * int -> unit,
  def_tyop: int * int * string -> unit,
  def_spec: int * int * string list -> unit,
  def_spec_gen: int * int * string list -> unit,
  compute_init: int * int
                * (string * int) list * (string * int) list -> unit,
  compute: int * int * int list -> unit
}

fun make_handler (h: handler) : ruleset_handler = fn opc => fn sr => let
  val vi = #readVarint sr
  val vs = #readString sr
in case opc of
    0x10 => let val id = vi() in #refl h (id, vi()) end
  | 0x11 => let val id = vi() val a = vi() in #alpha h (id, a, vi()) end
  | 0x12 => let val id = vi() in #assume h (id, vi()) end
  | 0x13 => let val id = vi() in #beta_conv h (id, vi()) end
  | 0x14 => let val id = vi() val a = vi() in #eq_mp h (id, a, vi()) end
  | 0x15 => let val id = vi() val a = vi() in #mp h (id, a, vi()) end
  | 0x16 => let val id = vi() in #sym h (id, vi()) end
  | 0x17 => let val id = vi() val a = vi() in #trans h (id, a, vi()) end
  | 0x18 => let val id = vi() val a = vi() in #conj h (id, a, vi()) end
  | 0x19 => let val id = vi() in #conjunct1 h (id, vi()) end
  | 0x1A => let val id = vi() in #conjunct2 h (id, vi()) end
  | 0x1B => let val id = vi() val a = vi() in #disch h (id, a, vi()) end
  | 0x1C => let val id = vi() val a = vi() in #disj1 h (id, a, vi()) end
  | 0x1D => let val id = vi() val a = vi() in #disj2 h (id, a, vi()) end
  | 0x1E => let val id = vi() val a = vi() val b = vi()
            in #disj_cases h (id, a, b, vi()) end
  | 0x1F => let val id = vi() in #not_elim h (id, vi()) end
  | 0x20 => let val id = vi() in #not_intro h (id, vi()) end
  | 0x21 => let val id = vi() val a = vi() in #ccontr h (id, a, vi()) end
  | 0x22 => let val id = vi() val a = vi() val b = vi()
            in #exists h (id, a, b, vi()) end
  | 0x23 => let val id = vi() val a = vi() val b = vi()
            in #choose h (id, a, b, vi()) end
  | 0x24 => let val id = vi() val a = vi() in #gen h (id, a, vi()) end
  | 0x25 => let val id = vi() val a = vi() in #spec h (id, a, vi()) end
  | 0x26 => let val id = vi() val a = vi() in #specialize h (id, a, vi()) end
  | 0x27 => let val id = vi() val th = vi()
            in #genl h (id, th, #readVarintList sr ()) end
  | 0x28 => let val id = vi() val th = vi()
            in #absl h (id, th, #readVarintList sr ()) end
  | 0x29 => let val id = vi() val th = vi() val c = vi()
            in #gen_abs h (id, th, c, #readVarintList sr ()) end
  | 0x30 => let val id = vi() val a = vi() in #abs_thm h (id, a, vi()) end
  | 0x31 => let val id = vi() val a = vi() in #ap_term h (id, a, vi()) end
  | 0x32 => let val id = vi() val a = vi() in #ap_thm h (id, a, vi()) end
  | 0x33 => let val id = vi() val a = vi() in #mk_comb h (id, a, vi()) end
  | 0x34 => let val id = vi() in #beta_thm h (id, vi()) end
  | 0x35 => let val id = vi() val a = vi() in #mk_abs_thm h (id, a, vi()) end
  | 0x36 => let val id = vi() val a = vi() val b = vi()
            in #mk_comb_thm h (id, a, b, vi()) end
  | 0x37 => let val id = vi() in #eq_imp_rule1 h (id, vi()) end
  | 0x38 => let val id = vi() in #eq_imp_rule2 h (id, vi()) end
  | 0x39 => let val id = vi() val th = vi()
            in #inst h (id, th, #readVarintPairs sr ()) end
  | 0x3A => let val id = vi() val th = vi()
            in #inst_type h (id, th, #readVarintPairs sr ()) end
  | 0x3B => let val id = vi() val t = vi() val th = vi()
            in #subst h (id, t, th, #readVarintPairs sr ()) end
  | 0x3C => let val id = vi() val a = vi()
            in #deductAntisym h (id, a, vi()) end
  | 0x40 => let val id = vi() val th = vi()
            in #def_tyop h (id, th, vs()) end
  | 0x41 => let val id = vi() val th = vi()
            in #def_spec h (id, th, #readStringList sr ()) end
  | 0x42 => let val id = vi() val th = vi()
            in #def_spec_gen h (id, th, #readStringList sr ()) end
  | 0x43 => let val ty1 = vi() val ty2 = vi()
                val eqns = #readStringVarintPairs sr ()
                val terms = #readStringVarintPairs sr ()
            in #compute_init h (ty1, ty2, eqns, terms) end
  | 0x44 => let val id = vi() val tm = vi()
            in #compute h (id, tm, #readVarintList sr ()) end
  | _ => raise Fail ("PFTReader.HOL4: unknown opcode 0x" ^
                      Int.fmt StringCvt.HEX opc)
end

end (* structure HOL4 *)

(* ========================================================================= *)
(* Public interface                                                          *)
(* ========================================================================= *)

fun read {file, binary, format_handler, ruleset_handler} =
  if binary then read_binary file format_handler ruleset_handler
  else raise Fail "PFTReader: JSON reader not yet implemented"

end
