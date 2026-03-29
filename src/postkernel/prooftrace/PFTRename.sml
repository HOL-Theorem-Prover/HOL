structure PFTRename :> PFTRename = struct

val binder_infix = " pft%"

(* ========================================================================= *)
(* Binder name utilities                                                     *)
(* ========================================================================= *)

fun is_binder_name s = String.isSubstring binder_infix s

(* Strip the last occurrence of binder_infix and everything after it. *)
fun strip_binder_name s = let
  val ilen = String.size binder_infix
  val slen = String.size s
  fun search i =
    if i < 0 then raise Fail ("PFTRename: not a binder name: " ^ s)
    else if String.substring(s, i, ilen) = binder_infix
         then String.substring(s, 0, i)
         else search (i - 1)
in search (slen - ilen) end

(* ========================================================================= *)
(* Term DAG representation                                                   *)
(* ========================================================================= *)

datatype term_info =
    TVar of string   (* name only; type not needed for rename check *)
  | TConst
  | TComb of int * int
  | TAbs of int * int  (* binder var id, body id *)

(* ========================================================================= *)
(* Pass 1: Read PFT file, build term DAG, collect ABS info                   *)
(* ========================================================================= *)

(* An ABS whose binder has a " pft%" name *)
type binder_abs = {
  binder_id : int,     (* PFT term ID of the binder VAR *)
  body_id : int,        (* PFT term ID of the body *)
  stripped : string     (* stripped binder name *)
}

fun pass1 (file: string) = let
  val {n_tm, ...} = PFTReader.read_limits {file = file, binary = true}
  val {ruleset, ...} = PFTReader.read_header {file = file, binary = true}
  val descs = PFTOpcodes.descs_for_ruleset ruleset

  (* Term info array *)
  val terms = Array.array(n_tm, TConst)  (* default doesn't matter *)

  fun set_term (id, info) = Array.update(terms, id, info)

  (* Collect ABS commands with binder names *)
  val abs_list = ref [] : binder_abs list ref

  val format_handler : PFTReader.format_handler = {
    tyvar     = fn _ => (),
    tyop      = fn _ => (),
    var       = fn (id, name, _) => set_term (id, TVar name),
    const     = fn (id, _, _) => set_term (id, TConst),
    comb      = fn (id, f, x) => set_term (id, TComb (f, x)),
    abs       = fn (id, v, b) => let
      val () = set_term (id, TAbs (v, b))
      val name = case Array.sub(terms, v) of
                   TVar n => n
                 | _ => raise Fail "PFTRename: ABS binder is not a VAR"
    in if is_binder_name name then
         abs_list := {binder_id = v, body_id = b,
                      stripped = strip_binder_name name} :: !abs_list
       else ()
    end,
    new_const = fn _ => (),
    new_type  = fn _ => (),
    axiom     = fn _ => (),
    save      = fn _ => (),
    load      = fn _ => (),
    del       = fn _ => (),
    del_range = fn _ => ()
  }

  (* Dummy ruleset handler: consume all arguments *)
  val ruleset_handler : PFTReader.ruleset_handler = fn opc => fn sr => let
    val desc = PFTOpcodes.lookup_desc descs opc
    val _ = #readVarint sr ()  (* result id *)
    fun skip (PFTOpcodes.Id _)          = ignore (#readVarint sr ())
      | skip PFTOpcodes.Val             = ignore (#readVarint sr ())
      | skip (PFTOpcodes.IdList _)      = ignore (#readVarintList sr ())
      | skip (PFTOpcodes.IdPairs _)     = ignore (#readVarintPairs sr ())
      | skip (PFTOpcodes.StrIdPairs _)  = ignore (#readStringVarintPairs sr ())
      | skip PFTOpcodes.NewTypeName     = ignore (#readString sr ())
      | skip PFTOpcodes.NewConstName    = ignore (#readString sr ())
      | skip PFTOpcodes.NewConstNames   = ignore (#readStringList sr ())
  in List.app skip (#args desc) end

  val _ = PFTReader.read {file = file, binary = true,
                          format_handler = format_handler,
                          ruleset_handler = ruleset_handler}
in
  { terms = terms,
    abs_list = !abs_list,
    n_tm = n_tm,
    ruleset = ruleset,
    descs = descs }
end

(* ========================================================================= *)
(* Pass 2: Decide which binders to rename                                    *)
(* ========================================================================= *)

(* Top-down DAG walk: does stripped_name occur free in term id?
   "Free" means: a VAR named stripped_name, or a VAR whose id is
   in the renamed set. No shadowing occurs because all binder names
   use the " pft%" infix, not plain names. *)
fun has_name (terms: term_info array)
             (renamed: BoolArray.array)
             (stripped_name: string)
             (id: int) : bool =
  case Array.sub(terms, id) of
    TVar name => name = stripped_name orelse BoolArray.sub(renamed, id)
  | TConst => false
  | TComb (f, x) =>
      has_name terms renamed stripped_name f orelse
      has_name terms renamed stripped_name x
  | TAbs (_, body) =>
      has_name terms renamed stripped_name body

fun pass2 {terms, abs_list, n_tm, ...}
    : BoolArray.array = let
  val renamed = BoolArray.array(n_tm, false)
  (* abs_list is in reverse file order (outermost first, since
     PFT is bottom-up and we cons'd onto the list). *)
  val () = List.app (fn {binder_id, body_id, stripped} =>
    if has_name terms renamed stripped body_id then ()
    else BoolArray.update(renamed, binder_id, true))
    abs_list
in renamed end

(* ========================================================================= *)
(* Pass 3: Byte-level rewrite                                                *)
(* ========================================================================= *)

(* Binary I/O primitives *)

type copy_state = {
  inp: BinIO.instream,
  out: BinIO.outstream,
  pos: int ref
}

fun read_byte ({inp, pos, ...}: copy_state) = let
  val b = Word8.toInt (valOf (BinIO.input1 inp))
in pos := !pos + 1; b end

fun write_byte ({out, ...}: copy_state) b =
  BinIO.output1(out, Word8.fromInt b)

fun copy_bytes ({inp, out, pos}: copy_state) n = let
  val bytes = BinIO.inputN(inp, n)
in BinIO.output(out, bytes); pos := !pos + n end

(* Read a varint, copying bytes to output *)
fun copy_varint (cs: copy_state) : int = let
  fun loop acc shift = let
    val b = read_byte cs
    val () = write_byte cs b
  in if b < 128 then acc + b * shift
     else loop (acc + (b - 128) * shift) (shift * 128)
  end
in loop 0 1 end

(* Read a varint without copying (for skipping) *)
fun read_varint (cs: copy_state) : int = let
  fun loop acc shift = let
    val b = read_byte cs
  in if b < 128 then acc + b * shift
     else loop (acc + (b - 128) * shift) (shift * 128)
  end
in loop 0 1 end

(* Write a varint *)
fun write_varint (cs: copy_state) (n: int) =
  if n < 128 then write_byte cs n
  else (write_byte cs (128 + (n mod 128));
        write_varint cs (n div 128))

(* Copy a string (varint length + bytes) *)
fun copy_string (cs: copy_state) = let
  val len = copy_varint cs
in copy_bytes cs len end

(* Skip a string without copying *)
fun skip_string (cs: copy_state) = let
  val len = read_varint cs
in ignore (BinIO.inputN(#inp cs, len));
   #pos cs := !(#pos cs) + len end

(* Write a string *)
fun write_string (cs: copy_state) (s: string) = let
  val () = write_varint cs (String.size s)
in BinIO.output(#out cs, Byte.stringToBytes s) end

(* Copy a varint list (count + varints) *)
fun copy_varint_list (cs: copy_state) = let
  val n = copy_varint cs
  fun loop 0 = () | loop k = (ignore (copy_varint cs); loop (k-1))
in loop n end

(* Copy varint pairs (count + pairs) *)
fun copy_varint_pairs (cs: copy_state) = let
  val n = copy_varint cs
  fun loop 0 = () | loop k = (ignore (copy_varint cs);
                               ignore (copy_varint cs); loop (k-1))
in loop n end

(* Copy string-varint pairs *)
fun copy_string_varint_pairs (cs: copy_state) = let
  val n = copy_varint cs
  fun loop 0 = () | loop k = (copy_string cs;
                               ignore (copy_varint cs); loop (k-1))
in loop n end

(* Copy a string list *)
fun copy_string_list (cs: copy_state) = let
  val n = copy_varint cs
  fun loop 0 = () | loop k = (copy_string cs; loop (k-1))
in loop n end

(* Skip/copy a ruleset command's arguments using opcode descriptors *)
fun copy_ruleset_cmd (cs: copy_state)
                     (descs: (int * PFTOpcodes.opcode_desc) list)
                     (opc: int) = let
  val desc = PFTOpcodes.lookup_desc descs opc
  val _ = copy_varint cs  (* result id *)
  fun copy_arg (PFTOpcodes.Id _)          = ignore (copy_varint cs)
    | copy_arg PFTOpcodes.Val             = ignore (copy_varint cs)
    | copy_arg (PFTOpcodes.IdList _)      = copy_varint_list cs
    | copy_arg (PFTOpcodes.IdPairs _)     = copy_varint_pairs cs
    | copy_arg (PFTOpcodes.StrIdPairs _)  = copy_string_varint_pairs cs
    | copy_arg PFTOpcodes.NewTypeName     = copy_string cs
    | copy_arg PFTOpcodes.NewConstName    = copy_string cs
    | copy_arg PFTOpcodes.NewConstNames   = copy_string_list cs
in List.app copy_arg (#args desc) end

fun pass3 {input, output, renamed, descs} = let
  val inp = BinIO.openIn input
  val out = BinIO.openOut output
  val cs : copy_state = {inp = inp, out = out, pos = ref 0}

  (* Copy header: magic "PFT\0" + version varint + ruleset string *)
  val () = copy_bytes cs 4  (* magic *)
  val _ = copy_varint cs    (* version *)
  val () = copy_string cs   (* ruleset *)

  (* Determine where commands end (before footer).
     Use read_footer_raw-style calculation: last 2 bytes are footer
     length, then footer_len bytes before that are the footer. *)
  val file_size = Position.toInt (OS.FileSys.fileSize input)
  val footer_info = let
    val r = BinIO.openIn input
    val _ = BinIO.inputN(r, file_size - 2)
    val lo = Word8.toInt (valOf (BinIO.input1 r))
    val hi = Word8.toInt (valOf (BinIO.input1 r))
    val () = BinIO.closeIn r
  in hi * 256 + lo end
  val cmd_end = file_size - footer_info - 2

  fun cmd_loop () =
    if !(#pos cs) >= cmd_end then ()
    else let
      val opc = read_byte cs
      val () = write_byte cs opc
    in
      (if opc >= 0x10 andalso opc <= 0x4F then
         copy_ruleset_cmd cs descs opc
       else case opc of
         (* TYVAR: id string *)
         0x01 => (ignore (copy_varint cs); copy_string cs)
         (* TYOP: id string varint-list *)
       | 0x02 => (ignore (copy_varint cs); copy_string cs;
                   copy_varint_list cs)
         (* VAR: id string ty — potentially rename *)
       | 0x03 => let
           val id = copy_varint cs
         in if BoolArray.sub(renamed, id)
            then let val len = read_varint cs
                     val name = Byte.bytesToString
                                  (BinIO.inputN(#inp cs, len))
                     val () = #pos cs := !(#pos cs) + len
                 in write_string cs (strip_binder_name name);
                    ignore (copy_varint cs) end
            else (copy_string cs; ignore (copy_varint cs))
         end
         (* CONST: id string ty *)
       | 0x04 => (ignore (copy_varint cs); copy_string cs;
                   ignore (copy_varint cs))
         (* COMB: id id id *)
       | 0x05 => (ignore (copy_varint cs); ignore (copy_varint cs);
                   ignore (copy_varint cs))
         (* ABS: id id id *)
       | 0x06 => (ignore (copy_varint cs); ignore (copy_varint cs);
                   ignore (copy_varint cs))
         (* NEW_CONST: string ty *)
       | 0x07 => (copy_string cs; ignore (copy_varint cs))
         (* NEW_TYPE: string arity *)
       | 0x08 => (copy_string cs; ignore (copy_varint cs))
         (* AXIOM: id tm name *)
       | 0x09 => (ignore (copy_varint cs); ignore (copy_varint cs);
                   copy_string cs)
         (* SAVE: name th *)
       | 0x50 => (copy_string cs; ignore (copy_varint cs))
         (* LOAD: id name *)
       | 0x51 => (ignore (copy_varint cs); copy_string cs)
         (* DEL: id *)
       | 0xE0 => ignore (copy_varint cs)
       | 0xE1 => ignore (copy_varint cs)
       | 0xE2 => ignore (copy_varint cs)
       | 0xE3 => ignore (copy_varint cs)
         (* DEL range: id id *)
       | 0xF0 => (ignore (copy_varint cs); ignore (copy_varint cs))
       | 0xF1 => (ignore (copy_varint cs); ignore (copy_varint cs))
       | 0xF2 => (ignore (copy_varint cs); ignore (copy_varint cs))
       | 0xF3 => (ignore (copy_varint cs); ignore (copy_varint cs))
       | _ => raise Fail ("PFTRename: unknown opcode 0x" ^
                           Int.fmt StringCvt.HEX opc));
      cmd_loop ()
    end

  val () = cmd_loop ()

  (* Copy footer verbatim *)
  val remaining = file_size - !(#pos cs)
  val () = copy_bytes cs remaining

  val () = BinIO.closeIn inp
  val () = BinIO.closeOut out
in () end

(* ========================================================================= *)
(* Main entry point                                                          *)
(* ========================================================================= *)

fun rename {input, output} = let
  val p1 = pass1 input
  val renamed = pass2 p1
  val () = pass3 {input = input, output = output,
                  renamed = renamed, descs = #descs p1}
in () end

end
