structure file_readerLib :> file_readerLib =
struct

open HolKernel boolLib bossLib Parse;
open helperLib backgroundLib writerLib;

datatype arch = ARM | ARM8 | M0 | RISCV

(* refs begin *)

val arch_name = ref ARM;
val skip_names = ref ["halt"];
val missing_sigs = ref ([]:string list);
val complete_sections = ref ([]:(string * (* sec_name *)
                                 (int list * int * bool) * (* signature *)
                                 string * (* location as hex string *)
                                 (int * string * string) list * (* body *)
                                 string list) list); (* dependencies *)

(* refs end *)

fun arch_str () =
  case (!arch_name) of ARM => "ARM" | ARM8 => "Arm8" | M0 => "M0" | RISCV => "RISC-V"

fun HOL_commit () = let
  val path = Globals.HOLDIR
  val exec = OS.Process.system
  val filename = "/tmp/hol_commit"
  val _ = exec ("cd " ^ path ^
                "; git log --abbrev-commit -n 1 | head -n 1 > " ^ filename)
  val t = TextIO.openIn(filename)
  val commit = case TextIO.inputLine(t) of SOME s => s | NONE => fail()
  val _ = TextIO.closeIn(t)
  val _ = exec ("/bin/rm -f " ^ filename)
  val remove_newline =
    String.translate (fn c => if c = #"\n" then "" else implode [c])
  in remove_newline commit end handle Interrupt => raise Interrupt
                     | _ => failwith("Cannot read commit number.")

fun HOL_version () =
  Globals.release ^ " " ^ int_to_string Globals.version ^
  " (" ^ Thm.kernelid ^ ") " ^ (HOL_commit () handle HOL_ERR e => #message e)

fun add_missing_sig x = let
  val _ = print ("No signature info for section: " ^ x ^ "\n")
  in (missing_sigs := x :: (!missing_sigs)) end;

fun read_sections filename = let
  val xs = lines_from_file filename
  fun is_hex_char c = mem c (explode "0123456789abcdefABCDEF")
  fun is_hex_string str = every is_hex_char (explode str)
  fun dest_section_declaration line = let
    val _ = String.substring(line,8,2) = " <" orelse
            String.substring(line,16,2) = " <" orelse fail()
    val rest = if String.substring(line,8,2) = " <"
               then String.substring(line,10,size line - 10)
               else String.substring(line,18,size line - 18)
    val sec_name = hd (String.tokens (fn x => x = #">") rest)
    val hex = if String.substring(line,8,2) = " <"
              then String.substring(line,0,8)
              else String.substring(line,0,16)
    in (hex,sec_name) end handle Empty => fail()
                               | Subscript => fail()
  val ys = drop_until (can dest_section_declaration) xs
  fun split_by_sections [] = []
    | split_by_sections (y::ys) =
        if y = "\n" then split_by_sections ys else (let
          val (location,sec_name) = dest_section_declaration y
          val body = take_until (fn x => x = "\n" orelse x="\r\n") ys
          val ys = drop_until (fn x => x = "\n" orelse x="\r\n") ys
          in (sec_name,location,body) :: split_by_sections ys end
          handle HOL_ERR _ => split_by_sections ys)
  in split_by_sections ys end

(* function that cleans names *)
val remove_dot =
  String.translate (fn c => if mem c [#".",#" "] then "_" else implode [c])

fun format_line sec_name = let
  fun find_first i c s = if String.sub(s,i) = c then i else find_first (i+1) c s
  fun split_at c s =
    (String.substring(s,0,find_first 0 c s),
     String.extract(s,find_first 0 c s+1,NONE))
  fun is_subroutine_call s3 =
    not (String.isPrefix "addi" s3) andalso
    not (String.isPrefix "sd" s3) andalso
    not (String.isPrefix "sw" s3) andalso
    not (String.isPrefix "lw" s3) andalso
    not (String.isPrefix "ld" s3) andalso
    not (String.isPrefix "lbu" s3) andalso
    ((String.isPrefix "bl" s3 andalso not (String.isPrefix "bls" s3)
                              andalso not (String.isPrefix "ble" s3)
                              andalso not (String.isPrefix "blt" s3)) orelse let
     val ts = String.tokens (fn c => mem c [#"<",#">"]) s3
     in 1 < length ts andalso not (el 2 ts = sec_name) andalso
        length (String.tokens (fn x => x = #"+") (el 2 ts)) < 2 end)
  fun format_line_aux line = let
    val (s1,s2) = split_at #":" line
    val s2 = String.extract(s2,1,NONE)
    val (s2,s3) = split_at #"\t" s2
    val s3 = String.extract(s3,0,SOME (size s3 - 1))
    val s1 = if size s1 < 16 then s1 else String.substring(s1,8,size s1 - 8)
    val i = Arbnum.toInt(Arbnum.fromHexString s1)
    val s2 = if String.isPrefix ".word" s3 then "const:" ^ s2 else s2
    val s2 = if String.isPrefix "ldrls\tpc," s3 then "switch:" ^ s2 else s2
    val s2 = ((if is_subroutine_call s3
               then "call:" ^ remove_dot
                 (el 2 (String.tokens (fn x => mem x [#"<",#">"]) s3)) ^ ":" ^ s2
               else s2)
              handle HOL_ERR _ => s2)
    val f = String.translate (fn c => if c = #" " then "" else
              implode [c])
    in (i,f s2,s3) end
    handle Subscript => (fail())
  in format_line_aux end

fun read_complete_sections filename filename_sigs ignore = let
  (* helper functions *)
  fun try_map f [] = []
    | try_map f (x::xs) = (f x :: try_map f xs) handle HOL_ERR _ => try_map f xs
  (* read basic section info *)
  val all_sections = read_sections filename
  val is_riscv = let
    val xs = lines_from_file filename
    in exists (fn s => String.isSubstring "riscv" s) xs end
  val is_arm8 = let
    val xs = lines_from_file filename
    in exists (fn s => String.isSubstring "aarch64" s) xs end
  (* read in signature file *)
  val ss = lines_from_file filename_sigs
  fun every p [] = true
    | every p (x::xs) = p x andalso every p xs
  val is_blank = every (fn c => mem c [#" ",#"\n",#"\t"]) o explode
  val ss = filter (not o is_blank) ss
  val bytes_in_word = (if is_riscv then 8 else 4)
  fun process_sig_line line = let
    val ts0 = String.tokens (fn x => mem x [#" ",#"\n"]) line
    val ts = filter (fn s => s <> "struct") ts0
    val sec_name = el 2 ts
    val returns_struct = (hd ts0 = "struct")
    val ret_length = if hd ts = "0" then 0 else
                     max(string_to_int (hd ts),bytes_in_word) div bytes_in_word
    val arg_lengths = map string_to_int (tl (tl ts))
    val arg_lengths = map (fn x => max(x,bytes_in_word) div bytes_in_word) arg_lengths
    in (sec_name,(arg_lengths,ret_length,returns_struct)) end
  val ss_alist = map process_sig_line ss
  (* combine section info with signatures *)
  val default_sig = ([]:int list,0,false)
  fun lookup x [] = (add_missing_sig x; default_sig(*fail()*))
    | lookup x ((y,z)::ys) = if x = y then z else lookup x ys
  fun combine_ss (sec_name,location,body) =
    (sec_name,lookup (hd (String.tokens (fn x => x = #".") sec_name)) ss_alist,location,body)
  val all_sections = try_map combine_ss all_sections
  (* process section bodies *)
  fun process_body (sec_name,io,location,body) =
    (remove_dot sec_name,io,location,
        if mem sec_name ignore then [] else try_map (format_line sec_name) body)
  val all_sections = map process_body all_sections
  (* location function *)
  fun update x y f a = if x = a then y else f a
  val find_section = foldl (fn ((sec_name,_,location,_),x) => update location sec_name x) (fn x => fail()) all_sections
  (* calculate dependencies *)
  fun get_deps (sec_name,io,location,body) = let
    val calls = body
          |> filter (fn (_,s,_) => String.isPrefix "call:" s)
          |> map (fn (_,s,_) => el 2 (String.tokens (fn x => x = #":") s) handle Subscript => "")
          |> filter (fn s => length (String.tokens (fn x => x = #"+") s) < 2)
    val consts = body
          |> filter (fn (_,s,_) => String.isPrefix "const:" s)
          |> map (fn (_,s,_) => el 2 (String.tokens (fn x => x = #":") s) handle Subscript => "")
          |> try_map find_section
    val deps = all_distinct (calls @ consts)
    in (sec_name,io,location,body,deps) end
  val all_sections = map get_deps all_sections
  (* annotate constants with function names whenever they match *)
  fun annotate_consts (sec_name,io,location,body,deps) = let
    fun annotate (x,line,y) = let
      val _ = String.isPrefix "const:" line orelse fail()
      val c = el 2 (String.tokens (fn x => x = #":") line)
      val sec_name = find_section c
      in (x,line ^ ":" ^ sec_name,y) end handle HOL_ERR _ => (x,line,y)
   in (sec_name,io,location,map annotate body,deps) end
  val all_sections = map annotate_consts all_sections
  fun compare_secs (_,_,_,body1,deps1) (_,_,_,body2,deps2) =
    if length deps1 < length deps2 then true else
    if length deps2 < length deps1 then false else
      (length body1 <= length deps2)
  (* guess arch *)
  val arch = let
    fun has_short_instr (_,_,_,lines,_) =
      exists (fn (_,hex,_) => size hex < 8) lines
    in if is_riscv then RISCV else
       if is_arm8 then ARM8 else
       if exists has_short_instr all_sections then M0 else ARM end
  val _ = (arch_name := arch)
  in complete_sections := sort compare_secs all_sections end

fun section_info sec_name = let
  fun f [] = failwith ("Can't find info for section: " ^ sec_name)
    | f ((name,io,location,body,deps)::xs) =
        if sec_name = name then (io,(location,(body,deps))) else f xs
  in f (!complete_sections) end

fun section_names () =
  map (fn (sec_name,io,location,body,deps) => sec_name) (!complete_sections);

val section_io = fst o section_info
val section_location = fst o snd o section_info
val section_body = fst o snd o snd o section_info
fun section_deps name = (snd o snd o snd o section_info) name handle HOL_ERR _ => []
fun section_length name = length (section_body name) handle HOL_ERR _ => 0

(*
  val base_name = "loop-riscv/example"
  val base_name = "kernel-riscv/kernel-riscv"
  val base_name = "example-arm8/SysModel"
  val ignore = [""]
*)

fun read_files base_name ignore = let
  val _ = set_base (base_name ^ "_")
  fun n_times 0 f x = x | n_times n f x = n_times (n-1) f (f x)
  val long_line = n_times 70 (fn x => "=" ^ x) "\n"
  val _ = print long_line
  val _ = print ("  Base name: "^base_name^"\n")
  val _ = print ("  Poly/ML: "^(int_to_string (PolyML.rtsVersion()))^"\n")
  val _ = print ("  HOL: "^(HOL_version ())^"\n")
  val _ = print long_line
  (* file names *)
  fun get_filename suffix = base_name ^ suffix;
  val filename = get_filename ".elf.txt";
  val filename_sigs = get_filename ".sigs";
  (* read sections *)
  val () = read_complete_sections filename filename_sigs ignore
  (* print stats *)
  val f = print
  val names = section_names ()
  val lengths = map (fn n => (n, (length o section_body) n)) names
  val _ = print long_line
  val names_count = (int_to_string (length names))
  val inst_count = (int_to_string (sum (map snd lengths)))
  val _ = f ("  Total: " ^ names_count ^ " functions, " ^ inst_count ^
             " " ^ arch_str () ^ " instructions\n")
  fun list_max [] = fail()
    | list_max [x] = x
    | list_max ((x,x1)::(y,y1)::xs) =
        if x1 < y1 then list_max ((y,y1)::xs) else list_max ((x,x1)::xs)
  val (longest_name,l) = list_max lengths
  val _ = f ("  Longest function: " ^ longest_name ^ " (" ^(int_to_string l) ^
             " instructions)\n")
  val dep_counts = map (length o section_deps) names |> all_distinct
  fun print_dep_count_line n = let
    fun max_string_length n [] s = s
      | max_string_length n (x::xs) s =
          if size (s ^ ", " ^ x) < n then
            max_string_length n xs (s ^ ", " ^ x) else s ^ ", ..."
    val deps = filter (fn s => length (section_deps s) = n) names
    val s = "  " ^ int_to_string n ^ " deps: " ^ int_to_string (length deps) ^
            " functions ("
    in max_string_length 65 (tl deps) (s ^ hd deps) ^ ")\n" end
  val _ = map (print o print_dep_count_line) dep_counts
  val _ = print long_line
  in () end;

val int_to_hex = (fn s => "0x" ^ s) o to_lower o
                 Arbnum.toHexString o Arbnum.fromInt

fun show_annotated_code ann sec_name = let
  val code = section_body sec_name
  val l = hd code |> #1
  val code = map (fn (x,y,z) => (x,x-l,z)) code
  val loc_width = last code |> #1 |> int_to_hex |> size
  val offset_width = (last code |> #2 |> int_to_hex |> size) + 4
  fun left_pad k s = if size s < k then left_pad k (" " ^ s) else s
  fun right_pad k s = if size s < k then right_pad k (s ^ " ") else s
  fun line (loc,offset,asm) = let
    val s1 = left_pad loc_width (int_to_hex loc)
    val s2 = left_pad offset_width (int_to_hex offset)
    val asm = String.tokens (fn c => c = #";") asm |> hd
              |> String.translate (fn c => if c = #"\r" then "" else
                                           if c = #"\t" then " " else implode [c])
    val s3 = right_pad 20 asm ^ "  ; " ^ ann loc handle HOL_ERR _ => asm
    in s1 ^ s2 ^ "    " ^ s3 ^ "\n" end
  val _ = write_blank_line ()
  val _ = write_indented_block (concat (map line code))
  val _ = write_blank_line ()
  in () end

val show_code = show_annotated_code (fn x => fail())

(* tools *)

val () = arm_progLib.arm_config "vfpv3" "mapped"
val arm_tools = arm_decompLib.l3_arm_tools
val (arm_spec,_,_,_) = arm_tools

val arm8_tools = arm8_decompLib.arm8_tools
val (arm8_spec,_,_,_) = arm8_tools

val () = m0_progLib.m0_config false (* not bigendian *) "mapped"
val m0_tools = m0_decompLib.l3_m0_tools
val (m0_spec,_,_,_) = m0_tools

val () = riscv_progLib.riscv_config true (* set id yo 0 *)
val riscv_tools = riscv_decompLib.riscv_tools
val (riscv_spec,_,_,_) = riscv_tools

fun get_tools () =
  case !arch_name of
    ARM   => arm_tools
  | ARM8  => arm8_tools
  | M0    => m0_tools
  | RISCV => riscv_tools ;

fun tysize () =
  case !arch_name of
    ARM   => ``:32``
  | ARM8  => ``:64``
  | M0    => ``:32``
  | RISCV => ``:64`` ;

fun wsize () = ``:^(tysize ()) word``;

end
