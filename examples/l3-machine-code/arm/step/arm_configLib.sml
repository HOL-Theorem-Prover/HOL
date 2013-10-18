(* ------------------------------------------------------------------------
   Support for defining the context (antecedent) of an ARM step evaluation
   For example: the architecture version, Thumb or ARM encoding, ...
   ------------------------------------------------------------------------ *)

structure arm_configLib :> arm_configLib =
struct

open HolKernel boolLib bossLib
open armTheory utilsLib

structure Parse =
struct
   open Parse
   val (Type, Term) = parse_from_grammars armTheory.arm_grammars
end

open Parse

val ERR = Feedback.mk_HOL_ERR "arm_evalLib"

(* ----------------------------------------------------------------------- *)

val st = Term.mk_var ("s", Type.mk_type ("arm_state", []))

fun mk_arm_const n = Term.prim_mk_const {Thy = "arm", Name = n}
fun mk_arm_type n = Type.mk_thy_type {Thy = "arm", Tyop = n, Args = []}

(* ----------------------------------------------------------------------- *)

val lower = List.map (List.map utilsLib.lowercase)

val endian_options = lower
   [["le", "little-endian", "LittleEndian"],
    ["be", "big-endian", "BigEndian"]]

val arch_options = lower
   [["v4", "ARMv4"],
    ["v4T", "ARMv4T"],
    ["v5", "v5T", "ARMv5", "ARMv5T"],
    ["v5TE", "ARMv5TE"],
    ["v6", "ARMv6"],
    ["v6K", "ARMv6K"],
    ["v6T2", "ARMv6T2"],
    ["v7", "v7_A", "v7-A", "ARMv7", "ARMv7_A", "ARMv7-A"],
    ["v7_R", "v7-R", "ARMv7_R", "ARMv7-R"]]

val thumb_options =
   [["thumb","thumb2","16-bit","16"],
    ["arm","32-bit","32"]]

val vfp_options = lower
   [["fp", "vfp", "VFPv3"],
    ["nofp", "novfp"]]

val fpr_map_options = lower
   [["map-fpr", "fpr-map"],
    ["no-fpr-map", "no-map-fpr"]]

val gpr_map_options = lower
   [["map-gpr", "gpr-map"],
    ["no-gpr-map", "no-map-gpr"]]

val mem_map_options = lower
   [["map-mem", "mem-map"],
    ["no-mem-map", "no-map-mem"]]

val temporal_options = lower
   [["temporal"],
    ["not-temporal"]]

fun find_pos P =
   let
      fun tail n [] = n
        | tail n (h::t) = if P h then n else tail (n + 1) t
   in
      tail 0
   end

fun isDelim c =
   Char.isPunct c andalso (c <> #"-") andalso (c <> #":") orelse Char.isSpace c

val fromDec = Option.valOf o Int.fromString

val empty_string_set = Redblackset.empty Int.compare

fun process_option P g s d l f =
   let
      val (l, r) = List.partition P l
      val positions = Lib.mk_set (List.map g l)
      val result =
         if List.null positions
            then d
         else if List.length positions = 1
            then f (hd positions)
         else raise ERR "process_option" ("More than one " ^ s ^ " option.")
   in
      (result, r)
   end

fun process_opt opt =
   process_option
      (Lib.C Lib.mem (List.concat opt))
      (fn option => find_pos (Lib.mem option) opt)

val default_options =
   {arch      = mk_arm_const "ARMv7_A",
    bigendian = false,
    thumb     = false,
    vfp       = false,
    gpr_map   = false,
    fpr_map   = false,
    mem_map   = true,
    temporal  = false,
    itblock   = wordsSyntax.mk_wordii (0, 8)}

fun process_options s =
   let
      val l = String.tokens isDelim s
      val l = List.map utilsLib.lowercase l
      val (bigendian, l) =
         process_opt endian_options "Endian"
            (#bigendian default_options) l (fn i => i <> 0)
      val (fpr_map, l) =
         process_opt fpr_map_options "Introduce FPR map"
            (#fpr_map default_options) l (Lib.equal 0)
      val (gpr_map, l) =
         process_opt gpr_map_options "Introduce GPR map"
            (#gpr_map default_options) l (Lib.equal 0)
      val (mem_map, l) =
         process_opt mem_map_options "Introduce MEM map"
            (#mem_map default_options) l (Lib.equal 0)
      val (temporal, l) =
         process_opt temporal_options "Temoporal triple"
            (#temporal default_options) l (Lib.equal 0)
      val (vfp, l) =
         process_opt vfp_options "VFP" (#vfp default_options) l (Lib.equal 0)
      val (arch, l) =
         process_opt arch_options "Arch"
            (#arch default_options) l
            (fn i =>
                mk_arm_const
                  (case i of
                      0 => "ARMv4"   | 1 => "ARMv4T"
                    | 2 => "ARMv5T"  | 3 => "ARMv5TE"
                    | 4 => "ARMv6"   | 5 => "ARMv6K"  | 6 => "ARMv6T2"
                    | 7 => "ARMv7_A" | 8 => "ARMv7_R"
                    | _ => raise ERR "process_options" "Bad Arch option."))
      val (thumb, l) =
         process_opt thumb_options "Thumb"
            (#thumb default_options) l (fn i => i = 0)
      val (itblock, l) =
         process_option
            (String.isPrefix "it:")
            (fn s => fromDec (String.extract (s,3,NONE)))
            "IT block" (#itblock default_options) l
            (fn i => if i < 256
                        then wordsSyntax.mk_wordii (i, 8)
                     else raise ERR "process_options" "Bad IT value.")
   in
      if List.null l
         then {arch = arch,
               bigendian = bigendian,
               thumb = thumb,
               vfp = vfp,
               gpr_map = gpr_map,
               fpr_map = fpr_map,
               mem_map = mem_map,
               temporal = temporal,
               itblock = itblock}
      else raise ERR "process_options"
                 ("Unrecognized option" ^
                  (if List.length l > 1 then "s" else "") ^
                  ": " ^ String.concat (commafy l))
   end

(* ----------------------------------------------------------------------- *)

fun mk_config_terms s =
   let
      val c = process_options s
      fun prop f t = if f c then t else boolSyntax.mk_neg t
   in
      (if #thumb c then [``^st.CPSR.IT = ^(#itblock c)``] else []) @
      [``^st.Architecture = ^(#arch c)``,
       prop #vfp ``^st.Extensions Extension_VFP``,
       prop #bigendian ``^st.CPSR.E``,
       prop #thumb ``^st.CPSR.T``]
   end

fun spec_options s =
   let
      val {gpr_map, fpr_map, mem_map, temporal, ...} = process_options s
   in
      (gpr_map, fpr_map, mem_map, temporal)
   end

(* ----------------------------------------------------------------------- *)

end
