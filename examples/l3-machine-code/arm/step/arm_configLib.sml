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

val ERR = Feedback.mk_HOL_ERR "arm_configLib"

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

val default_options =
   {arch      = mk_arm_const "ARMv7_A",
    bigendian = false,
    thumb     = false,
    vfp       = false,
    itblock   = wordsSyntax.mk_wordii (0, 8)}

fun isDelim c =
   Char.isPunct c andalso (c <> #"-") andalso (c <> #":") orelse Char.isSpace c

fun process_options s =
   let
      val l = String.tokens isDelim s
      val l = List.map utilsLib.lowercase l
      val (bigendian, l) = process_opt endian_options "Endian"
                              (#bigendian default_options) l (fn i => i <> 0)
      val (vfp, l) =
         process_opt vfp_options "VFP" (#vfp default_options) l (Lib.equal 0)
      val (arch, l) =
         process_opt arch_options "Arch" (#arch default_options) l
            (fn i =>
                mk_arm_const
                  (case i of
                      0 => "ARMv4"   | 1 => "ARMv4T"
                    | 2 => "ARMv5T"  | 3 => "ARMv5TE"
                    | 4 => "ARMv6"   | 5 => "ARMv6K"  | 6 => "ARMv6T2"
                    | 7 => "ARMv7_A" | 8 => "ARMv7_R"
                    | _ => raise ERR "process_options" "Bad Arch option."))
      val (thumb, l) = process_opt thumb_options "Thumb"
                          (#thumb default_options) l (fn i => i = 0)
      val (itblock, l) =
         process_option (String.isPrefix "it:")
            (fn s =>
               Option.valOf (Int.fromString (String.extract (s, 3, NONE))))
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
               itblock = itblock}
      else raise ERR "process_options"
                 ("Unrecognized option" ^
                  (if List.length l > 1 then "s" else "") ^
                  ": " ^ String.concat (commafy l))
   end

(* ----------------------------------------------------------------------- *)

local
   val architecture = ``^st.Architecture``
   val extension_vfp = ``^st.Extensions Extension_VFP``
   val cpsr_it = ``^st.CPSR.IT``
   val cpsr_e = ``^st.CPSR.E``
   val cpsr_t = ``^st.CPSR.T``
in
   fun mk_config_terms s =
      let
         val c = process_options s
         fun prop f t = if f c then t else boolSyntax.mk_neg t
         fun eq t f = boolSyntax.mk_eq (t, f c)
      in
         (if #thumb c then [eq cpsr_it (#itblock)] else []) @
         [eq architecture (#arch),
          prop #vfp extension_vfp,
          prop #bigendian cpsr_e,
          prop #thumb cpsr_t]
      end
end

(* ----------------------------------------------------------------------- *)

end
