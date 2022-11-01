signature arm_random_testingLib =
sig

  include Abbrev

  datatype encoding = ARM | Thumb | Thumb2 | ThumbEE

  datatype arch = ARMv4
                | ARMv4T
                | ARMv5T
                | ARMv5TE
                | ARMv6
                | ARMv6K
                | ARMv6T2
                | ARMv7_A
                | ARMv7_R

  datatype class = DataProcessing
                 | LoadStore
                 | Branch
                 | StatusAccess
                 | Miscellaneous

  datatype step_output
    = Simple_step of (term * term) list
    | Conditional_step of term * (term * term) list * (term * term) list

  val arm_step_updates : string -> string -> term list * step_output

  val generate_random : arch -> encoding -> class ->
                        (string * string * term list * (term * term) list)

  val generate_opcode : arch -> encoding -> string ->
                        (string * string * term list * (term * term) list)

  val generate_opcode_nop : arch -> encoding -> string ->
                            (string * string * term list * (term * term) list)

  val instruction_type : encoding -> string -> string

end
