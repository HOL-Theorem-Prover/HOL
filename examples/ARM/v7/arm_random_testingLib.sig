signature arm_random_testingLib =
sig

  include Abbrev

  datatype encoding = ARM | Thumb | Thumb2

  datatype arch = ARMv4
                | ARMv4T
                | ARMv5T
                | ARMv5TE
                | ARMv6
                | ARMv6K
                | ARMv6T2
                | ARMv7_A
                | ARMv7_R
             (* | ARMv7_M *)

  datatype class = DataProcessing
                 | LoadStore
                 | Branch
                 | StatusAccess
                 | Miscellaneous

  val generate_random : arch -> encoding -> class ->
                        (string * string * term list * (term * term) list)

  val generate_opcode : arch -> encoding -> string ->
                        (string * string * term list * (term * term) list)

  val generate_opcode_nop : arch -> encoding -> string ->
                            (string * string * term list * (term * term) list)

  val instruction_type : encoding -> string -> string

end
