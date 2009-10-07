signature arm_random_testingLib =
sig

  include Abbrev

  datatype arch = ARMv4
                | ARMv4T
                | ARMv5T
                | ARMv5TE
                | ARMv6
                | ARMv6K
                | ARMv6T2
                | ARMv7_A
                | ARMv7_R
                | ARMv7_M

  datatype class = DataProcessing
                 | LoadStore
                 | Branch
                 | StatusAccess
                 | Miscellaneous

  val generate_random : arch -> class ->
                        (string * string * term list * (term * term) list)

end
