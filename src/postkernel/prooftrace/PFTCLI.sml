structure PFTCLI :> PFTCLI = struct

val usage =
  "Usage: pft emit --ruleset hol4|candle --trace FILE --output FILE\n\
  \       pft preamble --output FILE\n\
  \       pft compute-preamble --output FILE\n"

fun fail msg = raise Fail ("pft: " ^ msg)

fun required name NONE = fail ("missing " ^ name)
  | required _ (SOME value) = value

fun ruleset "hol4" = PFTEmit.HOL4
  | ruleset "candle" = PFTEmit.Candle
  | ruleset s = fail ("unsupported ruleset " ^ s ^ "; expected hol4|candle")

fun emit args =
  let
    val trace = ref NONE
    val output = ref NONE
    val rs = ref NONE
    fun parse [] = ()
      | parse ("--trace" :: value :: rest) =
          (trace := SOME value; parse rest)
      | parse ("--output" :: value :: rest) =
          (output := SOME value; parse rest)
      | parse ("--ruleset" :: value :: rest) =
          (rs := SOME value; parse rest)
      | parse (arg :: _) = fail ("unknown or incomplete emit option " ^ arg)
    val () = parse args
    val rs = ruleset (required "--ruleset" (!rs))
    val trace = required "--trace" (!trace)
    val output = required "--output" (!output)
  in PFTEmit.emit_expect := false;
     PFTEmit.emit_theory
       {trace=trace, output=output, ruleset=rs}
  end

fun preamble ["--output", output] =
      PFTCandlePreamble.emit {output=output}
  | preamble _ = fail "preamble requires --output FILE"

fun compute_preamble ["--output", output] =
      PFTCandleComputePreamble.emit_file {output=output}
  | compute_preamble _ = fail "compute-preamble requires --output FILE"

fun main [] = fail usage
  | main ["--help"] = print usage
  | main ("emit" :: args) = emit args
  | main ("preamble" :: args) = preamble args
  | main ("compute-preamble" :: args) = compute_preamble args
  | main (arg :: _) = fail ("unknown command " ^ arg ^ "\n" ^ usage)

end
