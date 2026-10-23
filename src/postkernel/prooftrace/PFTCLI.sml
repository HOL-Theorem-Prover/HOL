structure PFTCLI :> PFTCLI = struct

val usage =
  "Usage: pft emit --ruleset hol4|candle --trace FILE --output FILE\n\
  \       pft preamble --output FILE\n\
  \       pft compute-preamble --output FILE\n\
  \       pft merge --ruleset hol4|candle --output FILE\n\
  \         [--order FILE] [--input FILE ...]\n\
  \         [--target 'THEORY$THEOREM' ...] [--all THEORY ...]\n\
  \         [--save-defs]\n\n\
  \The order file lists one binary PFT path per line, dependencies first.\n\
  \Paths in it are relative to the order file. Blank lines are ignored.\n\
  \--order expands at its position among repeated --input arguments.\n"

fun fail msg = raise Fail ("pft: " ^ msg)

fun required name NONE = fail ("missing " ^ name)
  | required _ (SOME value) = value

fun set_once name dst value =
  case !dst of
    NONE => dst := SOME value
  | SOME _ => fail ("repeated " ^ name)

fun trim s =
  let
    val n = size s
    fun left i = if i < n andalso Char.isSpace (String.sub(s,i))
                 then left (i+1) else i
    val a = left 0
    fun right i = if i > a andalso Char.isSpace (String.sub(s,i-1))
                  then right (i-1) else i
  in String.substring(s, a, right n - a) end

fun read_order file =
  let
    val ins = TextIO.openIn file
    val dir = OS.Path.dir file
    fun lines acc =
      case TextIO.inputLine ins of
        NONE => rev acc
      | SOME line =>
          let val path = trim line
          in if path = "" then lines acc
             else lines
               ((if OS.Path.isAbsolute path then path
                 else OS.Path.concat(dir, path)) :: acc)
          end
  in (lines [] before TextIO.closeIn ins)
     handle exn => (TextIO.closeIn ins; raise exn)
  end

fun target save_defs s =
  case String.fields (fn c => c = #"$") s of
    [thy, name] =>
      if thy = "" orelse name = "" then
        fail ("invalid --target " ^ s ^ "; expected THEORY$THEOREM")
      else PFTMerge.ThyThm(thy, name, save_defs)
  | _ => fail ("invalid --target " ^ s ^ "; expected THEORY$THEOREM")

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
          (set_once "--trace" trace value; parse rest)
      | parse ("--output" :: value :: rest) =
          (set_once "--output" output value; parse rest)
      | parse ("--ruleset" :: value :: rest) =
          (set_once "--ruleset" rs value; parse rest)
      | parse (arg :: _) = fail ("unknown or incomplete emit option " ^ arg)
    val () = parse args
    val rs = ruleset (required "--ruleset" (!rs))
    val trace = required "--trace" (!trace)
    val output = required "--output" (!output)
  in PFTEmit.emit_expect := false;
     PFTEmit.emit_theory
       {trace=trace, output=output, binary=true, ruleset=rs}
  end

fun preamble ["--output", output] =
      PFTCandlePreamble.emit {output=output, binary=true}
  | preamble _ = fail "preamble requires --output FILE"

fun compute_preamble ["--output", output] =
      PFTCandleComputePreamble.emit_file {output=output, binary=true}
  | compute_preamble _ = fail "compute-preamble requires --output FILE"

fun merge args =
  let
    val output = ref NONE
    val rs = ref NONE
    val inputs = ref []
    val names = ref []
    val theories = ref []
    val save_defs = ref false
    fun parse [] = ()
      | parse ("--output" :: value :: rest) =
          (set_once "--output" output value; parse rest)
      | parse ("--ruleset" :: value :: rest) =
          (set_once "--ruleset" rs value; parse rest)
      | parse ("--order" :: value :: rest) =
          (inputs := rev (read_order value) @ !inputs; parse rest)
      | parse ("--input" :: value :: rest) =
          (inputs := value :: !inputs; parse rest)
      | parse ("--target" :: value :: rest) =
          (names := value :: !names; parse rest)
      | parse ("--all" :: value :: rest) =
          (theories := value :: !theories; parse rest)
      | parse ("--save-defs" :: rest) = (save_defs := true; parse rest)
      | parse (arg :: _) = fail ("unknown or incomplete merge option " ^ arg)
    val () = parse args
    val rs = required "--ruleset" (!rs)
    val _ = ruleset rs
    val output = required "--output" (!output)
    val inputs = rev (!inputs)
    val targets = map (target (!save_defs)) (rev (!names)) @
                  map (fn thy => PFTMerge.ThyAll(thy, !save_defs))
                      (rev (!theories))
    val () = List.app (fn file =>
      let val {ruleset, ...} =
            PFTReader.read_header {file=file, binary=true}
      in if ruleset = rs then ()
         else fail ("ruleset " ^ ruleset ^ " in " ^ file ^ "; expected " ^ rs)
      end) inputs
  in PFTMerge.merge
       {inputs=inputs, targets=targets, output=output, binary=true}
  end

fun main [] = fail usage
  | main ["--help"] = print usage
  | main ("emit" :: args) = emit args
  | main ("preamble" :: args) = preamble args
  | main ("compute-preamble" :: args) = compute_preamble args
  | main ("merge" :: args) = merge args
  | main (arg :: _) = fail ("unknown command " ^ arg ^ "\n" ^ usage)

end
