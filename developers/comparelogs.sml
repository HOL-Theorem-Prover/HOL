val args = CommandLine.arguments()

val base = hd args

fun print_dashes () =
    (print (StringCvt.padLeft #"-" (25 * length args + 20) "");
     print "\n")


fun read_file (fname,m) = let
  val instr = TextIO.openIn fname
  fun recurse m =
    case TextIO.inputLine instr of
      "" => m
    | s => let
        val [thyname, number_s] = String.tokens Char.isSpace s
        val number = valOf (Real.fromString number_s)
        val basemap =
            case Binarymap.peek(m, fname) of
              NONE => Binarymap.mkDict String.compare
            | SOME m0 => m0
        val submap = Binarymap.insert(basemap, thyname, number)
      in
        recurse (Binarymap.insert(m, fname, submap))
      end
in
  recurse m before TextIO.closeIn instr
end

val final_map = List.foldl read_file (Binarymap.mkDict String.compare) args

fun lookup m fname thy =
    case Binarymap.peek(m, fname) of
      NONE => NONE
    | SOME m' => Binarymap.peek(m', thy)

val base_theories =
    map #1 (Binarymap.listItems (Binarymap.find(final_map, base)))

fun fmt_fname s = let
  val s' = if size s > 24 then String.extract(s, size s - 24, NONE) else s
in
  StringCvt.padLeft #" " 25 s'
end

fun centered25 s = let
  open StringCvt
in
  padRight #" " 25 (padLeft #" " 20 s)
end

fun fmt_real r = centered25 (Real.fmt (StringCvt.FIX (SOME 3)) r)

val _ = (print (StringCvt.padLeft #" " 20 "");
         app (print o fmt_fname) args;
         print "\n";
         print_dashes())

fun print_line m thyname = let
  open StringCvt
  fun print_entry fname =
      case lookup m fname thyname of
        NONE => print (centered25 "--")
      | SOME r => print (fmt_real r)
in
  print (StringCvt.padRight #" " 20 thyname);
  app print_entry args;
  print "\n"
end

val _ = app (print_line final_map) base_theories

fun calc_totals m = let
  fun calc_file (fname, m0) = let
    fun foldthis (thy, subtot) = let
      val r = case lookup m fname thy of NONE => 0.0 | SOME v => v
    in
      subtot + r
    end
  in
    Binarymap.insert(m0, fname, List.foldl foldthis 0.0 base_theories)
  end
in
  List.foldl calc_file (Binarymap.mkDict String.compare) args
end

val total_map = calc_totals final_map
fun print_entry fname = let
  open StringCvt
in
  print (fmt_real (Binarymap.find(total_map, fname)))
end


val _ = (print_dashes();
         print (StringCvt.padRight #" " 20 "Total");
         app print_entry args;
         print "\n")


