val theory_width = 30


structure Process = OS.Process

val args0 = CommandLine.arguments()

fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             Process.exit Process.failure)

fun mkquiet {bequiet, diffsort, files} =
    {bequiet = true, diffsort = diffsort, files = files}
fun mkdiff {bequiet, diffsort, files} =
    {bequiet = bequiet, diffsort = true, files = files}

fun getargs args =
    case args of
      [] => {bequiet = false, diffsort = false, files = []}
    | "-q" :: rest => mkquiet (getargs rest)
    | "-d" :: rest => mkdiff (getargs rest)
    | _ => {bequiet = false, diffsort = false, files = args}

val {bequiet,diffsort,files = args} = getargs args0

val _ = if null args then die "Must specify at least one file to \"analyse\""
        else ()

val _ = if length args <> 2 andalso diffsort then
          die "-d option not appropriate when #files <> 2"
        else ()

val base = hd args

fun print_dashes () =
    (print (StringCvt.padLeft #"-" (15 * length args + theory_width) "");
     print "\n")

fun read_file (fname,m) = let
  val instr = TextIO.openIn fname
  fun recurse m =
    case TextIO.inputLine instr of
      NONE => m
    | SOME s => let
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

val base_theories =
    if diffsort then let
        val [file1, file2] = args
        fun nzero NONE = 0.0
          | nzero (SOME r) = r
        fun get f thy = nzero (lookup final_map f thy)
        fun compare (thy1, thy2) = let
          val t11 = get file1 thy1
          val t12 = get file1 thy2
          val t21 = get file2 thy1
          val t22 = get file2 thy2
        in
          Real.compare (t21 - t11, t22 - t12)
        end
      in
        Listsort.sort compare base_theories
      end
    else base_theories

fun fmt_fname s = let
  val s' = if size s > 14 then String.extract(s, size s - 14, NONE) else s
in
  StringCvt.padLeft #" " 15 s'
end

fun centered25 s = let
  open StringCvt
in
  padLeft #" " 15 s
end

fun fmt_real r = centered25 (Real.fmt (StringCvt.FIX (SOME 3)) r)

val _ = if not bequiet then
          (print (StringCvt.padLeft #" " theory_width "");
           app (print o fmt_fname) args;
           print "\n";
           print_dashes())
        else ()

fun print_line m thyname = let
  open StringCvt
  fun print_entry fname =
      case lookup m fname thyname of
        NONE => print (centered25 "--")
      | SOME r => print (fmt_real r)
in
  print (StringCvt.padRight #" " theory_width thyname);
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


val _ = if not bequiet then
          (print_dashes();
           print (StringCvt.padRight #" " theory_width "Total");
           app print_entry args;
           print "\n")
        else ()
