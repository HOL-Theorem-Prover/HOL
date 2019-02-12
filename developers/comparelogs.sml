structure comparelogs =
struct

val theory_width = 30


structure Process = OS.Process


fun die s = (TextIO.output(TextIO.stdErr, s ^ "\n");
             Process.exit Process.failure)

fun mkquiet {bequiet, diffsort, files, averages} =
    {bequiet = true, diffsort = diffsort, files = files, averages = averages}
fun mkdiff {bequiet, diffsort, files, averages} =
    {bequiet = bequiet, diffsort = true, files = files, averages = averages}
fun mkaverages {bequiet, diffsort, files, averages} =
    {bequiet = bequiet, diffsort = diffsort, files = files, averages = true}


fun usage_msg appname =
    "Usage:\n  " ^ appname ^ " file1 file2 ... filen\n\n" ^
    "Options:\n\
    \  -a    Ouput averages for each line\n\
    \  -d    Sort results in order of the differences (only with two files)\n\
    \  -h    Show this help message\n\
    \  -q    Print raw data only, no sums, or fancy lines; (output to other tools)\n\
    \  -?    Show this help message\n"

fun show_usage appname =
  (print (usage_msg appname); Process.exit Process.success)


fun getargs appname args =
  let
    fun recurse args =
      case args of
        [] => {bequiet = false, diffsort = false, files = [], averages = false}
       | "-a" :: rest => mkaverages (recurse rest)
       | "-q" :: rest => mkquiet (recurse rest)
       | "-d" :: rest => mkdiff (recurse rest)
       | "-h" :: _ => show_usage appname
       | "-?" :: _ => show_usage appname
       | _ => {bequiet = false, diffsort = false, files = args,averages = false}
  in
    recurse args
  end

fun print_dashes n =
    (print (StringCvt.padLeft #"-" (15 * n + theory_width) "");
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

fun lookup m fname thy =
    case Binarymap.peek(m, fname) of
      NONE => NONE
    | SOME m' => Binarymap.peek(m', thy)

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

fun suml [] = 0.0
  | suml (r::rs) = r + suml rs
fun average [] = 0.0
  | average ls = suml ls / real (length ls)

fun fmt_real r = centered25 (Real.fmt (StringCvt.FIX (SOME 3)) r)
fun print_line m args thyname = let
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

fun print_entry total_map fname = let
  open StringCvt
in
  print (fmt_real (Binarymap.find(total_map, fname)))
end

fun main() = let
  val args0 = CommandLine.arguments()
  val {bequiet,diffsort,files = args,averages} =
      getargs (CommandLine.name()) args0

  val _ = if null args then die "Must specify at least one file to \"analyse\""
          else ()

  val _ = if length args <> 2 andalso diffsort then
            die "-d option not appropriate when #files <> 2"
          else ()

  val _ = if averages then
            if diffsort then die "-d and -a incompatible"
            else if length args < 2 then die "Need >= 2 files for -a option"
            else ()
          else ()

  val base = hd args
  val final_map = List.foldl read_file (Binarymap.mkDict String.compare) args
  val base_theories =
      map #1 (Binarymap.listItems (Binarymap.find(final_map, base)))
      handle NotFound => die ("No data in base file: "^hd args)
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

  fun insert_list (m, k, v) =
      case Binarymap.peek (m,k) of
          NONE => Binarymap.insert(m,k,[v])
        | SOME vs => Binarymap.insert(m,k,v::vs)
  fun combine_for_averages m =
      let
        (* m a map from filenames to maps from theory-names to times;
           output a map from theory-names to average times
        *)
        fun perfile(fname, fmap, A) =
            let
              fun pertheory (thyname, thytime, A) =
                  insert_list (A, thyname, thytime)
            in
              Binarymap.foldl pertheory A fmap
            end
      in
        Binarymap.foldl perfile (Binarymap.mkDict String.compare) m
      end

  val _ = if not bequiet andalso not averages then
            (print (StringCvt.padLeft #" " theory_width "");
             app (print o fmt_fname) args;
             print "\n";
             print_dashes (length args))
          else ()
in
  if averages then
    let
      val map' = combine_for_averages final_map
      fun pertheory(thy, times, A) = (thy, average times) :: A
      val data = Binarymap.foldr pertheory [] map'
    in
      app (fn (thy,avgtime) =>
              print (StringCvt.padRight #" " theory_width thy ^
                     fmt_real avgtime ^ "\n"))
          data
    end
  else
    let
      val _ = app (print_line final_map args) base_theories
      val total_map = calc_totals final_map
    in
      if not bequiet then
        (print_dashes (length args);
         print (StringCvt.padRight #" " theory_width "Total");
         app (print_entry total_map) args;
         print "\n")
      else ()
    end
end

end (* struct *)
