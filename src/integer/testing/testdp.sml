open HolKernel boolLib readproblemfile

fun print s = (TextIO.print s ; TextIO.flushOut TextIO.stdOut)

fun classify_result thm = let
  val tm = concl thm
  val r = rhs tm
  val (c,_) = dest_const r
in
  case c of
    "T" => "T"
  | "F" => "F"
  | _ => "?"
end handle HOL_ERR _ => "?"

fun size t = let
  val (_, args) = strip_comb t
in
  if null args then 0
  else 1 + List.foldl (fn (t,n) => size t + n) 0 args
end

fun analyse_term proc t = let
  val timer = Timer.startCPUTimer()
  val result = SOME (proc t) handle HOL_ERR _ => NONE
  val {usr,sys,gc} = Timer.checkCPUTimer timer
  val usrtime = Time.toString usr
  val verdict =
    case result of
      NONE => "U "
    | SOME thm => classify_result thm^" "
in
  verdict^usrtime
end

fun compare (t0,n) = let
  val t = valOf t0
  fun doproc p = let
    val fav = analyse_term p (gen_all t)
    val _ = (print fav; print " / ")
    val exv = analyse_term p (list_mk_exists(free_vars t,t))
  in
    print exv
  end
in
  print (StringCvt.padRight #" " 6 (Int.toString n ^ "."));
  print (" "^Int.toString (length (free_vars t)));
  print (" "^StringCvt.padLeft #" " 3 (Int.toString (size t))^" ");
  doproc numLib.ARITH_CONV;
  print " -- ";
  doproc Cooper.COOPER_CONV;
  print "\n";
  (n + 1)
end

val _ = readproblemfile.foldl compare 0 TextIO.stdIn
