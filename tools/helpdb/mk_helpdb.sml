(* this is a script that is run as part of the HOL configuration process,
   it doesn't compile into object code *)

val _ = print "Compiling help database code and creating DB\n";

val _ = app load ["Lexing", "Nonstdio"];


val current_dir = FileSys.getDir()
val _ = let
  val compiler  = fullPath [mosmldir, "bin/mosmlc"]
  val lexer  = fullPath [mosmldir, "bin/mosmllex"]
  val yaccer  = fullPath [mosmldir, "bin/mosmlyac"]
  val _ = FileSys.chDir (fullPath [holdir, "tools", "helpdb"])
  fun concat_wspaces [] = ""
    | concat_wspaces [x] = x
    | concat_wspaces (x::xs) = x ^ " " ^ concat_wspaces xs
  fun systeml l = let
    val command = concat_wspaces l
  in
    if Process.system command = Process.success then
      ()
    else
      (print ("Executing\n  "^command^"\nfailed.\n");
       raise Fail "")
  end
in
  systeml [compiler, "-c", "Database.sig"];
  systeml [compiler, "-c", "Database.sml"];
  systeml [lexer, "DBtokens.lex"];
  systeml [yaccer, "DBparse.grm"];
  systeml [compiler, "-c", "DBparse.sig"];
  systeml [compiler, "-c", "DBparse.sml"];
  systeml [compiler, "-c", "DBtokens.sig"];
  systeml [compiler, "-c", "DBtokens.sml"];
  systeml [compiler, "-c", "build_db.sml"];
  systeml [compiler, "-o", "build_db", "build_db.uo"];
  systeml [fullPath [FileSys.getDir(), "build_db"], "textdb",
           fullPath [holdir, "help", "HOLdbase"]]
end

val _ = FileSys.chDir current_dir;


