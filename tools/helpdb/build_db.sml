fun usage() =
  (print "Usage: ";
   print (CommandLine.name());
   print " <textDBfile> <compiledDB>\n")

val (inputfile, outputfile) =
  case CommandLine.arguments () of
    [inp,out] => (inp,out)
  | _ => (usage(); Process.exit Process.failure)

fun createLexerStream is =
  Lexing.createLexer (fn buff => fn n => Nonstdio.buff_input is buff 0 n)

val strm = BasicIO.open_in inputfile handle _ =>
  (print ("Couldn't find file "^inputfile^"\n"); Process.exit Process.failure)
val lbf = createLexerStream strm
val entries = DBparse.entrylist DBtokens.lextoken lbf
val db = Database.fromList entries

val _ =  Database.writebase (outputfile, db)

val _ = Process.exit Process.success

