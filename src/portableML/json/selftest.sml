open JSONStreamParser

fun die s =
    (print s; OS.Process.exit OS.Process.failure)

fun id x = x
val cbs : string list callbacks =
    {null = id,
     string = (fn (ss,s) => s :: ss),
     integer = #1,
     float = #1,
     boolean = #1,
     objectKey = #1,
     startArray = id,
     endArray = id,
     startObject = id,
     endObject = id,
     error = print o #2}

val _ = print (StringCvt.padRight #" " 70
                                  "Checking strings present in test.json")

val _ = case Exn.capture (parse cbs) (openFile "test.json", []) of
            Exn.Exn e => die ("\nUnexpected exception: "^General.exnMessage e)
          | Exn.Res r =>
            if r = ["another string", "¬(∃x. x ≤ 3)"] then print "OK\n"
            else die ("\nIncorrect output: [" ^
                      String.concatWith ", " r ^ "]\n")
