open JSONStreamParser

fun die s =
    (print s; OS.Process.exit OS.Process.failure)

fun tprint s = print (StringCvt.padRight #" " 70 s)

fun check (name, test) =
    (tprint name; if test () then print "OK\n" else die "FAILED\n")

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

val _ = tprint "Checking strings present in test.json"

val _ = case Exn.capture (parse cbs) (openFile "test.json", []) of
            Exn.Exn e => die ("\nUnexpected exception: "^General.exnMessage e)
          | Exn.Res r =>
            if r = ["another string", "¬(∃x. x ≤ 3)"] then print "OK\n"
            else die ("\nIncorrect output: [" ^
                      String.concatWith ", " r ^ "]\n")

fun valueEq (JSON.OBJECT xs, JSON.OBJECT ys) = fieldListEq (xs, ys)
  | valueEq (JSON.ARRAY xs, JSON.ARRAY ys) = valueListEq (xs, ys)
  | valueEq (JSON.NULL, JSON.NULL) = true
  | valueEq (JSON.BOOL x, JSON.BOOL y) = x = y
  | valueEq (JSON.INT x, JSON.INT y) = x = y
  | valueEq (JSON.FLOAT x, JSON.FLOAT y) = Real.== (x, y)
  | valueEq (JSON.STRING x, JSON.STRING y) = x = y
  | valueEq _ = false
and fieldListEq ([], []) = true
  | fieldListEq ((key1, value1)::xs, (key2, value2)::ys) =
      key1 = key2 andalso valueEq (value1, value2) andalso fieldListEq (xs, ys)
  | fieldListEq _ = false
and valueListEq ([], []) = true
  | valueListEq (x::xs, y::ys) =
      valueEq (x, y) andalso valueListEq (xs, ys)
  | valueListEq _ = false

fun parseValue s = let
  val source = JSONParser.openString s
  val value = JSONParser.parse source
in
  JSONParser.close source;
  value
end

fun outputOf printer value = let
  val filename = "json-printer-selftest.out"
  val outstream = TextIO.openOut filename
  val _ = printer (outstream, value)
  val _ = TextIO.closeOut outstream
  val instream = TextIO.openIn filename
  val result = TextIO.inputAll instream
in
  TextIO.closeIn instream;
  result
end

val nested =
    JSON.OBJECT
      [("items",
        JSON.ARRAY [JSON.INT (~42), JSON.FLOAT 1.25,
                    JSON.STRING ("quote: \"\n" ^ "\226\136\128")]),
       ("empty", JSON.OBJECT [])]

val _ = check
  ("JSONPrinter compact nested-value round trip",
   fn () => valueEq (nested, parseValue (JSONPrinter.valueToString nested)))

val _ = List.app check
  [("JSONPrinter escapes quote",
    fn () => JSONPrinter.valueToString (JSON.STRING "\"") = "\"\\\"\""),
   ("JSONPrinter escapes backslash",
    fn () => JSONPrinter.valueToString (JSON.STRING "\\") = "\"\\\\\""),
   ("JSONPrinter escapes backspace",
    fn () => JSONPrinter.valueToString (JSON.STRING "\b") = "\"\\b\""),
   ("JSONPrinter escapes form feed",
    fn () => JSONPrinter.valueToString (JSON.STRING "\f") = "\"\\f\""),
   ("JSONPrinter escapes newline",
    fn () => JSONPrinter.valueToString (JSON.STRING "\n") = "\"\\n\""),
   ("JSONPrinter escapes carriage return",
    fn () => JSONPrinter.valueToString (JSON.STRING "\r") = "\"\\r\""),
   ("JSONPrinter escapes tab",
    fn () => JSONPrinter.valueToString (JSON.STRING "\t") = "\"\\t\""),
   ("JSONPrinter escapes other controls",
    fn () => JSONPrinter.valueToString (JSON.STRING "\001") = "\"\\u0001\""),
   ("JSONPrinter prints negative integers",
    fn () => JSONPrinter.valueToString (JSON.INT (~42)) = "-42"),
   ("JSONPrinter prints floats",
    fn () => JSONPrinter.valueToString (JSON.FLOAT 1.25) = "1.25"),
   ("JSONPrinter preserves UTF-8",
    fn () => JSONPrinter.valueToString (JSON.STRING "\226\136\128") =
             "\"\226\136\128\"")]

val formatted =
    JSON.OBJECT [("answer", JSON.INT (~42)),
                 ("array", JSON.ARRAY [JSON.BOOL true, JSON.NULL])]

val _ = check
  ("JSONPrinter.print emits compact JSON",
   fn () => outputOf JSONPrinter.print formatted =
            "{\"answer\":-42,\"array\":[true,null]}")

val _ = check
  ("JSONPrinter.printFmt emits formatted JSON",
   fn () => outputOf JSONPrinter.printFmt formatted =
            ("{\n  \"answer\": -42,\n  \"array\": [\n    true,\n" ^
             "    null\n  ]\n}"))

fun rejectsNonFinite f =
    (JSONPrinter.valueToString (JSON.FLOAT f); false) handle Fail _ => true

val _ = check
  ("JSONPrinter rejects infinite floats", fn () => rejectsNonFinite Real.posInf)

val _ = check
  ("JSONPrinter rejects NaN floats",
   fn () => rejectsNonFinite (Real.posInf - Real.posInf))
