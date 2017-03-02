
val _ =print "\n"

fun die s = (print (s^"\n"); OS.Process.exit OS.Process.failure)

fun assert (s, b) =
    (print (UTF8.padRight #" " 65 s);
     if b() then print "OK\n" else die "FAILED!")


open Redblackset
val es = empty Int.compare

fun m10cmp (i1,i2) = Int.compare(i1 mod 10, i2 mod 10)
val em10 = empty m10cmp
val em3 = add(em10, 3)
val em13 = add(em3, 13)

fun gcSucceeds s res () = UTF8.getChar s = res
fun gcFails s () = (UTF8.getChar s ; false) handle UTF8.BadUTF8 _ => true

val _ = List.app assert [
    ("Redblackset.isSubset({},{})", fn () => isSubset(es,es)),
    ("Redblackset.isSubset({}, {1})",
     (fn () => isSubset(es,addList(es,[1])))),
    ("Redblackset.add replaces EQUAL elements",
     (fn () => listItems em13 = [13])),
    ("UTF8.getChar \"\" = NONE", gcSucceeds "" NONE),
    ("UTF8.getChar 0x41 = #\"A\"", gcSucceeds "A" (SOME(("A", 65), ""))),
    ("UTF8.getChar A\\000 = #\"A\"",
     gcSucceeds "A\000" (SOME(("A", 65), "\000"))),
    ("UTF8.getChar 0x2200 = #\"\226\136\128\"",
     gcSucceeds "\226\136\128" (SOME(("\226\136\128", 8704), ""))),
    ("UTF8.getChar 0x2200A = #\"\226\136\128\"",
     gcSucceeds "\226\136\128A" (SOME(("\226\136\128", 8704), "A"))),
    ("UTF8.getChar 0x2200-0x2000 = #\"\226\136\128\"",
     gcSucceeds "\226\136\128\226\136\128"
                (SOME(("\226\136\128", 8704), "\226\136\128"))),
    ("UTF8.getChar 0x8F fails", gcFails "\128"),
    ("UTF8.getChar \"\\192\\128\" fails", gcFails "\192\168"),
    ("UTF8.getChar \"\\252\\129\\129\\129\\129\\129\" fails",
     gcFails "\252\129\129\129\129\129"),
    ("UF8.getChar \"\\244\\129\" fails", gcFails "\244\129"),
    ("padRight #\" \" on ∀", fn () => UTF8.padRight #" " 5 "∀" = "∀    "),
    ("padRight #\"a\" on ∀", fn () => UTF8.padRight #"a" 5 "∀" = "∀aaaa")
    ]

val _ = OS.Process.exit OS.Process.success
