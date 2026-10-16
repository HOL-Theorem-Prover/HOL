
val _ =print "\n";

infix |>
fun x |> f = f x

fun die s = (print (s^"\n"); OS.Process.exit OS.Process.failure)

fun tprint s = print (UTF8.padRight #" " 65 s)

fun assert (s, b) =
    (tprint s; if b() then print "OK\n" else die "FAILED!")

fun testf str f x resprint expected =
    let
      val _ = tprint str
      val res = Exn.capture f x
    in
      case res of
          Exn.Exn e => die ("Unexpected exception: " ^ General.exnMessage e)
        | Exn.Res r => if r = expected then print "OK\n"
                       else die ("Unexpected result: " ^ resprint r)
    end


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
    ("UTF8.getChar \"\\244\\129\" fails", gcFails "\244\129"),
    ("padRight #\" \" on ∀", fn () => UTF8.padRight #" " 5 "∀" = "∀    "),
    ("padRight #\"a\" on ∀", fn () => UTF8.padRight #"a" 5 "∀" = "∀aaaa"),
    ("UTF8.substring(\"a\", 0, 1)", fn () => UTF8.substring("a", 0, 1) = "a"),
    ("UTF8.substring(\"abc\", 0, 3)",
     fn () => UTF8.substring("abc", 0, 3) = "abc"),
    ("UTF8.substring(\"abc\", 1, 3)",
     fn () => (UTF8.substring("abc", 1, 3); false) handle Subscript => true
                                                        | e => false),
    ("UTF8.substring(\"ab\", 1, 1)", fn () => UTF8.substring("ab", 1, 1) = "b"),
    ("UTF8.substring(\"«ab»\", 1, 2)",
     fn () => UTF8.substring("«ab»", 1, 2) = "ab")
    ]

val _ = tprint "mapFilter executes L-to-R"
val _ = let
  val r = ref 0
  fun f x = (r := x; if x mod 2 = 1 then raise Fail "foo" else x + 1)
  val res = Portable.mapfilter f [1,2,3,4]
in
  if res = [3,5] then
    if !r = 4 then print "OK\n"
    else die ("\n Evaluation in wrong order; !r = " ^ Int.toString (!r))
  else
    die ("\n Evaluation gave wrong result: [" ^
         String.concatWith ", " (map Int.toString res) ^ "]")
end

val _ = tprint "Checking HOLsexp-reading"
val _ = let
  open HOLsexp
  val el1 = Cons(Symbol "bar", Symbol "baz")
  val I = Integer
  val el2 = List [Quote, List [I 1,I 2,I 3,String "\203a\"", String"foo\n",
                               Symbol "1+", String "xy\028"]]
  val t_out = List[Symbol "foo ", el1, el2]
  val outstrm = TextIO.openOut "test.sexp"
  val _ = TextIO.output(outstrm,
                        ";; this is an automatically generated test file\n")
  val _ = TextIO.output(outstrm, HOLPP.pp_to_string 70 printer t_out ^
                                 "; another comment \n")
  val _ = TextIO.closeOut outstrm
  val t_in = HOLsexp_parser.raw_read_file "test.sexp"
in
  if t_in = t_out then print "OK\n"
  else
    die ("FAILED, read back:\n  "^
         HOLPP.pp_to_string 70 printer t_in)
end

val _ = testf "PIntMap size after duplicate add"
              PIntMap.size
              (let open PIntMap in
               empty |> add 10 "a" |> add 5 "c" |> add 10 "b"
               end)
              Int.toString
              2

val _ = testf "PIntMap size after hitting remove"
              PIntMap.size
              (let open PIntMap in
               empty |> add 10 "a" |> add 5 "c" |> remove 10
               end)
              Int.toString
              1

val _ = testf "PIntMap size after missing remove"
              PIntMap.size
              (let open PIntMap in
               empty |> add 10 "a" |> add 5 "c" |> remove 11
               end)
              Int.toString
              2

local
  open TheoryDat
  fun with_file text f =
      let val path = OS.FileSys.tmpName ()
          val out = TextIO.openOut path
          val _ = TextIO.output (out, text)
          val _ = TextIO.closeOut out
          fun cleanup () = OS.FileSys.remove path
          val r = f path handle e => (cleanup (); raise e)
      in cleanup (); r end
  fun header ps = "(theory (\"child\" " ^ ps ^ ") (core-data "
  fun pair thy hash = "(\"" ^ thy ^ "\" . \"" ^ hash ^ "\")"
  fun rejects text =
      with_file text (fn p => case read_parents p of
                                 Failure _ => true | _ => false)
in
  val _ = assert ("TheoryDat empty parent header", fn () =>
    with_file (header "") (fn p => read_parents p = Success []))
  val _ = assert ("TheoryDat bootstrap identity", fn () =>
    with_file (header (pair "min" "")) (fn p =>
      null (validate {path = p, resolve = fn _ => raise Fail "resolved min"})))
  val _ = assert ("TheoryDat wrong bootstrap identity", fn () =>
    with_file (header (pair "min" "wrong")) (fn p =>
      case validate {path = p, resolve = fn _ => Missing} of
          [HashMismatch _] => true | _ => false))
  val _ = assert ("TheoryDat strict header parsing", fn () =>
    List.all rejects
      ["", "junk " ^ header "", "(theory (\"child\"",
       "(theory (\"child\" (\"min\" . \"\"))",
       header (pair "parent" "bad"),
       header (pair "min" "" ^ pair "min" ""),
       "(theory (\"child\") (core-data-bogus "])
  val _ = assert ("TheoryDat comments and escaped names", fn () =>
    let val hash = String.implode (List.tabulate (40, fn _ => #"a"))
        val text = "; prefix\n(theory ; tag\n(\"child\"\n" ^
                   "(\"pa\\\"rent\\\\name\\110\" ; name\n. \"" ^ hash ^
                   "\")) ; parentage\n(core-data "
    in with_file text (fn p =>
         read_parents p =
         Success [{thy = "pa\"rent\\namen", hash = hash}]) end)
  val _ = assert ("TheoryDat rejects each truncated header prefix", fn () =>
    let val text = header (pair "min" "")
    in List.all (fn n => rejects (String.substring (text, 0, n)))
                (List.tabulate (size text, fn n => n)) end)
  val _ = assert ("TheoryDat rejects malformed string escapes", fn () =>
    List.all rejects
      [header (pair "mi\\q" ""), header (pair "mi\\999" ""),
       header (pair "mi\\12" ""), header (pair "mi\\^a" "")])
  val _ = assert ("TheoryDat deliberately ignores malformed body", fn () =>
    with_file (header (pair "min" "") ^ "BROKEN ((\"unterminated")
      (fn p => read_parents p = Success [{thy = "min", hash = ""}] andalso
               null (validate {path = p, resolve = fn _ => Missing})))
  val _ = assert ("TheoryDat parent-like body text is not parentage", fn () =>
    with_file (header "" ^ pair "min" "wrong")
      (fn p => read_parents p = Success []))
  val _ = assert ("TheoryDat missing header file is a failure", fn () =>
    let val path = OS.FileSys.tmpName ()
        val _ = OS.FileSys.remove path handle OS.SysErr _ => ()
    in case read_parents path of Failure _ => true | _ => false end)
  val _ = assert ("TheoryDat normal parent chain", fn () =>
    with_file (header (pair "min" "")) (fn base =>
      let val baseHash = SHA1.sha1_file {filename = base}
      in with_file (header (pair "base" baseHash)) (fn middle =>
        let val middleHash = SHA1.sha1_file {filename = middle}
        in with_file (header (pair "middle" middleHash)) (fn leaf =>
          null (validate {path = middle,
                          resolve = fn "base" => Artifact base
                                     | _ => Missing}) andalso
          null (validate {path = leaf,
                          resolve = fn "middle" => Artifact middle
                                     | _ => Missing})) end) end))
  val _ = assert ("TheoryDat parent byte identity and failures", fn () =>
    with_file "parent artifact bytes" (fn parent =>
      let val hash = SHA1.sha1_file {filename = parent}
      in with_file (header (pair "parent" hash)) (fn child =>
        null (validate {path = child,
                        resolve = fn _ => Artifact parent}) andalso
        (case validate {path = child, resolve = fn _ => Missing} of
             [MissingParent _] => true | _ => false) andalso
        (case validate {path = child,
                        resolve = fn _ => Ambiguous [parent, parent]} of
             [AmbiguousParent _] => true | _ => false) andalso
        (case validate {path = child,
                        resolve = fn _ => raise Fail "resolver failed"} of
             [ResolverError _] => true | _ => false) andalso
        let val absent = OS.FileSys.tmpName ()
            val _ = OS.FileSys.remove absent handle OS.SysErr _ => ()
        in case validate {path = child, resolve = fn _ => Artifact absent} of
               [UnreadableParent _] => true | _ => false end andalso
        with_file "different bytes" (fn other =>
          case validate {path = child, resolve = fn _ => Artifact other} of
              [HashMismatch _] => true | _ => false)) end))
end

val _ = OS.Process.exit OS.Process.success
