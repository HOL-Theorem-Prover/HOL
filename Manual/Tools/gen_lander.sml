(* gen_lander BOOK_TOML...

   Emit Manual/book/index.html on stdout: a static landing page
   listing one card per manual.  Each argument is the path to a
   manual's book.toml (e.g., `Manual/Description/book.toml`);
   the manual's directory name (`Description`) becomes the link
   target (`./Description/`), and the `title` and `description`
   fields from the `[book]` table of the .toml fill the card.

   The page is intentionally minimal — system fonts, no JS,
   inline CSS — so it works statically without any of mdbook's
   per-book assets.  The per-manual mdbooks live at sibling
   subdirectories of Manual/book/. *)

fun readFile path =
    let val s = TextIO.openIn path
        val all = TextIO.inputAll s
        val () = TextIO.closeIn s
    in all end

fun die msg =
    ( TextIO.output (TextIO.stdErr, msg ^ "\n")
    ; OS.Process.exit OS.Process.failure )

fun emit s = TextIO.output (TextIO.stdOut, s)

(* TOML extraction: look for `<key> = "<value>"` lines inside the
   `[book]` section, before any `[other-section]` header.  Strips
   surrounding whitespace.  Doesn't handle multi-line strings,
   inline tables, or escaped quotes — none of which appear in our
   book.toml files.  Returns NONE if the key isn't found. *)
fun trim s =
    let val ss = Substring.full s
        val ss = Substring.dropl Char.isSpace ss
        val ss = Substring.dropr Char.isSpace ss
    in Substring.string ss end

fun extractBookKey key content =
    let
      val lines = String.fields (fn c => c = #"\n") content
      val keyPrefix = key ^ "="
      val keyPrefixSp = key ^ " ="
      fun stripPrefix prefix s =
          if String.isPrefix prefix s
          then SOME (String.extract (s, size prefix, NONE))
          else NONE
      fun matchKey ln =
          let val t = trim ln
          in
            case stripPrefix keyPrefix t of
                SOME rest => SOME (trim rest)
              | NONE =>
                  case stripPrefix keyPrefixSp t of
                      SOME rest => SOME (trim rest)
                    | NONE => NONE
          end
      fun unquote s =
          let val n = size s
          in if n >= 2 andalso String.sub (s, 0) = #"\""
                andalso String.sub (s, n - 1) = #"\""
             then SOME (String.substring (s, 1, n - 2))
             else NONE
          end
      (* state = NotYetInBook | InBook | LeftBook *)
      datatype state = NotYetInBook | InBook | LeftBook
      fun isSectionHeader t =
          size t >= 2 andalso String.sub (t, 0) = #"["
      fun loop [] _ = NONE
        | loop (ln :: rest) state =
          let val t = trim ln
          in
            case state of
                LeftBook => NONE
              | NotYetInBook =>
                  if t = "[book]" then loop rest InBook
                  else loop rest NotYetInBook
              | InBook =>
                  if isSectionHeader t then NONE
                  else case matchKey ln of
                           SOME rhs => unquote rhs
                         | NONE => loop rest InBook
          end
    in loop lines NotYetInBook end

(* HTML escape just enough for our use: & < > and double-quote. *)
fun escape s =
    let
      fun esc #"&"  = "&amp;"
        | esc #"<"  = "&lt;"
        | esc #">"  = "&gt;"
        | esc #"\"" = "&quot;"
        | esc c     = String.str c
    in String.translate esc s end

(* From `Manual/Description/book.toml` return `Description`. *)
fun manualName path =
    let
      val {dir, ...} = OS.Path.splitDirFile path
      val {file, ...} = OS.Path.splitDirFile dir
    in file end

(* Per-manual card: title (linked) + description paragraph. *)
fun renderCard path =
    let
      val content = readFile path
                    handle IO.Io _ =>
                      die ("gen_lander: cannot read " ^ path)
      val title = case extractBookKey "title" content of
                      SOME t => t
                    | NONE => die ("gen_lander: no `title` in [book] of " ^ path)
      val desc = Option.getOpt
                   (extractBookKey "description" content,
                    "")
      val name = manualName path
      val href = name ^ "/index.html"
    in
      "    <li>\n" ^
      "      <a href=\"" ^ escape href ^ "\"><strong>" ^
        escape title ^ "</strong></a>\n" ^
      (if desc = "" then ""
       else "      <p>" ^ escape desc ^ "</p>\n") ^
      "    </li>\n"
    end

fun renderPage paths =
    let
      val cards = String.concat (List.map renderCard paths)
    in
      "<!doctype html>\n\
      \<html lang=\"en\">\n\
      \<head>\n\
      \  <meta charset=\"utf-8\">\n\
      \  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
      \  <title>HOL Manuals</title>\n\
      \  <style>\n\
      \    body {\n\
      \      max-width: 720px;\n\
      \      margin: 4em auto;\n\
      \      padding: 0 1em;\n\
      \      font-family: -apple-system, BlinkMacSystemFont, \"Segoe UI\",\n\
      \        Roboto, Oxygen-Sans, Ubuntu, Cantarell, \"Helvetica Neue\",\n\
      \        sans-serif;\n\
      \      line-height: 1.5;\n\
      \      color: #222;\n\
      \    }\n\
      \    h1 { font-weight: 500; margin-bottom: 0.2em; }\n\
      \    .sub { color: #666; margin-top: 0; margin-bottom: 2em; }\n\
      \    ul.manuals { list-style: none; padding: 0; }\n\
      \    ul.manuals li {\n\
      \      margin-bottom: 1.5em;\n\
      \      padding: 1em 1.2em;\n\
      \      border: 1px solid #e0e0e0;\n\
      \      border-radius: 4px;\n\
      \    }\n\
      \    ul.manuals li:hover { border-color: #4183c4; }\n\
      \    ul.manuals a { color: #4183c4; text-decoration: none; }\n\
      \    ul.manuals a:hover { text-decoration: underline; }\n\
      \    ul.manuals strong { font-size: 1.1em; }\n\
      \    ul.manuals p { margin: 0.4em 0 0; color: #555; }\n\
      \    @media (prefers-color-scheme: dark) {\n\
      \      body { background: #1a1a1a; color: #e0e0e0; }\n\
      \      .sub { color: #aaa; }\n\
      \      ul.manuals li { border-color: #333; }\n\
      \      ul.manuals li:hover { border-color: #66aaff; }\n\
      \      ul.manuals a { color: #66aaff; }\n\
      \      ul.manuals p { color: #b0b0b0; }\n\
      \    }\n\
      \  </style>\n\
      \</head>\n\
      \<body>\n\
      \  <h1>HOL Manuals</h1>\n\
      \  <p class=\"sub\">Documentation for the HOL4 theorem prover.</p>\n\
      \  <ul class=\"manuals\">\n" ^
      cards ^
      "  </ul>\n\
      \</body>\n\
      \</html>\n"
    end

fun main () =
    case CommandLine.arguments () of
        [] => die "Usage: gen_lander BOOK_TOML..."
      | paths => emit (renderPage paths)
