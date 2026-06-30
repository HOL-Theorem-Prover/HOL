(* gen_lander [--fragment <path>] BOOK_TOML...

   Emit Manual/book/index.html on stdout: a static landing page
   listing one card per manual.  Each `BOOK_TOML` argument is the
   path to a manual's book.toml (e.g., `Manual/Description/book.toml`);
   the manual's directory name (`Description`) becomes the link
   target (`./Description/`), and the `title` and `description`
   fields from the `[book]` table of the .toml fill the card.

   If `--fragment <path>` is supplied, the file at <path> is read
   verbatim and inlined after the manual cards as the page's
   "Reference" area.  The fragment is expected to be HTML body
   content -- the typical producer is HOLPage.emitLanderFragment,
   which lists libraries, theories, syntax, simpsets and indexes
   with URLs relative to Manual/book/.

   The page is intentionally minimal -- system fonts, no JS,
   inline CSS -- so it works statically without any of mdbook's
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
      "      <a href=\"" ^ escape href ^ "\">\n" ^
      "        <strong>" ^ escape title ^ "</strong>\n" ^
      (if desc = "" then ""
       else "        <p>" ^ escape desc ^ "</p>\n") ^
      "      </a>\n" ^
      "    </li>\n"
    end

(* The getting-started block is editorial content authored as arbitrary
   Markdown in Tools/getting-started.md and rendered to an HTML fragment
   by pandoc (see Manual/Holmakefile).  gen_lander inlines that fragment
   verbatim -- just as it does the reference --fragment -- so the markup
   is whatever pandoc produced.  The block shows both on the live website
   and in a local docs build, so links to website pages should be
   absolute URLs (e.g. https://hol-theorem-prover.org/faq.html) while
   in-docs links stay relative (e.g. Tutorial/index.html). *)

fun renderPage (paths, fragment, intro) =
    let
      val cards = String.concat (List.map renderCard paths)
      val introSection =
          case intro of
              NONE => ""
            | SOME body =>
                "  <section class=\"lander-intro\">\n" ^ body ^ "  </section>\n"
      val refSection =
          case fragment of
              NONE => ""
            | SOME body =>
                "  <h2 class=\"section\">Reference</h2>\n" ^
                "  <p class=\"sub\">Generated indexes of installed\
                  \ libraries, theories and signatures.</p>\n" ^
                body
    in
      "<!doctype html>\n\
      \<html lang=\"en\">\n\
      \<head>\n\
      \  <meta charset=\"utf-8\">\n\
      \  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n\
      \  <link href=\"https://fonts.googleapis.com/css?family=Lora\" rel=\"stylesheet\">\n\
      \  <link href=\"https://fonts.googleapis.com/css?family=Bree+Serif\" rel=\"stylesheet\">\n\
      \  <title>HOL4 Documentation</title>\n\
      \  <style>\n\
      \    body {\n\
      \      max-width: 960px;\n\
      \      margin: 4em auto;\n\
      \      padding: 0 1em;\n\
      \      font-family: -apple-system, BlinkMacSystemFont, \"Segoe UI\",\n\
      \        Roboto, Oxygen-Sans, Ubuntu, Cantarell, \"Helvetica Neue\",\n\
      \        sans-serif;\n\
      \      line-height: 1.5;\n\
      \      color: #222;\n\
      \    }\n\
      \    h1 { font-weight: 500; margin-bottom: 0.2em; }\n\
      \    h2.section {\n\
      \      font-weight: 500;\n\
      \      margin-top: 3em;\n\
      \      padding-bottom: 0.3em;\n\
      \      border-bottom: 1px solid #e0e0e0;\n\
      \    }\n\
      \    .sub { color: #666; margin-top: 0; margin-bottom: 2em; }\n\
      \    ul.manuals {\n\
      \      list-style: none;\n\
      \      padding: 0;\n\
      \      display: grid;\n\
      \      grid-template-columns: repeat(auto-fill, minmax(240px, 1fr));\n\
      \      gap: 1em;\n\
      \    }\n\
      \    ul.manuals li {\n\
      \      border: 1px solid #e0e0e0;\n\
      \      border-radius: 4px;\n\
      \    }\n\
      \    ul.manuals li:hover { border-color: #4183c4; }\n\
      \    ul.manuals a {\n\
      \      display: block;\n\
      \      padding: 0.8em 1em;\n\
      \      color: inherit;\n\
      \      text-decoration: none;\n\
      \    }\n\
      \    ul.manuals li:hover strong { text-decoration: underline; }\n\
      \    ul.manuals strong { color: #4183c4; font-size: 1.05em; }\n\
      \    ul.manuals p {\n\
      \      margin: 0.4em 0 0;\n\
      \      color: #555;\n\
      \      font-size: 0.9em;\n\
      \      line-height: 1.4;\n\
      \    }\n\
      \    section.ref-section { margin-bottom: 2em; }\n\
      \    section.ref-section h2 {\n\
      \      font-size: 1.1em;\n\
      \      font-weight: 500;\n\
      \      margin: 1.2em 0 0.3em;\n\
      \    }\n\
      \    section.ref-section h2 small {\n\
      \      font-size: 0.85em;\n\
      \      color: #888;\n\
      \      font-weight: normal;\n\
      \    }\n\
      \    section.ref-section h2 small a { color: #4183c4; }\n\
      \    ul.refs {\n\
      \      list-style: none;\n\
      \      padding: 0;\n\
      \      margin: 0;\n\
      \      display: grid;\n\
      \      grid-template-columns: repeat(auto-fill, minmax(160px, 1fr));\n\
      \      gap: 0.2em 1em;\n\
      \    }\n\
      \    ul.refs a {\n\
      \      color: #4183c4;\n\
      \      text-decoration: none;\n\
      \      font-family: ui-monospace, SFMono-Regular, Menlo, Consolas,\n\
      \        \"Liberation Mono\", monospace;\n\
      \      font-size: 0.95em;\n\
      \    }\n\
      \    ul.refs a:hover { text-decoration: underline; }\n\
      \    ul.refs .nolink {\n\
      \      color: #999;\n\
      \      font-family: ui-monospace, SFMono-Regular, Menlo, Consolas,\n\
      \        \"Liberation Mono\", monospace;\n\
      \      font-size: 0.95em;\n\
      \    }\n\
      \    /* Editorial intro: arbitrary pandoc-rendered Markdown. */\n\
      \    .lander-intro h1, .lander-intro h2 {\n\
      \      font-weight: 500; margin-top: 2em;\n\
      \      padding-bottom: 0.3em; border-bottom: 1px solid #e0e0e0;\n\
      \    }\n\
      \    .lander-intro a { color: #4183c4; text-decoration: none; }\n\
      \    .lander-intro a:hover { text-decoration: underline; }\n\
      \    /* Website nav strip -- echoes the strip on the site sub-pages.\n\
      \       Hidden until the progressive-enhancement script confirms we\n\
      \       are running inside the website. */\n\
      \    .subheader { display: none; text-align: center; padding: 12pt 10pt; line-height: normal; }\n\
      \    .subheader_home {\n\
      \      font-family: 'Lora', serif; font-size: 24pt; font-weight: bold;\n\
      \      background: rgba(255, 255, 255, 1.0); color: black;\n\
      \      border-radius: 10pt; padding: 4pt 14pt; text-decoration: none;\n\
      \      display: inline-block; vertical-align: middle;\n\
      \    }\n\
      \    .subnav { display: inline-block; vertical-align: middle; }\n\
      \    .subnav a {\n\
      \      display: inline-block; background: rgba(0, 0, 0, 0.7);\n\
      \      color: white; border-radius: 1.5vh; padding: 6pt 12pt;\n\
      \      margin: 4pt; text-decoration: none;\n\
      \      font-family: Arial, Helvetica, sans-serif;\n\
      \    }\n\
      \    .subnav a:hover { background: rgba(0, 0, 0, 0.85); }\n\
      \    .subnav a.current { background: rgba(230, 0, 0, 0.85); }\n\
      \    /* Augmented (in-website) presentation: lake photo behind a white\n\
      \       content card, mirroring the main site.  Forced light palette so\n\
      \       the card stays readable even under a dark OS theme. */\n\
      \    html.web-context {\n\
      \      background: url(/images/trindemossen.jpg) center center / cover\n\
      \        fixed no-repeat;\n\
      \      min-height: 100vh;\n\
      \    }\n\
      \    html.web-context body {\n\
      \      background: transparent; margin: 0; max-width: none; padding: 0;\n\
      \    }\n\
      \    /* Match the content-frame width of the website sub-pages\n\
      \       (.textbox in new-look/style.css): 85vw on mobile, 60% on\n\
      \       desktop with 45pt side padding. */\n\
      \    html.web-context .lander {\n\
      \      background: #fff; color: #222;\n\
      \      border-radius: 14px; box-shadow: 0 2px 16px rgba(0, 0, 0, 0.35);\n\
      \      margin: 10pt auto 20pt; max-width: 85vw;\n\
      \      padding: 8pt 5vw 30pt;\n\
      \    }\n\
      \    @media screen and (min-width: 600px) {\n\
      \      html.web-context .lander {\n\
      \        width: 60%; min-width: 400px; max-width: none;\n\
      \        padding-left: 45pt; padding-right: 45pt;\n\
      \      }\n\
      \    }\n\
      \    html.web-context .subheader { display: block; }\n\
      \    html.web-context h1, html.web-context h2 {\n\
      \      font-family: 'Bree Serif', serif;\n\
      \    }\n\
      \    html.web-context h1 { font-size: 32pt; font-weight: bold; }\n\
      \    html.web-context h2 { color: rgba(230, 0, 0, 1.0); }\n\
      \    html.web-context .sub { color: #555; }\n\
      \    html.web-context h2.section { border-color: #e0e0e0; }\n\
      \    html.web-context ul.manuals li { border-color: #e0e0e0; }\n\
      \    html.web-context ul.manuals li:hover { border-color: #4183c4; }\n\
      \    html.web-context ul.manuals strong { color: #4183c4; }\n\
      \    html.web-context ul.manuals p { color: #555; }\n\
      \    html.web-context section.ref-section h2 small { color: #888; }\n\
      \    html.web-context section.ref-section h2 small a,\n\
      \    html.web-context ul.refs a,\n\
      \    html.web-context .lander-intro a { color: #4183c4; }\n\
      \    html.web-context .lander-intro h1,\n\
      \    html.web-context .lander-intro h2 { border-color: #e0e0e0; }\n\
      \    html.web-context ul.refs .nolink { color: #999; }\n\
      \    @media (prefers-color-scheme: dark) {\n\
      \      body { background: #1a1a1a; color: #e0e0e0; }\n\
      \      .sub { color: #aaa; }\n\
      \      h2.section { border-color: #333; }\n\
      \      ul.manuals li { border-color: #333; }\n\
      \      ul.manuals li:hover { border-color: #66aaff; }\n\
      \      ul.manuals strong { color: #66aaff; }\n\
      \      ul.manuals p { color: #b0b0b0; }\n\
      \      section.ref-section h2 small { color: #888; }\n\
      \      section.ref-section h2 small a,\n\
      \      ul.refs a { color: #66aaff; }\n\
      \      ul.refs .nolink { color: #707070; }\n\
      \      .lander-intro h1, .lander-intro h2 { border-color: #333; }\n\
      \      .lander-intro a { color: #66aaff; }\n\
      \      /* In-website dark: dark card over a dimmed photo, matching the\n\
      \         website's dark theme. */\n\
      \      html.web-context body::before {\n\
      \        content: \"\"; position: fixed; inset: 0;\n\
      \        background: rgba(0, 0, 0, 0.55); z-index: -1; pointer-events: none;\n\
      \      }\n\
      \      html.web-context .lander {\n\
      \        background: rgba(28, 28, 28, 0.95); color: #e6e6e6;\n\
      \      }\n\
      \      html.web-context .sub { color: #aaa; }\n\
      \      html.web-context h2 { color: #ff6b6b; }\n\
      \      html.web-context h2.section,\n\
      \      html.web-context .lander-intro h1,\n\
      \      html.web-context .lander-intro h2 { border-color: #444; }\n\
      \      html.web-context ul.manuals li { border-color: #444; }\n\
      \      html.web-context ul.manuals li:hover { border-color: #6fa8ff; }\n\
      \      html.web-context ul.manuals strong { color: #6fa8ff; }\n\
      \      html.web-context ul.manuals p { color: #bbb; }\n\
      \      html.web-context section.ref-section h2 small { color: #aaa; }\n\
      \      html.web-context section.ref-section h2 small a,\n\
      \      html.web-context ul.refs a,\n\
      \      html.web-context .lander-intro a { color: #6fa8ff; }\n\
      \      html.web-context ul.refs .nolink { color: #888; }\n\
      \      html.web-context .subheader_home {\n\
      \        background: rgba(20, 20, 20, 0.92); color: #f0f0f0;\n\
      \      }\n\
      \    }\n\
      \  </style>\n\
      \  <script>\n\
      \    /* Decide synchronously, before first paint, whether this page is\n\
      \       served inside the HOL website (docs always live under /docs/...)\n\
      \       rather than as a standalone/local docs build (file:, or book/\n\
      \       served at the root by Tools/mdbook-preview.py).  Setting the\n\
      \       class here in <head> styles the first paint and avoids a flash. */\n\
      \    if (location.protocol !== 'file:' &&\n\
      \        location.pathname.indexOf('/docs/') === 0) {\n\
      \      document.documentElement.className += ' web-context';\n\
      \    }\n\
      \  </script>\n\
      \</head>\n\
      \<body>\n\
      \  <div class=\"subheader\">\n\
      \    <a class=\"subheader_home\" href=\"/\">HOL</a>\n\
      \    <nav class=\"subnav\">\n\
      \      <a href=\"/about.html\">About</a>\n\
      \      <a href=\"/install.html\">Download &amp; Install</a>\n\
      \      <a href=\"/docs/latest/\" class=\"current\">Documentation</a>\n\
      \      <a href=\"/community.html\">Community</a>\n\
      \    </nav>\n\
      \  </div>\n\
      \  <main class=\"lander\">\n\
      \  <h1>HOL4 Documentation</h1>\n\
      \  <p class=\"sub\">Documentation for the HOL4 theorem prover.</p>\n" ^
      introSection ^
      "  <h2 class=\"section\">Manuals</h2>\n\
      \  <ul class=\"manuals\">\n" ^
      cards ^
      "  </ul>\n" ^
      refSection ^
      "  </main>\n\
      \</body>\n\
      \</html>\n"
    end

(* Parse leading `--fragment <path>` and `--getting-started <path>`
   flags, in any order.  Returns (fragment_opt, getting_started_opt,
   rest). *)
fun parseArgs args =
    let
      fun loop (frag, gs) ("--fragment" :: p :: rest) = loop (SOME p, gs) rest
        | loop (frag, gs) ("--getting-started" :: p :: rest) =
            loop (frag, SOME p) rest
        | loop (frag, gs) rest = (frag, gs, rest)
    in loop (NONE, NONE) args end

fun readOpt what NONE = NONE
  | readOpt what (SOME p) =
      SOME (readFile p
            handle IO.Io _ => die ("gen_lander: cannot read " ^ what ^ " " ^ p))

fun main () =
    let
      val (fragPath, gsPath, paths) = parseArgs (CommandLine.arguments ())
      val fragment = readOpt "fragment" fragPath
      val intro = readOpt "getting-started" gsPath
    in
      case paths of
          [] => die "Usage: gen_lander [--fragment <path>] \
                    \[--getting-started <path>] BOOK_TOML..."
        | _  => emit (renderPage (paths, fragment, intro))
    end
