structure Holdep_tokens :> Holdep_tokens =
struct

infix |>
fun x |> f = f x

exception LEX_ERROR of string
type result = (string,int) Binarymap.dict
open HOLFileSys

datatype char_reader = CR of {reader : unit -> string,
                              current : char option,
                              maxpos : int,
                              buffer : string,
                              closer : unit -> unit,
                              pos : int}
(* invariants:
    * buffer = "" ⇒ current = NONE ∧ maxpos = 0 ∧ pos = 0
    * 0 ≤ pos ≤ maxpos
*)

fun current (CR {current = c, ...}) = c
fun make inp close = let
  val newbuf = inp()
in
  if newbuf = "" then CR {pos = 0, maxpos = 0, buffer = newbuf,
                          reader = inp, current = NONE,
                          closer = close}
  else CR {pos = 0, maxpos = size newbuf - 1, buffer = newbuf,
           reader = inp, current = SOME(String.sub(newbuf, 0)),
           closer = close}
end
fun fromFile f = let
  val is = openIn f
in
  make (fn () => input is) (fn () => closeIn is)
end
fun fromStream is = make (fn () => input is) (fn () => ())
fun fromReader uc = make (fn () => case uc() of NONE => "" | SOME c => str c)
                         (fn () => ())
fun closeCR (CR {closer,...}) = closer()

fun advance (c as CR {pos, buffer, maxpos, reader, current, closer}) =
    if pos < maxpos then
      CR { pos = pos + 1, buffer = buffer, reader = reader,
           current = SOME(String.sub(buffer, pos + 1)),
           maxpos = maxpos, closer = closer }
    else if buffer = "" then c
    else make reader closer

(* What the scan remembers about the modules the file defines for
   itself; `dropSelfBound' below says what it is for.

     - `depth' counts the `struct' / `sig' / `let' / `local' /
       `abstype' bodies open at this point.  Those are the only
       constructs SML closes with `end', so counting their keywords
       against `end' tracks nesting without parsing.
     - `awaiting' means the last keyword was a top-level `structure',
       so the next identifier is the name it binds.
     - `binder' is the name of the binding whose declaration we are
       inside, with the depth it started at.
     - `ends' maps such a name to the position just past the end of
       its declaration, and `first' maps every identifier recorded as
       a dependency to the position just past its first occurrence. *)
type selfbind = {depth : int,
                 awaiting : bool,
                 binder : (string * int) option,
                 ends : (string,int) Binarymap.dict,
                 first : (string,int) Binarymap.dict}

datatype SCR = SCR of {linenum : int,
                       filename : string,
                       colnum : int,
                       pos : int,
                       ids : (string,int) Binarymap.dict,
                       sb : selfbind,
                       cr : char_reader}


fun SCRfromNamedCR (name, cr) =
  SCR { linenum = 1, colnum = 0, pos = 0, filename = name,
        ids = Binarymap.mkDict String.compare,
        sb = {depth = 0, awaiting = false, binder = NONE,
              ends = Binarymap.mkDict String.compare,
              first = Binarymap.mkDict String.compare},
        cr = cr }

fun makeSCR fname = SCRfromNamedCR (fname, fromFile fname)
fun SCRfromStream (name, is) = SCRfromNamedCR (name, fromStream is)
fun SCRfromReader (name, uc) = SCRfromNamedCR (name, fromReader uc)

fun currentChar (SCR{cr,...}) = current cr
fun closeSCR (SCR{cr,...}) = closeCR cr
fun inc (SCR {linenum, filename, colnum, pos, ids, sb, cr}) =
    SCR{linenum = linenum, filename = filename, colnum = colnum + 1,
        pos = pos + 1, ids = ids, sb = sb, cr = advance cr}
fun newline (SCR{linenum, filename, colnum, pos, ids, sb, cr}) =
    SCR{linenum = linenum + 1, filename = filename, colnum = 0,
        pos = pos + 1, ids = ids, sb = sb, cr = advance cr}
fun completeID s (SCR{linenum, filename, colnum, pos, ids, sb, cr}) = let
  val {depth, awaiting, binder, ends, first} = sb
in
  SCR{linenum = linenum, filename = filename, colnum = colnum, pos = pos,
      ids = case Binarymap.peek(ids,s) of
                NONE => Binarymap.insert(ids, s, linenum)
              | SOME _ => ids,
      sb = {depth = depth, awaiting = awaiting, binder = binder, ends = ends,
            first = case Binarymap.peek(first,s) of
                        NONE => Binarymap.insert(first, s, pos)
                      | SOME _ => first},
      cr = cr}
end

fun mem x [] = false
  | mem x (y::ys) = x = y orelse mem x ys
val SMLsyms = String.explode "!%&$+/:<=>?@~|#*\\-~^"
val symbools = List.tabulate(256, fn i => mem (Char.chr i) SMLsyms)
val symb_vec = Vector.fromList symbools
fun isSMLSym c = Vector.sub(symb_vec, Char.ord c)

fun isSMLAlphaCont c =
    Char.isAlphaNum c orelse c = #"_" orelse c = #"'"

(* The constructs SML closes with `end'.  Nothing else does, so the
   difference between these and `end' is the nesting depth. *)
val blockOpeners = ["struct", "sig", "let", "local", "abstype"]
(* A keyword that can only begin a new declaration, and so ends the
   one before it.  Used to find where `structure M = N' stops, which
   opens no block for an `end' to close. *)
val decKeywords = ["val", "fun", "datatype", "abstype", "type",
                   "exception", "structure", "signature", "functor",
                   "open", "include", "local", "infix", "infixl",
                   "infixr", "nonfix"]

(* An alphabetic keyword or identifier has just been read, outside any
   comment or string literal.  Move the self-binding state over it. *)
fun sbNote nm (SCR{linenum,filename,colnum,pos,ids,sb,cr}) = let
  val {depth, awaiting, binder, ends, first} = sb
  fun put sb' = SCR{linenum = linenum, filename = filename, colnum = colnum,
                    pos = pos, ids = ids, sb = sb', cr = cr}
in
  if awaiting then
    put {depth = depth, awaiting = false, binder = SOME (nm, depth),
         ends = ends, first = first}
  else let
    (* The binding ends at the `end' that takes us back to the depth
       it started at, or -- when its right-hand side opened no block --
       at the next declaration keyword written at that depth. *)
    val leaving =
        case binder of
            NONE => false
          | SOME (_, d) => if nm = "end" then depth - 1 <= d
                           else depth = d andalso mem nm decKeywords
    val (binder', ends') =
        case (leaving, binder) of
            (true, SOME (m, _)) =>
              (NONE, case Binarymap.peek (ends, m) of
                         NONE => Binarymap.insert (ends, m, pos)
                       | SOME _ => ends)
          | _ => (binder, ends)
    (* Clamped: a file we cannot nest correctly must not be made to
       look as though a binding had been left. *)
    val depth' = if nm = "end" then Int.max (0, depth - 1)
                 else if mem nm blockOpeners then depth + 1
                 else depth
  in
    put {depth = depth', awaiting = nm = "structure" andalso depth' = 0,
         binder = binder', ends = ends', first = first}
  end
end

fun Error(SCR {filename,colnum,linenum,...}, msg) =
    raise LEX_ERROR (filename^" "^Int.toString linenum ^ "." ^
                     Int.toString colnum ^ " " ^ msg)



fun clean_open scr =
    case currentChar scr of
        NONE => scr
      | SOME #"d" => openTermPFX "datatype" 1 (inc scr)
      | SOME #"e" => opene (inc scr) (* exception, end *)
      | SOME #"f" => openf (inc scr) (* fun, functor *)
      | SOME #"i" => openi (inc scr) (* in, infixl, infix, infixr *)
      | SOME #"l" => openTermPFXsb "local" 1 (inc scr)
      | SOME #"n" => openTermPFX "nonfix" 1 (inc scr)
      | SOME #"o" => modTermPFX true "open" 1 (clean_open, clean_open) (inc scr)
      | SOME #"p" => openTermPFX "prim_val" 1 (inc scr)
      | SOME #"s" => opens (inc scr) (* structure, signature *)
      | SOME #"t" => openTermPFX "type" 1 (inc scr)
      | SOME #"v" => openTermPFX "val" 1 (inc scr)
      | SOME #";" => clean_initial (inc scr)
      | SOME #"(" => openLPAREN (inc scr)
      | SOME #"#" => openHASH (inc scr)
      | SOME #"\n" => clean_open (newline scr)
      | SOME c => if Char.isSpace c then clean_open (inc scr)
                  else if Char.isAlpha c then
                    modAlphaID true clean_open ("", [c]) (scr |> inc)
                  else if isSMLSym c then
                    modSymID true clean_open [c] (scr |> inc)
                  else Error(scr, "Bad character >"^str c^"< after open")
and openTermPFX kstr c scr =
    modTermPFX true kstr c (clean_initial, clean_open) scr
(* As `openTermPFX', for the keywords an `open' list can end at that
   also move the self-binding state: `end', `local' and `structure'
   mean there what they mean anywhere else. *)
and openTermPFXsb kstr c scr =
    modTermPFX true kstr c (fn s => clean_initial (sbNote kstr s), clean_open)
               scr
and openOnKWord kstr scr = OnKWord true kstr (clean_initial, clean_open) scr
and opene scr =
    case currentChar scr of
        NONE => scr |> completeID "e"
      | SOME #"n" => openTermPFXsb "end" 2 (inc scr)
      | SOME #"x" => openTermPFX "exception" 2 (inc scr)
      | SOME c => extend_openAlpha "e" c scr
and openf scr =
    case currentChar scr of
        NONE => scr |> completeID "f"
      | SOME #"u" => openfu (inc scr)
      | SOME c => extend_openAlpha "f" c scr
and openfu scr =
    case currentChar scr of
        NONE => scr |> completeID "fu"
      | SOME #"n" => openfun (inc scr)
      | SOME c => extend_openAlpha "fu" c scr
and openfun scr =
    case currentChar scr of
        NONE => scr
      | SOME #"c" => openTermPFX "functor" 4 (inc scr)
      | SOME c => openOnKWord "fun" scr
and openi scr =
    case currentChar scr of
        NONE => scr |> completeID "i"
      | SOME #"n" => openin (inc scr)
      | SOME c => extend_openAlpha "i" c scr
and openin scr =
    case currentChar scr of
        NONE => Error(scr, "Don't expect to see 'in'-EOF")
      | SOME #"f" => scr |> inc |> openinf
      | SOME c => openOnKWord "in" scr
and openinf scr =
    case currentChar scr of
        NONE => scr |> completeID "inf"
      | SOME #"i" => scr |> inc |> openinfi
      | SOME c => extend_openAlpha "inf" c scr
and openinfi scr =
    case currentChar scr of
        NONE => scr |> completeID "infi"
      | SOME #"x" => scr |> inc |> openinfix
      | SOME c => extend_openAlpha "infi" c scr
and openinfix scr =
    case currentChar scr of
        NONE => Error(scr, "Don't expect to see 'infix'-EOF")
      | SOME #"l" => openOnKWord "infixl" (inc scr)
      | SOME #"r" => openOnKWord "infixr" (inc scr)
      | SOME c => openOnKWord "infix" scr
and opens scr =
    case currentChar scr of
        NONE => scr |> completeID "s"
      | SOME #"i" => openTermPFX "signature" 2 (inc scr)
      | SOME #"t" => openTermPFXsb "structure" 2 (inc scr)
      | SOME c => extend_openAlpha "s" c scr
and extend_openAlpha pfx c scr =
    if Char.isSpace c then clean_open (scr |> inc |> completeID pfx)
    else if isSMLAlphaCont c then
      modAlphaID true clean_open (pfx, [c]) (scr |> inc)
    else if isSMLSym c then
      modSymID true clean_open [c] (scr |> inc |> completeID pfx)
    else Error(scr, "Bad character >"^str c^"< after 'open'")
and openLPAREN scr =
    case currentChar scr of
        NONE => Error(scr, "Don't expect to see '('-EOF")
      | SOME #"*" => COMMENT clean_open (inc scr)
      | SOME c => Error(scr, "Don't expect to see '("^str c^"' after 'open'")
and openHASH scr =
    case currentChar scr of
        NONE => Error(scr, "Don't expect to see 'open'-'#'")
      | SOME c => if isSMLSym c then
                    modSymID true clean_open [c,#"#"] (scr |> inc)
                  else Error(scr, "Don't expect to see 'open'-'#'")
and openQID0 scr = (* seen the dot *)
    case currentChar scr of
        NONE => Error(scr, "'.'-EOF unexpected")
      | SOME c => if Char.isAlpha c then openQIDalpha (inc scr)
                  else if isSMLSym c then openQIDsym (inc scr)
                  else Error(scr, "'."^str c^" unexpected")
and openQIDalpha scr =
    case currentChar scr of
        NONE => scr
      | SOME #"." => openQID0 (inc scr)
      | SOME c => if isSMLAlphaCont c then openQIDalpha (inc scr)
                  else clean_open scr
and openQIDsym scr =
    case currentChar scr of
        NONE => scr
      | SOME #"." => openQID0 (inc scr)
      | SOME c => if isSMLSym c then openQIDsym (inc scr)
                  else clean_open scr
and modTermPFX dotok kword numseen (seenk, notk) scr = let
  fun get() = String.extract(kword, 0, SOME numseen)
in
  case currentChar scr of
      NONE => notk (scr |> completeID (get()))
    | SOME c => if c = String.sub(kword, numseen) then
                  if numseen + 1 = size kword then
                    OnKWord dotok kword (seenk,notk) (inc scr)
                  else
                    modTermPFX dotok kword (numseen + 1) (seenk,notk) (inc scr)
                else if isSMLAlphaCont c then
                  modAlphaID dotok notk (get(), [c]) (inc scr)
                else notk (scr |> completeID (get()))
end
and OnKWord dotok kword (seenk,notseenk) scr =
    case currentChar scr of
        NONE => seenk scr
      | SOME c => if isSMLAlphaCont c then
                    modAlphaID dotok notseenk (kword, [c]) (inc scr)
                  else seenk scr
and modAlphaID dotok k (base,cs) scr =
    case currentChar scr of
        NONE => scr |> completeID (base ^ implode (List.rev cs))
      | SOME #"." =>
          if dotok then
            openQID0 (scr |> inc |> completeID (base ^ implode (List.rev cs)))
          else Error(scr, "Didn't expect to see qualified ident here")
      | SOME c =>
          if isSMLAlphaCont c then modAlphaID dotok k (base,c::cs) (inc scr)
          else k (scr |> completeID (base ^ implode (List.rev cs)))
and modSymID dotok k cs scr =
    case currentChar scr of
        NONE => scr |> completeID (implode (List.rev cs))
      | SOME #"." =>
          if dotok then
            openQID0 (scr |> inc |> completeID (implode (List.rev cs)))
          else Error(scr, "Didn't expect to see qualified ident here")
      | SOME c => if isSMLSym c then modSymID dotok k (c::cs) (inc scr)
                  else k (scr |> completeID (implode (List.rev cs)))
and includeLPAR scr =
    case currentChar scr of
        NONE => Error(scr, "Don't expect 'include'-'('-EOF")
      | SOME #"*" => COMMENT clean_include (inc scr)
      | SOME c => Error(scr, "Don't expect 'include'-'('-'"^str c^"'")
and clean_include scr =
    case currentChar scr of
        NONE => scr
      | SOME #"d" =>
          modTermPFX false "datatype" 1 (clean_initial, clean_include) (inc scr)
      | SOME #"e" => includee (inc scr)
      | SOME #"s" =>
          modTermPFX false "structure" 1
                     (fn s => clean_initial (sbNote "structure" s),
                      clean_include)
                     (inc scr)
      | SOME #"t" =>
          modTermPFX false "type" 1 (clean_initial, clean_include) (inc scr)
      | SOME #"v" =>
          modTermPFX false "val" 1 (clean_initial, clean_include) (inc scr)
      | SOME #"w" =>
          modTermPFX false "where" 1 (clean_initial, clean_include) (inc scr)
      | SOME #"\n" => clean_include (newline scr)
      | SOME #"(" => includeLPAR (inc scr)
      | SOME #";" => clean_initial (inc scr)
      | SOME c => if Char.isSpace c then clean_include (inc scr)
                  else if Char.isAlpha c then
                    modAlphaID false clean_include ("", [c]) (inc scr)
                  else if isSMLSym c then
                    modSymID false clean_include [c] (inc scr)
                  else Error(scr, "Bad character >"^str c^"< after 'include'")
and includee scr =
    case currentChar scr of
        NONE => scr |> completeID "e"
      | SOME #"\n" => clean_include (scr |> newline |> completeID "e")
      | SOME #"n" =>
          modTermPFX false "end" 2
                     (fn s => clean_initial (sbNote "end" s), clean_include)
                     (inc scr)
      | SOME #"x" =>
          modTermPFX false "exception" 2 (clean_initial, clean_include) (inc scr)
      | SOME c => if Char.isSpace c then clean_include (scr |> inc |> completeID "e")
                  else if isSMLSym c then
                    modSymID false clean_include [c] (scr |> inc |> completeID "e")
                  else if isSMLAlphaCont c then
                    modAlphaID false clean_include ("e", [c]) (inc scr)
                  else Error(scr, "Bad character >"^str c^"< after 'include'")
and clean_initial scr =
    case currentChar scr of
        NONE => scr
      | SOME #"i" => initialAlphaKWordPFX "include" 1 clean_include (inc scr)
      | SOME #"o" => initialAlphaKWordPFX "open" 1 clean_open (inc scr)
      | SOME #"\n" => clean_initial (newline scr)
      | SOME #"(" => initialLPAREN (inc scr)
      | SOME #"\"" => STRING (inc scr)
      | SOME c =>
        if Char.isSpace c then clean_initial (inc scr)
        else if Char.isAlpha c then initialAlphaID("", [c]) (inc scr)
        else if isSMLSym c then initialSymID("", [c]) (inc scr)
        else clean_initial (inc scr)
and initialAlphaID (pfx, cs) scr = let
  fun idstr () = pfx ^ String.implode (List.rev cs)
in
  (* Every alphabetic identifier outside an `open' or `include' list
     arrives here, which is where `sbNote' gets to see the keywords it
     tracks.  The qualified branch is a reference rather than a
     keyword, so it is left alone. *)
  case currentChar scr of
      NONE => sbNote (idstr()) scr
    | SOME #"." => initialQID0 (scr |> inc |> completeID (idstr()))
    | SOME #"\n" => clean_initial (newline (sbNote (idstr()) scr))
    | SOME c => if isSMLAlphaCont c then initialAlphaID (pfx, c::cs) (inc scr)
                else clean_initial (sbNote (idstr()) scr)
end
and initialSymID (pfx, cs) scr =
    case currentChar scr of
        NONE => scr
      | SOME #"." => initialQID0 (scr |> inc |> completeID (pfx ^ String.implode (List.rev cs)))
      | SOME #"\n" => clean_initial (newline scr)
      | SOME c => if isSMLSym c then initialSymID (pfx, c::cs) (inc scr)
                  else clean_initial scr
and initialLPAREN scr =
    case currentChar scr of
        NONE => Error(scr, "'('-EOF unexpected")
      | SOME #"*" => COMMENT clean_initial (inc scr)
      | SOME #"(" => initialLPAREN (inc scr)
      | _ => clean_initial scr
and COMMENT k scr =
    case currentChar scr of
        NONE => Error(scr, "Unterminated comment")
      | SOME #"(" => COMMENTlpar k (inc scr)
      | SOME #"*" => COMMENTast k (inc scr)
      | SOME #"\n" => COMMENT k (newline scr)
      | _ => COMMENT k (inc scr)
and COMMENTlpar k scr =
    case currentChar scr of
        NONE => Error(scr, "Unterminated comment")
      | SOME #"(" => COMMENTlpar k (inc scr)
      | SOME #"*" => COMMENT (COMMENT k) (inc scr)
      | SOME #"\n" => COMMENT k (newline scr)
      | _ => COMMENT k (inc scr)
and COMMENTast k scr =
    case currentChar scr of
        NONE => Error(scr, "Unterminated comment")
      | SOME #"*" => COMMENTast k (inc scr)
      | SOME #")" => k (inc scr)
      | SOME #"\n" => COMMENT k (newline scr)
      | _ => COMMENT k (inc scr)
and initialQID0 scr = (* have just seen '.' *)
    case currentChar scr of
        NONE => Error(scr, "'.'-EOF unexpected")
      | SOME c => if Char.isSpace c then Error(scr, "'.'-whitespace unexpected")
                  else if Char.isAlpha c then
                    initialAlphaQID (inc scr)
                  else if isSMLSym c then
                    initialSymQID (inc scr)
                  else Error(scr, "Bad character >"^str c^"< after qualifying '.'")
and initialAlphaQID scr = (* have seen some characters of ID *)
    case currentChar scr of
        NONE => scr
      | SOME #"." => initialQID0 (inc scr)
      | SOME c => if isSMLAlphaCont c then initialAlphaQID (inc scr)
                  else clean_initial scr
and initialSymQID scr = (* have seen some characters of ID *)
    case currentChar scr of
        NONE => scr
      | SOME #"." => initialQID0 (inc scr)
      | SOME c => if isSMLSym c then initialSymQID (inc scr)
                  else clean_initial scr
and STRING scr = (* have seen the quote *)
    case currentChar scr of
        NONE => Error(scr, "Unterminated string literal")
      | SOME #"\"" => clean_initial (inc scr)
      | SOME #"\\" => STRINGslash (inc scr)
      | SOME #"\n" => Error(scr, "Unescaped newline in string literal")
      | _ => STRING (inc scr)
and STRINGcaret scr =
    case currentChar scr of
        NONE => Error(scr, "Unterminated string literal")
      | SOME c => let val i = Char.ord c
                  in
                    if i < 64 orelse i >= 96 then
                      Error(scr, "Illegal caret-escape in string literal")
                    else STRING (inc scr)
                  end
and STRINGslash scr =
    case currentChar scr of
        NONE => Error(scr, "Unterminated string literal")
      | SOME #"\n" => STRINGelidews (newline scr)
      | SOME #"\\" => STRING (inc scr)
      | SOME #"\"" => STRING (inc scr)
      | SOME #"^" => STRINGcaret (inc scr)
      | SOME #"a" => STRING (inc scr)
      | SOME #"b" => STRING (inc scr)
      | SOME #"f" => STRING (inc scr)
      | SOME #"n" => STRING (inc scr)
      | SOME #"r" => STRING (inc scr)
      | SOME #"t" => STRING (inc scr)
      | SOME #"v" => STRING (inc scr)
      | SOME c => if Char.isDigit c then
                    STRINGslashdigit 1 (inc scr)
                  else if Char.isSpace c then
                    STRINGelidews (inc scr)
                  else Error(scr, "Illegal backslash escape >" ^ str c ^
                                  "< in string literal")
and STRINGelidews scr =
    case currentChar scr of
        NONE => Error(scr, "Unterminated string literal")
      | SOME #"\\" => STRING (inc scr)
      | SOME #"\n" => STRINGelidews (newline scr)
      | SOME c => if Char.isSpace c then STRINGelidews (inc scr)
                  else Error(scr, "Illegal char >" ^ str c ^
                                  "< in string \\...\\ elision")
and STRINGslashdigit cnt scr =
    case currentChar scr of
        NONE => Error(scr, "Unterminated string literal")
      | SOME c => if Char.isDigit c then
                    if cnt = 2 then STRING (inc scr)
                    else STRINGslashdigit (cnt + 1) (inc scr)
                  else Error(scr, "Illegal backslash escape in string literal")
and initialAlphaKWordPFX kword numseen k scr =
    case currentChar scr of
        NONE => scr
      | SOME c =>
        if c = String.sub(kword, numseen) then
          if numseen + 1 = size kword then
            initialAlphaKWord kword k (inc scr)
          else
            initialAlphaKWordPFX kword (numseen + 1) k (inc scr)
        else if isSMLAlphaCont c then
          initialAlphaID (String.extract(kword, 0, SOME numseen), [c])
                         (inc scr)
        else clean_initial scr
and initialAlphaKWord kword k scr =
    case currentChar scr of
        NONE => k (sbNote kword scr)
      | SOME c => if isSMLAlphaCont c then
                    initialAlphaID (kword, [c]) (inc scr)
                  else k (sbNote kword scr)

(* Drop the modules the file defines for itself.  A script that writes

     structure bossLib = struct val Datatype = Datatype.Datatype end

   so that a `[bare]' theory can use the `Datatype:' block does not
   depend on the real `bossLib', and loading it on the strength of
   that mention is not merely wasteful: `bossLib' brings `listTheory'
   with it, and a theory already loaded in the session is sealed
   against the `new_theory' that `listScript.sml' is about to perform.

   Dropping every self-bound name would be wrong, because the binder
   is not in scope in its own right-hand side:

     structure Parse = struct open Parse ... end

   opens the *outer* `Parse', which is a real dependency, and the idiom
   appears in some ninety files here.  So a name survives if it is
   mentioned anywhere up to the end of its own declaration, and is
   dropped only when every mention of it comes afterwards, where the
   file's own structure is what the name means.

   A binding whose end was never found -- `structure M = N' at the end
   of a file, or anything the depth counting could not follow -- has no
   entry in `ends' and keeps its dependency. *)
fun dropSelfBound (SCR{ids, sb, ...}) = let
  val ends = #ends sb and first = #first sb
  fun keep nm =
      case Binarymap.peek (ends, nm) of
          NONE => true
        | SOME e => (case Binarymap.peek (first, nm) of
                         NONE => true
                       | SOME p => p < e)
in
  Binarymap.foldl (fn (nm, ln, acc) =>
                      if keep nm then Binarymap.insert (acc, nm, ln) else acc)
                  (Binarymap.mkDict String.compare)
                  ids
end

fun scrdeps scr =
    dropSelfBound (clean_initial scr) before
    closeSCR scr

fun file_deps fname = scrdeps (makeSCR fname)
fun stream_deps p = scrdeps (SCRfromStream p)
fun reader_deps p = scrdeps (SCRfromReader p)

end (* struct *)
