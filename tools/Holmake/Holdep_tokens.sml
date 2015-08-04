structure Holdep_tokens :> Holdep_tokens =
struct

infix |>
fun x |> f = f x

exception LEX_ERROR of string

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
  val is = TextIO.openIn f
in
  make (fn () => TextIO.input is) (fn () => TextIO.closeIn is)
end
fun fromStream is = make (fn () => TextIO.input is) (fn () => ())
fun closeCR (CR {closer,...}) = closer()

fun advance (c as CR {pos, buffer, maxpos, reader, current, closer}) =
    if pos < maxpos then
      CR { pos = pos + 1, buffer = buffer, reader = reader,
           current = SOME(String.sub(buffer, pos + 1)),
           maxpos = maxpos, closer = closer }
    else if buffer = "" then c
    else make reader closer

datatype SCR = SCR of {linenum : int,
                       filename : string,
                       colnum : int,
                       ids : string Binaryset.set,
                       cr : char_reader}
fun makeSCR fname = let
  val cr = fromFile fname
in
  SCR {linenum = 1, colnum = 0, filename = fname,
       ids = Binaryset.empty String.compare, cr = cr}
end

fun SCRfromStream (name, is) = let
  val cr = fromStream is
in
  SCR {linenum = 1, colnum = 0, filename = name,
       ids = Binaryset.empty String.compare, cr = cr}
end

fun currentChar (SCR{cr,...}) = current cr
fun closeSCR (SCR{cr,...}) = closeCR cr
fun getIDs (SCR{ids,...}) = ids
fun inc (SCR {linenum, filename, colnum, ids, cr}) =
    SCR{linenum = linenum, filename = filename, colnum = colnum + 1,
        ids = ids, cr = advance cr}
fun newline (SCR{linenum, filename, colnum, ids, cr}) =
    SCR{linenum = linenum + 1, filename = filename, colnum = 0,
        ids = ids, cr = advance cr}
fun completeID s (SCR{linenum, filename, colnum, ids, cr}) =
    SCR{linenum = linenum, filename = filename, colnum = colnum,
        ids = Binaryset.add(ids, s), cr = cr}

fun mem x [] = false
  | mem x (y::ys) = x = y orelse mem x ys
val SMLsyms = String.explode "!%&$+/:<=>?@~|#*\\-~^"
val symbools = List.tabulate(256, fn i => mem (Char.chr i) SMLsyms)
val symb_vec = Vector.fromList symbools
fun isSMLSym c = Vector.sub(symb_vec, Char.ord c)

fun isSMLAlphaCont c =
    Char.isAlphaNum c orelse c = #"_" orelse c = #"'"

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
      | SOME #"l" => openTermPFX "local" 1 (inc scr)
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
and openOnKWord kstr scr = OnKWord true kstr (clean_initial, clean_open) scr
and opene scr =
    case currentChar scr of
        NONE => scr |> completeID "e"
      | SOME #"n" => openTermPFX "end" 2 (inc scr)
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
      | SOME #"t" => openTermPFX "structure" 2 (inc scr)
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
          modTermPFX false "structure" 1 (clean_initial, clean_include) (inc scr)
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
          modTermPFX false "end" 2 (clean_initial, clean_include) (inc scr)
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
and initialAlphaID (pfx, cs) scr =
    case currentChar scr of
        NONE => scr
      | SOME #"." =>
          initialQID0 (scr |> inc
                           |> completeID (pfx ^ String.implode (List.rev cs)))
      | SOME #"\n" => clean_initial (newline scr)
      | SOME c => if isSMLAlphaCont c then initialAlphaID (pfx, c::cs) (inc scr)
                  else clean_initial scr
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
        NONE => k scr
      | SOME c => if isSMLAlphaCont c then
                    initialAlphaID (kword, [c]) (inc scr)
                  else k scr

fun scrdeps scr =
    getIDs (clean_initial scr) before
    closeSCR scr

fun file_deps fname = scrdeps (makeSCR fname)
fun stream_deps p = scrdeps (SCRfromStream p)

end (* struct *)
