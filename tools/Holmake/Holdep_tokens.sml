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
                       currentID : string list option,
                       ids : string Binaryset.set,
                       cr : char_reader}
fun makeSCR fname = let
  val cr = fromFile fname
in
  SCR {linenum = 1, colnum = 0, filename = fname,
       currentID = NONE, ids = Binaryset.empty String.compare,
       cr = cr}
end

fun SCRfromStream (name, is) = let
  val cr = fromStream is
in
  SCR {linenum = 1, colnum = 0, filename = name,
       currentID = NONE, ids = Binaryset.empty String.compare,
       cr = cr}
end

fun currentChar (SCR{cr,...}) = current cr
fun closeSCR (SCR{cr,...}) = closeCR cr
fun getIDs (SCR{ids,...}) = ids
fun inc (SCR {linenum, filename, colnum, currentID, ids, cr}) =
    SCR{linenum = linenum, filename = filename, colnum = colnum + 1,
        currentID = currentID, ids = ids, cr = advance cr}
fun newline (SCR{linenum, filename, colnum, currentID, ids, cr}) =
    SCR{linenum = linenum + 1, filename = filename, colnum = 0,
        currentID = NONE, ids = ids, cr = advance cr}
fun newID s (SCR{linenum, filename, colnum, currentID, ids, cr}) =
    SCR{linenum = linenum, filename = filename, colnum = colnum,
        currentID = SOME [s], ids = ids, cr = cr}
fun extendID c (SCR{linenum, filename, colnum, currentID, ids, cr}) =
    case currentID of
        SOME strs =>
          SCR{linenum = linenum, filename = filename, colnum = colnum,
              currentID = SOME (str c :: strs), ids = ids, cr = cr}
      | NONE =>
          raise Fail "Invariant failure: extendID with no ID current"
fun completeID s (SCR{linenum, filename, colnum, currentID, ids, cr}) =
    SCR{linenum = linenum, filename = filename, colnum = colnum,
        currentID = NONE, ids = Binaryset.add(ids, s), cr = cr}
fun finishID (SCR{linenum, filename, colnum, currentID, ids, cr}) =
    case currentID of
        NONE => raise Fail "Invariant failure: finishID with no ID current"
      | SOME strs =>
        let
          val s = String.concat (List.rev strs)
        in
          SCR{linenum = linenum, filename = filename, colnum = colnum,
              currentID = NONE, ids = Binaryset.add(ids, s), cr = cr}
        end

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
      | SOME #"d" => openTerminatorPFX "datatype" 1 (inc scr) (* datatype *)
      | SOME #"e" => opene (inc scr) (* exception, end *)
      | SOME #"f" => openTerminatorPFX "fun" 1 (inc scr)
      | SOME #"i" => openi (inc scr) (* in, infixl, infix, infixr *)
      | SOME #"l" => openTerminatorPFX "local" 1 (inc scr)
      | SOME #"n" => openTerminatorPFX "nonfix" 1 (inc scr)
      | SOME #"o" => openAlphaKWordPFX "open" 1 clean_open (inc scr)
      | SOME #"p" => openTerminatorPFX "prim_val" 1 (inc scr)
      | SOME #"s" => opens (inc scr) (* structure, signature *)
      | SOME #"t" => openTerminatorPFX "type" 1 (inc scr)
      | SOME #"v" => openTerminatorPFX "val" 1 (inc scr)
      | SOME #";" => clean_initial (inc scr)
      | SOME #"(" => openLPAREN (inc scr)
      | SOME #"#" => openHASH (inc scr)
      | SOME #"\n" => clean_open (newline scr)
      | SOME c => if Char.isSpace c then clean_open (inc scr)
                  else if Char.isAlpha c then
                    openAlphaID (scr |> inc |> newID (str c))
                  else if isSMLSym c then
                    openSymID (scr |> inc |> newID (str c))
                  else Error(scr, "Bad character >"^str c^"< after open")
and openTerminatorPFX kword cnt scr =
    openAlphaKWordPFX kword cnt clean_initial scr
and openOnTerminator kword scr =
    openOnKWord kword clean_initial scr
and opene scr =
    case currentChar scr of
        NONE => scr |> completeID "e"
      | SOME #"n" => openTerminatorPFX "end" 2 (inc scr)
      | SOME #"x" => openTerminatorPFX "exception" 2 (inc scr)
      | SOME c => extend_openAlpha "e" c scr
and openi scr =
    case currentChar scr of
        NONE => scr |> completeID "i"
      | SOME #"n" => openin (inc scr)
      | SOME c => extend_openAlpha "i" c scr
and openin scr =
    case currentChar scr of
        NONE => Error(scr, "Don't expect to see 'in'-EOF")
      | SOME #"f" => scr |> inc |> openinf
      | SOME c => openOnTerminator "in" scr
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
      | SOME #"l" => openOnTerminator "infixl" (inc scr)
      | SOME #"r" => openOnTerminator "infixr" (inc scr)
      | SOME c => openOnTerminator "infix" scr
and opens scr =
    case currentChar scr of
        NONE => scr |> completeID "s"
      | SOME #"i" => openTerminatorPFX "signature" 2 (inc scr)
      | SOME #"t" => openTerminatorPFX "structure" 2 (inc scr)
      | SOME c => extend_openAlpha "s" c scr
and openLPAREN scr =
    case currentChar scr of
        NONE => Error(scr, "Don't expect to see '('-EOF")
      | SOME #"*" => COMMENT clean_open (inc scr)
      | SOME c => Error(scr, "Don't expect to see '("^str c^"' after 'open'")
and openHASH scr =
    case currentChar scr of
        NONE => Error(scr, "Don't expect to see 'open'-'#'")
      | SOME c => if isSMLSym c then
                    openSymID (scr |> inc |> newID ("#" ^ str c))
                  else Error(scr, "Don't expect to see 'open'-'#'")
and openAlphaID scr =
    case currentChar scr of
        NONE => scr |> finishID
      | SOME #"." => openQID0 (scr |> inc |> finishID)
      | SOME c => if isSMLAlphaCont c then
                    openAlphaID (scr |> inc |> extendID c)
                  else
                    clean_open (scr |> finishID)
and openSymID scr =
    case currentChar scr of
        NONE => scr |> finishID
      | SOME #"." => openQID0 (scr |> inc |> finishID)
      | SOME c => if isSMLSym c then openSymID (scr |> inc |> extendID c)
                  else clean_open (scr |> finishID)
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
and openAlphaKWordPFX kword numseen k scr = let
  fun get() = String.extract(kword, 0, SOME numseen)
in
  case currentChar scr of
      NONE => scr |> completeID (get())
    | SOME c => if c = String.sub(kword, numseen) then
                  if numseen + 1 = size kword then
                    openOnKWord kword k (inc scr)
                  else openAlphaKWordPFX kword (numseen + 1) k (inc scr)
                else if isSMLAlphaCont c then
                  extend_openAlpha (get()) c scr
                else clean_open (scr |> completeID (get()))
end
and openOnKWord kword k scr =
    case currentChar scr of
        NONE => k scr
      | SOME c => if isSMLAlphaCont c then
                    extend_openAlpha kword c scr
                  else k scr
and extend_openAlpha pfx c scr =
    if Char.isSpace c then clean_open (scr |> inc |> completeID pfx)
    else if isSMLAlphaCont c then
      openAlphaID (scr |> inc |> newID (pfx ^ str c))
    else if isSMLSym c then
      openSymID (scr |> inc |> completeID pfx |> newID (str c))
    else Error(scr, "Bad character >"^str c^"< after 'open'")
and extend_openKeyword kword c scr =
    if Char.isSpace c then Error(scr, "Don't expect to see '"^kword^"' after 'open'")
    else if Char.isAlpha c then
      openAlphaID (scr |> inc |> newID (kword ^ str c))
    else if isSMLSym c then
      Error(scr, "Don't expect to see '"^kword^"' after 'open'")
    else Error(scr, "Bad character >"^str c^"< after 'open'")
and extend_openTerminator kword c scr =
    if c = #"\n" then clean_initial (scr |> newline)
    else if Char.isSpace c then clean_initial (scr |> inc)
    else if Char.isAlpha c then
      openAlphaID (scr |> inc |> newID (kword ^ str c))
    else clean_initial (scr |> inc)
and includeALPHA cs scr =
    case currentChar scr of
        NONE => scr |> completeID (implode (List.rev cs))
      | SOME c => if isSMLAlphaCont c then includeALPHA (c::cs) (inc scr)
                  else clean_initial (scr |> completeID (implode (List.rev cs)))
and includeSYM cs scr =
    case currentChar scr of
        NONE => scr |> completeID (implode (List.rev cs))
      | SOME c => if isSMLSym c then includeSYM (c::cs) (inc scr)
                  else clean_initial (scr |> completeID (implode (List.rev cs)))
and includeLPAR scr =
    case currentChar scr of
        NONE => Error(scr, "Don't expect 'include'-'('-EOF")
      | SOME #"*" => COMMENT clean_include (inc scr)
      | SOME c => Error(scr, "Don't expect 'include'-'('-'"^str c^"'")
and clean_include scr =
    case currentChar scr of
        NONE => Error(scr, "Don't expect to see 'include'-EOF")
      | SOME #"\n" => clean_include (newline scr)
      | SOME #"(" => includeLPAR (inc scr)
      | SOME c => if Char.isSpace c then clean_include (inc scr)
                  else if Char.isAlpha c then includeALPHA [c] (inc scr)
                  else if isSMLSym c then includeSYM [c] (inc scr)
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
