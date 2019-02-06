structure TheoryDat_Reader :> TheoryDat_Reader =
struct

datatype token = datatype TheoryDatTokens_dtype.t
fun toString t =
    case t of
        ID s => s
      | QString s => "\"" ^ String.toString s ^ "\""
      | Num n => Arbnum.toString n
      | LBr => "["
      | RBr => "]"
      | Comma => ","
      | EOF => "<EOF>"



fun tokstream reader =
    let
      val st = TheoryDatTokens.UserDeclarations.newstate ()
    in
      TheoryDatTokens.makeLexer reader st
    end

type buffer = {lexer: unit -> TheoryDatTokens_dtype.t,
               istrm : TextIO.instream,
               current : TheoryDatTokens_dtype.t ref}

fun current (b : buffer) = !(#current b)
fun eof (b:buffer) = current b = EOF
fun checkForEOF b = if eof b then TextIO.closeIn (#istrm b) else ()
fun advance (b as {current,lexer,...} : buffer) =
    if eof b then () else (current := lexer(); checkForEOF b)

fun datBuffer {filename} =
    let
      val istrm = TextIO.openIn filename
      val lex = tokstream (fn i => TextIO.inputN (istrm,i))
    in
      {lexer = lex, istrm = istrm, current = ref (lex())}
    end

end
