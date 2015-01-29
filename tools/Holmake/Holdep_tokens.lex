(* though strictly an mllex file, -*- sml -*- mode works OK *)
type lexstate = {
  commentdepth : int ref,
  commentstart : SourcePos.t ref,
  in_string : bool ref,
  stringstart : SourcePos.t ref,
  source : SourceFile.t
}
fun new_state fname = {commentdepth = ref 0,
                       commentstart = ref SourcePos.bogus,
                       stringstart = ref SourcePos.bogus,
                       in_string = ref false,
                       source = SourceFile.new fname}

fun inputLine strm =
    case TextIO.inputLine strm of
        SOME s => s
      | NONE => ""

type lexresult = string option
exception LEX_ERROR of string
fun regionError (r, s) = Region.toString r ^ ": " ^ s
fun lexErrorP(source, yypos, s) =
    let
      val p = SourceFile.getPos(source, yypos)
      val r = Region.make {left = p, right = p}
    in
      raise LEX_ERROR(regionError(r, s))
    end
fun lexErrorR(region, s) = raise LEX_ERROR(regionError(region,s))

fun eof ({commentdepth,source,commentstart,in_string,stringstart,...} : lexstate) =
    let
      fun mkr st = Region.make{left = st, right = SourceFile.lineStart source}
    in
      if !commentdepth <> 0 then
        lexErrorR(mkr (!commentstart), "Unclosed comment")
      else if !in_string then
        lexErrorR(mkr (!stringstart), "Unterminated string")
      else NONE
    end

fun getQual s =
  let
    fun parse n =
        if String.sub(s, n) = #"." then
            String.extract(s, 0, SOME n)
        else
            parse (n+1)
  in
    parse 0
  end;

%%
id = [A-Za-z][A-Za-z0-9_']* | [-!%&$#+/:<=>?@~^|*`\\]+;
ws = [\ \013\t];
newline = "\n" | "\013\n";
openterminator = "val" | "fun" | "in" | "infix[lr]?" | "local" | "type" | "datatype" | "nonfix" | "exception" | "end" | "structure" | "signature";
%s OPEN STRING COMMENT INCLUDE STRINGCONT;
%arg ({source, commentdepth, commentstart, in_string, stringstart, ...}:UserDeclarations.lexstate);
%structure Holdep_tokens
%%
<INITIAL,OPEN,INCLUDE>{ws} => (continue());
<INITIAL,OPEN,COMMENT,INCLUDE>{newline} =>
  (SourceFile.newline(source,yypos+size yytext); continue());
<INITIAL>"(*" => (
  YYBEGIN COMMENT;
  commentstart := SourceFile.getPos(source, yypos);
  commentdepth := 1;
  continue());
<INITIAL>"*)" => (
  lexErrorP(source, yypos, "Unmatched comment bracket")
);
<INITIAL>'[A-Za-z0-9_']+ => (continue());
<INITIAL>~?[0-9]+(\.[0-9]+)?(E~?[0-9]+)? => (continue());
<INITIAL>\" | #\" => (
  YYBEGIN STRING;
  stringstart := SourceFile.getPos(source, yypos);
  in_string := true;
  continue());
<INITIAL>[_,{}[();] | ] | "..." => (continue());
<INITIAL>({id}\.)+{id} => (SOME (getQual yytext));
<INITIAL>"open" => (YYBEGIN OPEN; continue());
<INITIAL>"include" => (YYBEGIN INCLUDE; continue());
<INITIAL>{id} => (continue());

<COMMENT>"(*" => (commentdepth := !commentdepth + 1; continue());
<COMMENT>"*)" => (commentdepth := !commentdepth - 1;
                  YYBEGIN (if !commentdepth = 0 then INITIAL else COMMENT);
                  continue());
<COMMENT>. => (continue());

<OPEN>{openterminator} => (YYBEGIN INITIAL; continue());
<OPEN>"open" => (continue());
<OPEN>{id} => (SOME yytext);

<STRING>"\\\"" => (continue());
<STRING>"\\" {newline} => (SourceFile.newline(source,yypos+size yytext);
                           YYBEGIN STRINGCONT;
                           continue());
<STRING>"\\" {ws} => (YYBEGIN STRINGCONT; continue());
<STRING>"\\" . => (continue());
<STRING>\" => (YYBEGIN INITIAL; in_string := false; continue());
<STRING>. => (continue());
<STRING>{newline} => (lexErrorP(source, yypos, "String terminated by newline"));

<STRINGCONT>{ws} => (continue());
<STRINGCONT>{newline} => (SourceFile.newline(source,yypos+size yytext); continue());
<STRINGCONT>"\\" => (YYBEGIN STRING; continue());
<STRINGCONT> . => (lexErrorP(source, yypos, "Invalid character in \\ ... \\"));
