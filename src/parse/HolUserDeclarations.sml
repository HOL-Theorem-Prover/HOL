structure HolUserDeclarations =
struct

type pos = int;
val line:pos = 0;
type svalue = HolTokens.svalue;
type ('a,'b) token = ('a,'b) HolTokens.token;
type lexresult = (svalue,pos) HolTokens.token;
type arg = Term.term list ref;
fun eof (_:arg) = HolTokens.EOF(line,line); 

fun error(s,_,_) = 
  Portable.output(Portable.std_out,"HOL lexer error: "^s^"\n");

val type_paren_count = ref 0;
val comment_paren_count = ref 0;
val string_list = ref ([]:string list);
exception AQ_ERR of string;
exception LEX_ERR of string;

val ordof = Portable_String.ordof;
fun ord s = ordof(s,0);
val inc = Portable_Ref.inc;
val dec = Portable_Ref.dec;

local val tilde = ord "~"
      val comma = ord ","
      val semicolon = ord ";"
in
fun has_tilde s =
   let fun f i = let val oof = ordof(s,i)
                 in (oof = tilde) orelse (oof = comma) orelse 
                    (oof=semicolon) orelse f(i+1) end
   in f 0 handle _ => false end
end;

local val dollar = ord "$"
in
fun drop_dollar s =
   if (ordof(s,0) = dollar) 
   then String.substring(s,1,String.size s - 1)  
   else s
end;

local val squote = "\""
in
fun build_string (l as [h1,h2]) = 
       if (h1=squote) andalso (h2=squote)
       then "emptystring"
       else Portable.implode l
  | build_string l = Portable.implode l
end;
 
local val dquote = ord"\""
      fun is_string_literal s =
          Portable_Int.> (String.size s, 1)
           andalso (ordof(s,0) = dquote)
           andalso (ordof(s, String.size s - 1) = dquote)
in
fun string_aq tm = 
  let val s = #Name(Term.dest_const tm)
      val _ = Lib.assert is_string_literal s
  in Portable_String.substring(s,1,String.size s-2)
  end
end;


end;
