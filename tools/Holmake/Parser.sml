local
in
datatype token =
    ID of string
  | EQUALS
  | NULL
  | OPEN
  | QUAL_ID of string
  | STAR
  | EOF
end;

open Obj Parsing;
prim_val vector_ : int -> 'a -> 'a Vector.vector = 2 "make_vect";
prim_val update_ : 'a Vector.vector -> int -> 'a -> unit = 3 "set_vect_item";

open List

fun print s = BasicIO.print;
fun printb s = print (s ^ " ");
(* Line 10, file Parser.sml *)
val yytransl = #[
  257 (* ID *),
  258 (* EQUALS *),
  259 (* NULL *),
  260 (* OPEN *),
  261 (* QUAL_ID *),
  262 (* STAR *),
  263 (* EOF *),
    0];

val yylhs = "\255\255\
\\001\000\001\000\002\000\002\000\002\000\003\000\003\000\004\000\
\\004\000\006\000\006\000\007\000\007\000\005\000\005\000\000\000";

val yylen = "\002\000\
\\002\000\001\000\001\000\001\000\002\000\002\000\001\000\002\000\
\\000\000\001\000\001\000\001\000\001\000\001\000\001\000\002\000";

val yydefred = "\000\000\
\\000\000\000\000\012\000\003\000\000\000\015\000\013\000\002\000\
\\016\000\000\000\000\000\004\000\014\000\011\000\005\000\000\000\
\\010\000\006\000\001\000\008\000";

val yydgoto = "\002\000\
\\009\000\010\000\011\000\015\000\012\000\016\000\013\000";

val yysindex = "\001\000\
\\000\255\000\000\000\000\000\000\015\255\000\000\000\000\000\000\
\\000\000\009\255\001\255\000\000\000\000\000\000\000\000\015\255\
\\000\000\000\000\000\000\000\000";

val yyrindex = "\000\000\
\\000\000\000\000\000\000\000\000\019\255\000\000\000\000\000\000\
\\000\000\002\255\000\000\000\000\000\000\000\000\000\000\019\255\
\\000\000\000\000\000\000\000\000";

val yygindex = "\000\000\
\\000\000\000\000\008\000\003\000\000\000\000\000\251\255";

val YYTABLESIZE = 26;
val yytable = "\017\000\
\\003\000\001\000\004\000\005\000\006\000\007\000\008\000\019\000\
\\007\000\003\000\017\000\004\000\005\000\006\000\007\000\003\000\
\\014\000\018\000\020\000\000\000\007\000\009\000\009\000\009\000\
\\000\000\009\000";

val yycheck = "\005\000\
\\001\001\001\000\003\001\004\001\005\001\006\001\007\001\007\001\
\\007\001\001\001\016\000\003\001\004\001\005\001\006\001\001\001\
\\002\001\010\000\016\000\255\255\006\001\003\001\004\001\005\001\
\\255\255\007\001";

val yyact = vector_ 17 (fn () => ((raise Fail "parser") : obj));
(* Rule 1, file Parser.grm, line 17 *)
val _ = update_ yyact 1
(fn () => repr(let
val d__1__ = peekVal 1 : string list
in
( (d__1__) ) end : string list))
;
(* Rule 2, file Parser.grm, line 18 *)
val _ = update_ yyact 2
(fn () => repr(let
in
( [] ) end : string list))
;
(* Rule 3, file Parser.grm, line 22 *)
val _ = update_ yyact 3
(fn () => repr(let
in
( [] ) end : string list))
;
(* Rule 4, file Parser.grm, line 23 *)
val _ = update_ yyact 4
(fn () => repr(let
val d__1__ = peekVal 0 : string list
in
( (d__1__) ) end : string list))
;
(* Rule 5, file Parser.grm, line 24 *)
val _ = update_ yyact 5
(fn () => repr(let
val d__2__ = peekVal 0 : string list
in
( (d__2__) ) end : string list))
;
(* Rule 6, file Parser.grm, line 28 *)
val _ = update_ yyact 6
(fn () => repr(let
val d__1__ = peekVal 1 : string list
val d__2__ = peekVal 0 : string list
in
( (d__1__) @ (d__2__) ) end : string list))
;
(* Rule 7, file Parser.grm, line 29 *)
val _ = update_ yyact 7
(fn () => repr(let
val d__1__ = peekVal 0 : string list
in
( (d__1__) ) end : string list))
;
(* Rule 8, file Parser.grm, line 33 *)
val _ = update_ yyact 8
(fn () => repr(let
val d__1__ = peekVal 1 : string
val d__2__ = peekVal 0 : string list
in
( (d__1__) :: (d__2__) ) end : string list))
;
(* Rule 9, file Parser.grm, line 34 *)
val _ = update_ yyact 9
(fn () => repr(let
in
( [] ) end : string list))
;
(* Rule 10, file Parser.grm, line 38 *)
val _ = update_ yyact 10
(fn () => repr(let
val d__1__ = peekVal 0 : string
in
( (d__1__) ) end : string))
;
(* Rule 11, file Parser.grm, line 39 *)
val _ = update_ yyact 11
(fn () => repr(let
in
( "=" ) end : string))
;
(* Rule 12, file Parser.grm, line 43 *)
val _ = update_ yyact 12
(fn () => repr(let
val d__1__ = peekVal 0 : string
in
( (d__1__) ) end : string))
;
(* Rule 13, file Parser.grm, line 44 *)
val _ = update_ yyact 13
(fn () => repr(let
in
( "*" ) end : string))
;
(* Rule 14, file Parser.grm, line 48 *)
val _ = update_ yyact 14
(fn () => repr(let
val d__1__ = peekVal 0 : string
in
( [] ) end : string list))
;
(* Rule 15, file Parser.grm, line 49 *)
val _ = update_ yyact 15
(fn () => repr(let
val d__1__ = peekVal 0 : string
in
( [(d__1__)] ) end : string list))
;
(* Entry MLtext *)
val _ = update_ yyact 16 (fn () => raise yyexit (peekVal 0));
val yytables : parseTables =
  ( yyact,
    yytransl,
    yylhs,
    yylen,
    yydefred,
    yydgoto,
    yysindex,
    yyrindex,
    yygindex,
    YYTABLESIZE,
    yytable,
    yycheck );
fun MLtext lexer lexbuf = yyparse yytables 1 lexer lexbuf;
