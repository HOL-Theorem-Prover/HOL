   /* hol-quote-filter.lex */

   /* Filter to provide quotation and antiquotation for the HOL system. */
   /* Written by R.J.Boulton, 13th November 1995.                       */
   /* Modified on 9th July 1997 by RJB to fix bug spotted by M. Norrish.*/
   /* Modified on 22 February 1999 by Michael Norrish to allow for use
       as batch file executable where input and output arguments
       (necessarily files) are specified on the command-line.  This
       will allow its use in contexts where it is not straightforward
       to modify a process's standard in and out.  (In Unix, this is
       easily achieved with file redirections and pipes, but we want
       to reduce dependence on Unix-isms). */

   /* Expects the following Standard ML datatype to have been declared: */
   /*                                                                   */
   /*    datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a;          */
   /*                                                                   */
   /* and also the functions Term, Type, and ty_antiq.    */

   /* This filter adds the following special features to Standard ML:   */
   /*                                                                   */
   /*    `...`        a generic quotation                               */
   /*    ``...``      a HOL term quotation                              */
   /*    ``:...``     a HOL type quotation                              */
   /*    --`...`--    a HOL term quotation (for backward compatibility) */
   /*    ==`:...`==   a HOL type quotation (for backward compatibility) */
   /*                                                                   */
   /*    `... ^(...) ...`      antiquotation in a generic quotation     */
   /*    ``... ^(...) ...``    term antiquotation in a HOL term         */
   /*    ``... :^(...) ...``   type antiquotation in a HOL term         */
   /*    ``:... ^(...) ...``   type antiquotation in a HOL type         */
   /*                                                                   */
   /* where (...) may be an alphanumeric or symbolic ML identifier or a */
   /* parenthesized expression. The number of lines in the processed    */
   /* text remains unchanged.                                           */
   /*                                                                   */
   /* Limitations:                                                      */
   /*                                                                   */
   /*    o No carriage return or line feed may appear between the `--'  */
   /*      or `==' and the quotation marks in the old-style quotations. */

%{
#include <stdlib.h>
#include <stdio.h>
unsigned antiquote = 0;
int anti(void);
%}

%option noyywrap

%s STRING COMMENT QUOTE TMQUOTE OLDTMQUOTE TYQUOTE OLDTYQUOTE ANTIQUOTE

letter [A-Za-z]
digit  [0-9]
symbol [!%&$+/:<=>?@~|#*]|\\|\-|\^
id     {letter}({letter}|{digit}|_|')*|{symbol}+
ws     [ \t]

%%

%{
int pardepth = 0;
int comdepth = 0;
int prevstate = INITIAL;
%}

<INITIAL>\"       { ECHO; BEGIN STRING; }
<INITIAL>"(*"     { ECHO; ++comdepth; BEGIN COMMENT; }
<INITIAL>"("      { ECHO; ++pardepth; }
<INITIAL>")"      { ECHO; --pardepth;
                    if (antiquote && pardepth < 1) return 0; }
<INITIAL>=={ws}*` { fprintf(yyout, "(Type [QUOTE \"");
                    BEGIN OLDTYQUOTE; }
<INITIAL>--{ws}*` { fprintf(yyout,
                    "(Term [QUOTE \""); BEGIN OLDTMQUOTE; }
<INITIAL>``{ws}*:/[A-Za-z[:space:]] {
                    fprintf(yyout, "(Type [QUOTE \":"); BEGIN TYQUOTE; }
<INITIAL>``       { fprintf(yyout, "(Term [QUOTE \""); BEGIN TMQUOTE; }
<INITIAL>`        { fprintf(yyout, "[QUOTE \""); BEGIN QUOTE; }
<INITIAL>\n       { ECHO; fflush(stdout); fflush(stdout); }

<STRING>\\\\      { ECHO; }
<STRING>\\\"      { ECHO; }
<STRING>\"        { ECHO; BEGIN INITIAL; }

<COMMENT>"(*"     { ECHO; ++comdepth; }
<COMMENT>"*)"     { ECHO; --comdepth; if (comdepth < 1) BEGIN INITIAL; }

<QUOTE>`          { fprintf(yyout, "\"]"); BEGIN INITIAL; }
<QUOTE>\^         { fprintf(yyout, "\",ANTIQUOTE (");
                    prevstate = QUOTE; BEGIN ANTIQUOTE; }
<QUOTE>\\         { fprintf(yyout, "\\\\"); }
<QUOTE>\"         { fprintf(yyout, "\\\""); }
<QUOTE>\t         { fprintf(yyout, "\\t"); }
<QUOTE>\n         { fprintf(yyout, " \",\nQUOTE \""); }

<TMQUOTE>``       { fprintf(yyout, "\"])"); BEGIN INITIAL; }
<TMQUOTE>\^       { fprintf(yyout, "\",ANTIQUOTE (");
                    prevstate = TMQUOTE; BEGIN ANTIQUOTE; }
<TMQUOTE>\\       { fprintf(yyout, "\\\\"); }
<TMQUOTE>\"       { fprintf(yyout, "\\\""); }
<TMQUOTE>\t       { fprintf(yyout, "\\t"); }
<TMQUOTE>\n       { fprintf(yyout, " \",\nQUOTE \""); }

<OLDTMQUOTE>`{ws}*-- { fprintf(yyout, "\"])"); BEGIN INITIAL; }
<OLDTMQUOTE>\^       { fprintf(yyout, "\",ANTIQUOTE (");
                       prevstate = OLDTMQUOTE; BEGIN ANTIQUOTE; }
<OLDTMQUOTE>\\       { fprintf(yyout, "\\\\"); }
<OLDTMQUOTE>\"       { fprintf(yyout, "\\\""); }
<OLDTMQUOTE>\t       { fprintf(yyout, "\\t"); }
<OLDTMQUOTE>\n       { fprintf(yyout, " \",\nQUOTE \""); }

<TYQUOTE>``       { fprintf(yyout, "\"])"); BEGIN INITIAL; }
<TYQUOTE>\^       { fprintf(yyout, "\",ANTIQUOTE (");
                    prevstate = TYQUOTE; BEGIN ANTIQUOTE; }
<TYQUOTE>\\       { fprintf(yyout, "\\\\"); }
<TYQUOTE>\"       { fprintf(yyout, "\\\""); }
<TYQUOTE>\t       { fprintf(yyout, "\\t"); }
<TYQUOTE>\n       { fprintf(yyout, " \",\nQUOTE \""); }

<OLDTYQUOTE>`{ws}*== { fprintf(yyout, "\"])"); BEGIN INITIAL; }
<OLDTYQUOTE>\^       { fprintf(yyout, "\",ANTIQUOTE (");
                       prevstate = OLDTYQUOTE; BEGIN ANTIQUOTE; }
<OLDTYQUOTE>\\       { fprintf(yyout, "\\\\"); }
<OLDTYQUOTE>\"       { fprintf(yyout, "\\\""); }
<OLDTYQUOTE>\t       { fprintf(yyout, "\\t"); }
<OLDTYQUOTE>\n       { fprintf(yyout, " \",\nQUOTE \""); }

<ANTIQUOTE>{id}   { ECHO; fprintf(yyout, "),QUOTE \""); BEGIN prevstate; }
<ANTIQUOTE>"("    { yyless(0); BEGIN INITIAL; anti();
                    fprintf(yyout, "),QUOTE \""); BEGIN prevstate; }
<ANTIQUOTE>{ws}+  { }
<ANTIQUOTE>\n     { ECHO; }
<ANTIQUOTE>.      { yyless(0); fprintf(yyout, "),QUOTE \""); BEGIN prevstate; }

%%

#include <signal.h>

int anti(void)
{ int x;
  unsigned old = antiquote;
  antiquote = 1;
  x = yylex();
  antiquote = old;
  return x;
}

int main(int argc, char *argv[])
{
  if (argc != 1 && argc != 3) {
    fprintf(stderr, "Invalid arguments to %s\n", argv[0]);
    exit(EXIT_FAILURE);
  }

  if (argc == 3) {
    if (!(yyin = fopen(argv[1], "r"))) {
      perror(argv[1]);
      exit(EXIT_FAILURE);
    }
    if (!(yyout = fopen(argv[2], "w"))) {
      perror(argv[2]);
      exit(EXIT_FAILURE);
    }
  }

  signal(SIGINT,SIG_IGN); /* Ignores Ctl-C; when HOL is interrupted,
                             the filter continues unaffected. */
  return yylex();
}
