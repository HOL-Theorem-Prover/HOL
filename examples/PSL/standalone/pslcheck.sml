
(******************************************************************************
* Command line tool
* 
*  pslcheck [-all] -sere '<SERE>' -path '<PATH>'
*  pslcheck [-all] -fl   '<FL>'   -path '<PATH>'
* 
* The optional "-all" argument specifies that all intervals are
* checked in the case of a SERE and all path tails in the case of a
* formula.
* 
* Without the "-all" arguments, the commands: 
* 
*  pslcheck -sere '<SERE>' -path '<PATH>' 
*  pslcheck -fl   '<FL>'   -path '<PATH>' 
* 
* report "true" or "false" (or a parser or processing error).
* 
* The command: 
* 
*  pslcheck -sere '<SERE>' -path '<PATH>' -all
* 
* reports "true on intervals [m1:n1][m2:n2] ..." 
* (or a parser or processing error).
*
* The command: 
* 
*  pslcheck -fl   '<FL>'   -path '<PATH>' -all
* 
* reports "true at times t1,t2, ..."
* (or a parser or processing error).
*
* Arguments have to be in the order shown here.
******************************************************************************)

open HolKernel Parse boolLib bossLib;
open ParserTools;

val _ = Process.system ("echo " ^ process_args(CommandLine.arguments()));

(*
pslcheck      -sere '{{a;b}@clk1;c}@clk2' -path '{clk2}{clk1,a}{a}{clk1,b,clk2}{c}{clk1}{c,clk2}{clk1}'
pslcheck -all -sere '{{a;b}@clk1;c}@clk2' -path '{clk2}{clk1,a}{a}{clk1,b,clk2}{c}{clk1}{c,clk2}{clk1}'

pslcheck      -fl '(a until! b)@clk' -path '{}{clk}{}{clk,a}{a}{clk,a,b}{}{clk,b}{b}{clk}'
pslcheck -all -fl '(a until! b)@clk' -path '{}{clk}{}{clk,a}{a}{clk,a,b}{}{clk,b}{b}{clk}'
*)
