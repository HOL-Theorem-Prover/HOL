(*****************************************************************************)
(* Parsing the PSL/Sugar semantics                                           *)
(*****************************************************************************)

(*
structure ParserTools :> ParserTools =
struct
*)

(******************************************************************************
* Load theories
* (commented out for compilation)
******************************************************************************)
(*
quietdec := true;
loadPath := "../official-semantics"   ::
            "../executable-semantics" ::
            "../regexp"               ::
            "../parser.mosmlyacc"     ::
            !loadPath;
map load
 ["numLib", "intLib", "stringLib",
  "Data", "Main", "regexpLib", "ExecuteTools"];
open intLib numLib stringLib Data Main regexpLib;
val _ = intLib.deprecate_int();
quietdec := false;
*)

(******************************************************************************
* Boilerplate needed for compilation
******************************************************************************)
open HolKernel Parse boolLib bossLib;


(******************************************************************************
* Open theories
******************************************************************************)
open intLib numLib stringLib Data Main regexpLib ExecuteTools;

(******************************************************************************
* Set default parsing to natural numbers rather than integers
******************************************************************************)
val _ = intLib.deprecate_int();

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

(******************************************************************************
* Set the trace level of the regular expression library:
* 0: silent
* 1: 1 character (either - or +) for each list element processed
* 2: matches as they are discovered
* 3: transitions as they are calculated
* 4: internal state of the automata
******************************************************************************)
val _ = set_trace "regexpTools" 1;

(******************************************************************************
* Translate ML datatype bexp to HOL terms
******************************************************************************)
fun bexpToTerm(B_PROP a) =
     if a="T" then ``B_TRUE:string bexp`` else ``B_PROP ^(fromMLstring a)``
 |  bexpToTerm(B_NOT b) =
     ``B_NOT ^(bexpToTerm b)``
 |  bexpToTerm(B_AND(b1,b2)) =
     ``B_AND(^(bexpToTerm b1), ^(bexpToTerm b2))``
 |  bexpToTerm(B_OR(b1,b2)) =
     ``B_OR(^(bexpToTerm b1), ^(bexpToTerm b2))``
 |  bexpToTerm(B_IMP(b1,b2)) =
     ``B_IMP(^(bexpToTerm b1), ^(bexpToTerm b2))``
 |  bexpToTerm(B_IFF(b1,b2)) =
     ``B_IFF(^(bexpToTerm b1), ^(bexpToTerm b2))``
 |  bexpToTerm B_TRUE =
     ``B_TRUE``
 |  bexpToTerm B_FALSE       =
     ``B_FALSE``;

(******************************************************************************
* Translate ML datatype range to HOL terms
******************************************************************************)
fun rangeToTerm(m, NONE)   =
     ``(^(term_of_int m), NONE)``
 |  rangeToTerm(m, SOME n) =
     ``(^(term_of_int m), SOME ^(term_of_int n))``;

(******************************************************************************
* Translate ML datatype sere to HOL terms
******************************************************************************)
fun sereToTerm(S_BOOL b) =
     ``S_BOOL ^(bexpToTerm b)``
 |  sereToTerm(S_CAT(r1,r2)) =
     ``S_CAT(^(sereToTerm r1), ^(sereToTerm r2))``
 |  sereToTerm(S_FUSION(r1,r2)) =
     ``S_FUSION(^(sereToTerm r1), ^(sereToTerm r2))``
 |  sereToTerm(S_OR(r1,r2)) =
     ``S_OR(^(sereToTerm r1), ^(sereToTerm r2))``
 |  sereToTerm(S_AND(r1,r2)) =
     ``S_AND(^(sereToTerm r1), ^(sereToTerm r2))``
 |  sereToTerm(S_REPEAT r) =
     ``S_REPEAT ^(sereToTerm r)``
 |  sereToTerm(S_CLOCK(r,b)) =
     ``S_CLOCK(^(sereToTerm r), ^(bexpToTerm b))``
 |  sereToTerm(S_FLEX_AND(r1,r2)) =
     ``S_FLEX_AND(^(sereToTerm r1), ^(sereToTerm r2))``
 |  sereToTerm(S_RANGE_REPEAT(r,rng)) =
     ``S_RANGE_REPEAT(^(sereToTerm r), ^(rangeToTerm rng))``
 |  sereToTerm(S_NON_ZERO_REPEAT r) =
     ``S_NON_ZERO_REPEAT ^(sereToTerm r)``
 |  sereToTerm(S_RANGE_EQ_REPEAT(b, rng)) =
     ``S_RANGE_EQ_REPEAT(^(bexpToTerm b), ^(rangeToTerm rng))``
 |  sereToTerm(S_RANGE_GOTO_REPEAT(b,rng)) =
     ``S_RANGE_GOTO_REPEAT(^(bexpToTerm b), ^(rangeToTerm rng))``
;

(******************************************************************************
* Translate ML datatype fl to HOL terms
******************************************************************************)
fun flToTerm(F_BOOL b) =
     ``F_BOOL ^(bexpToTerm b)``
 |  flToTerm(F_NOT f) =
     ``F_NOT ^(flToTerm f)``
 |  flToTerm(F_AND(f1,f2)) =
     ``F_AND(^(flToTerm f1), ^(flToTerm f2))``
 |  flToTerm(F_STRONG_X f) =
     ``F_STRONG_X ^(flToTerm f)``
 |  flToTerm(F_U(f1,f2)) =
     ``F_U(^(flToTerm f1), ^(flToTerm f2))``
 |  flToTerm(F_SUFFIX_IMP(r,f)) =
     ``F_SUFFIX_IMP(^(sereToTerm r), ^(flToTerm f))``
 |  flToTerm(F_STRONG_IMP(r1,r2)) =
     ``F_STRONG_IMP(^(sereToTerm r1), ^(sereToTerm r2))``
 |  flToTerm(F_WEAK_IMP(r1,r2)) =
     ``F_WEAK_IMP(^(sereToTerm r1), ^(sereToTerm r2))``
 |  flToTerm(F_ABORT(f,b)) =
     ``F_ABORT(^(flToTerm f), ^(bexpToTerm b))``
 |  flToTerm(F_STRONG_CLOCK(f,b)) =
     ``F_STRONG_CLOCK(^(flToTerm f), ^(bexpToTerm b))``
 |  flToTerm(F_WEAK_CLOCK(f,b)) =
     ``F_WEAK_CLOCK(^(flToTerm f), ^(bexpToTerm b))``
 |  flToTerm(F_OR(f1,f2)) =
     ``F_OR(^(flToTerm f1), ^(flToTerm f2))``
 |  flToTerm(F_IMP(f1,f2)) =
     ``F_IMP(^(flToTerm f1), ^(flToTerm f2))``
 |  flToTerm(F_IFF(f1,f2)) =
     ``F_IFF(^(flToTerm f1), ^(flToTerm f2))``
 |  flToTerm(F_WEAK_X f) =
     ``F_WEAK_X ^(flToTerm f)``
 |  flToTerm(F_F f) =
     ``F_F ^(flToTerm f)``
 |  flToTerm(F_G f) =
     ``F_G ^(flToTerm f)``
 |  flToTerm(F_W(f1,f2)) =
     ``F_W(^(flToTerm f1), ^(flToTerm f2))``
 |  flToTerm(F_ALWAYS f) =
     ``F_ALWAYS ^(flToTerm f)``
 |  flToTerm(F_NEVER f) =
     ``F_NEVER ^(flToTerm f)``
 |  flToTerm(F_WEAK_NEXT f) =
     ``F_WEAK_NEXT ^(flToTerm f)``
 |  flToTerm(F_STRONG_NEXT f) =
     ``F_STRONG_NEXT ^(flToTerm f)``
 |  flToTerm(F_STRONG_EVENTUALLY f) =
     ``F_STRONG_EVENTUALLY ^(flToTerm f)``
 |  flToTerm(F_STRONG_UNTIL(f1,f2)) =
     ``F_STRONG_UNTIL(^(flToTerm f1), ^(flToTerm f2))``
 |  flToTerm(F_WEAK_UNTIL(f1,f2)) =
     ``F_WEAK_UNTIL(^(flToTerm f1), ^(flToTerm f2))``
 |  flToTerm(F_STRONG_UNTIL_INC(f1,f2)) =
     ``F_STRONG_UNTIL_INC(^(flToTerm f1), ^(flToTerm f2))``
 |  flToTerm(F_WEAK_UNTIL_INC(f1,f2)) =
     ``F_WEAK_UNTIL_INC(^(flToTerm f1), ^(flToTerm f2))``
 |  flToTerm(F_STRONG_BEFORE(f1,f2)) =
     ``F_STRONG_BEFORE(^(flToTerm f1), ^(flToTerm f2))``
 |  flToTerm(F_WEAK_BEFORE(f1,f2)) =
     ``F_WEAK_BEFORE(^(flToTerm f1), ^(flToTerm f2))``
 |  flToTerm(F_STRONG_BEFORE_INC(f1,f2)) =
     ``F_STRONG_BEFORE_INC(^(flToTerm f1), ^(flToTerm f2))``
 |  flToTerm(F_WEAK_BEFORE_INC(f1,f2)) =
     ``F_WEAK_BEFORE_INC(^(flToTerm f1), ^(flToTerm f2))``
 |  flToTerm(F_NUM_WEAK_X(n,f)) =
     ``F_NUM_WEAK_X(^(term_of_int n), ^(flToTerm f))``
 |  flToTerm(F_NUM_STRONG_X(n,f)) =
     ``F_NUM_STRONG_X(^(term_of_int n), ^(flToTerm f))``
 |  flToTerm(F_NUM_WEAK_NEXT(n,f)) =
     ``F_NUM_WEAK_NEXT(^(term_of_int n), ^(flToTerm f))``
 |  flToTerm(F_NUM_STRONG_NEXT(n,f)) =
     ``F_NUM_STRONG_NEXT(^(term_of_int n), ^(flToTerm f))``
 |  flToTerm(F_NUM_WEAK_NEXT_A(rng,f)) =
     ``F_NUM_WEAK_NEXT_A(^(rangeToTerm rng), ^(flToTerm f))``
 |  flToTerm(F_NUM_STRONG_NEXT_A(rng,f)) =
     ``F_NUM_STRONG_NEXT_A(^(rangeToTerm rng), ^(flToTerm f))``
 |  flToTerm(F_NUM_WEAK_NEXT_E(rng,f)) =
     ``F_NUM_WEAK_NEXT_E(^(rangeToTerm rng), ^(flToTerm f))``
 |  flToTerm(F_NUM_STRONG_NEXT_E(rng,f)) =
     ``F_NUM_STRONG_NEXT_E(^(rangeToTerm rng), ^(flToTerm f))``
 |  flToTerm(F_STRONG_NEXT_EVENT(b,f)) =
     ``F_STRONG_NEXT_EVENT(^(bexpToTerm b), ^(flToTerm f))``
 |  flToTerm(F_WEAK_NEXT_EVENT(b,f)) =
     ``F_WEAK_NEXT_EVENT(^(bexpToTerm b), ^(flToTerm f))``
 |  flToTerm(F_NUM_STRONG_NEXT_EVENT(b,n,f)) =
     ``F_NUM_STRONG_NEXT_EVENT(^(bexpToTerm b), ^(term_of_int n), ^(flToTerm f))``
 |  flToTerm(F_NUM_WEAK_NEXT_EVENT(b,n,f)) =
     ``F_NUM_WEAK_NEXT_EVENT(^(bexpToTerm b), ^(term_of_int n), ^(flToTerm f))``
 |  flToTerm(F_NUM_STRONG_NEXT_EVENT_A(b,rng,f)) =
     ``F_NUM_STRONG_NEXT_EVENT_A(^(bexpToTerm b), ^(rangeToTerm rng), ^(flToTerm f))``
 |  flToTerm(F_NUM_WEAK_NEXT_EVENT_A(b,rng,f)) =
     ``F_NUM_WEAK_NEXT_EVENT_A(^(bexpToTerm b), ^(rangeToTerm rng), ^(flToTerm f))``
 |  flToTerm(F_NUM_STRONG_NEXT_EVENT_E(b,rng,f)) =
     ``F_NUM_STRONG_NEXT_EVENT_E(^(bexpToTerm b), ^(rangeToTerm rng), ^(flToTerm f))``
 |  flToTerm(F_NUM_WEAK_NEXT_EVENT_E(b,rng,f)) =
     ``F_NUM_WEAK_NEXT_EVENT_E(^(bexpToTerm b), ^(rangeToTerm rng), ^(flToTerm f))``
 |  flToTerm(F_SKIP_STRONG_IMP(r1,r2)) =
     ``F_SKIP_STRONG_IMP(^(sereToTerm r1), ^(sereToTerm r2))``
 |  flToTerm(F_SKIP_WEAK_IMP(r1,r2)) =
     ``F_SKIP_WEAK_IMP(^(sereToTerm r1), ^(sereToTerm r2))``
 |  flToTerm(F_SERE_ALWAYS r) =
     ``F_SERE_ALWAYS ^(sereToTerm r)``
 |  flToTerm(F_SERE_NEVER r) =
     ``F_SERE_NEVER ^(sereToTerm r)``
 |  flToTerm(F_SERE_STRONG_EVENTUALLY r) =
     ``F_SERE_STRONG_EVENTUALLY ^(sereToTerm r)``
 |  flToTerm(F_STRONG_WITHIN(r1,b,r2)) =
     ``F_STRONG_WITHIN(^(sereToTerm r1), ^(bexpToTerm b), ^(sereToTerm r2))``
 |  flToTerm(F_WEAK_WITHIN(r1,b,r2)) =
     ``F_WEAK_WITHIN(^(sereToTerm r1), ^(bexpToTerm b), ^(sereToTerm r2))``
 |  flToTerm(F_STRONG_WITHIN_INC(r1,b,r2)) =
     ``F_STRONG_WITHIN_INC(^(sereToTerm r1), ^(bexpToTerm b), ^(sereToTerm r2))``
 |  flToTerm(F_WEAK_WITHIN_INC(r1,b,r2)) =
     ``F_WEAK_WITHIN_INC(^(sereToTerm r1), ^(bexpToTerm b), ^(sereToTerm r2))``
 |  flToTerm(F_STRONG_WHILENOT(b,r)) =
     ``F_STRONG_WHILENOT(^(bexpToTerm b), ^(sereToTerm r))``
 |  flToTerm(F_WEAK_WHILENOT(b,r)) =
     ``F_WEAK_WHILENOT(^(bexpToTerm b), ^(sereToTerm r))``
 |  flToTerm(F_STRONG_WHILENOT_INC(b,r)) =
     ``F_STRONG_WHILENOT_INC(^(bexpToTerm b), ^(sereToTerm r))``
 |  flToTerm(F_WEAK_WHILENOT_INC(b,r)) =
     ``F_WEAK_WHILENOT_INC(^(bexpToTerm b), ^(sereToTerm r)))``
;

(******************************************************************************
* Translate ML datatype obe to HOL terms
******************************************************************************)
fun obeToTerm(O_BOOL b)     = ``O_BOOL ^(bexpToTerm b)``
 |  obeToTerm(O_NOT f)      = ``O_NOT ^(obeToTerm f)``
 |  obeToTerm(O_AND(f1,f2)) = ``O_AND(^(obeToTerm f1), ^(obeToTerm f2))``
 |  obeToTerm(O_EX f)       = ``O_EX ^(obeToTerm f)``
 |  obeToTerm(O_EU(f1,f2))  = ``O_EU(^(obeToTerm f1), ^(obeToTerm f2))``
 |  obeToTerm(O_EG f)       = ``O_EG ^(obeToTerm f)``
;

(******************************************************************************
* Parse PSL constructs from a string and report error locations
******************************************************************************)
val Boolean  = bexpToTerm o parseFileBexp     o stringToFile
and SERE     = sereToTerm o parseFileSere     o stringToFile
and FL       = flToTerm   o parseFileFl       o stringToFile
and OBE      = obeToTerm  o parseFileObe      o stringToFile;

(******************************************************************************
* Convert a list of strings to a term representing a state
******************************************************************************)
fun stateToTerm [] = ``{}:string->bool``
 |  stateToTerm (a :: s) = ``^(fromMLstring a) INSERT ^(stateToTerm s)``;

(******************************************************************************
* Convert a list of lists of strings to a term representing a path
******************************************************************************)
fun pathToTerm p = listSyntax.mk_list(map stateToTerm p, ``:string -> bool``);

(******************************************************************************
* Create a term representing the value of a SERE wrt a path
******************************************************************************)
fun pathsereToTerm(p,r) = ``S_SEM ^(pathToTerm p) B_TRUE ^(sereToTerm r)``;

(******************************************************************************
* Create a term representing the value of an FL formula wrt a path
******************************************************************************)
fun pathflToTerm(p,f) = ``F_SEM (FINITE ^(pathToTerm p)) B_TRUE ^(flToTerm f)``;

(******************************************************************************
* State "a,b,c" =
*  ``{"a"; "b"; "c"}``
*
* Path "{}{a,b}{c,d,e}" =
*  ``[{}; {"a"; "b"}; {"c"; "d"; "e"}]``
*
* PathSERE "{x}{y} |= x;y" =
*  ``S_SEM [{"x"}; {"y"}] B_TRUE
*     (S_CAT (S_BOOL (B_PROP "x"),S_BOOL (B_PROP "y")))``
*
* PathFL "{x}{y,p}{q} |= {x;y} |-> {p;q}" =
*  ``F_SEM (FINITE [{"x"}; {"y"; "p"}; {"q"}]) B_TRUE
*     (F_WEAK_IMP
*        (S_CAT (S_BOOL (B_PROP "x"),S_BOOL (B_PROP "y")),
*         S_CAT (S_BOOL (B_PROP "p"),S_BOOL (B_PROP "q"))))``
******************************************************************************)
val State    = stateToTerm    o parseFileState    o stringToFile
and Path     = pathToTerm     o parseFilePath     o stringToFile
and PathSERE = pathsereToTerm o parseFilePathSere o stringToFile
and PathFL   = pathflToTerm   o parseFilePathFl   o stringToFile;

(******************************************************************************
* EVAL a SERE or FL formula wrt a path
******************************************************************************)
val EvalSERE = EVAL o PathSERE
and EvalFL   = EVAL o PathFL;


(* Examples
loadPath := "../official-semantics"   ::
            "../executable-semantics" ::
            "../regexp"               ::
            "../parser.mosmlyacc"     ::
            !loadPath;
load "ParserTools";
open ParserTools;

EvalSERE "{x}{y} |= x;y";
EvalSERE "{p}{q} |= p;q";
EvalSERE "{x}{y}{p} |= x;T;p";
EvalSERE "{x}{y}{p}{q} |= T[*];p;T[*]";

EvalFL "{x}{y,p}{q} |= {x;y} |-> {p;q}";
EvalFL "{x}{y,p}{q} |= {x;y} |=> {p;q}";
EvalFL "{x}{y}{p}{q} |= {x;y} |-> {p;q}";
EvalFL "{x}{y}{p}{q} |= {x;y} |=> {p;q}";
EvalFL "{x}{y}{p}{q} |= {x;y;p} |-> {p;q}";
EvalFL "{x}{y}{p}{q} |= {x;y;T} |-> {p;q}";
*)

(******************************************************************************
* EVAL an FL formula on all tails of a path and report positions
* where it is true
******************************************************************************)

fun EvalAllFL(p,f) =
 let val ll = parsePath p
     val fm = parseFl f
     val nl = List.tabulate(length ll + 1,I)
 in
 mapfilter
  (fn n => if rhs(concl(EVAL(pathflToTerm(List.drop(ll,n),fm)))) = ``F``
            then fail()
            else n)
   nl
 end;

(*

EvalAllFL
 ("{}{clk}{}{clk,a}{a}{clk,a,b}{}{clk,b}{b}{clk}", "a until! b");

EvalAllFL
 ("{}{clk}{}{clk,a}{a}{clk,a,b}{}{clk,b}{b}{clk}", "(a until! b)@clk");

*)


(******************************************************************************
* map_interval p [x0,...,xn] = [((i,j), p[xi,...,xj]) | 0 <= i <= j <= n]
******************************************************************************)
fun map_interval p l =
 flatten
  (mapfilter
   (fn i =>
     mapfilter
      (fn j => if i<=j then ((i,j),p(List.take(List.drop(l,i),j-i+1)))
                       else fail())
      (List.tabulate(length l,I)))
   (List.tabulate(length l,I)));

(******************************************************************************
* EVAL a SERE on all sub-intervals of a path and report those where it holds
******************************************************************************)

fun EvalAllSERE(p,r) =
 let val ll = parsePath p
     val se = parseSere r
 in
 mapfilter
  (fn (interval,result) => if result = ``F`` then fail() else interval)
  (map_interval (fn w => rhs(concl(EVAL(pathsereToTerm(w,se))))) ll)
 end;


(*


(******************************************************************************
* Example 2 (LRM Version 1.0, page 33)
*
* time  0  1  2  3  4  5  6  7
* ----------------------------
* clk1  0  1  0  1  0  1  0  1
* a     0  1  1  0  0  0  0  0
* b     0  0  0  1  0  0  0  0
* c     0  0  0  0  1  0  1  0
* clk2  1  0  0  1  0  0  1  0
*
* {clk2}{clk1,a}{a}{clk1,b,clk2}{c}{clk1}{c,clk2}{clk1}
******************************************************************************)

EvalAllSERE
 ("{clk2}{clk1,a}{a}{clk1,b,clk2}{c}{clk1}{c,clk2}{clk1}",
  "{{a;b}@clk1;c}@clk2");

*)

(******************************************************************************
* ML function to support processing of arguments of command line invocation:
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
*  pslcheck -all -sere '<SERE>' -path '<PATH>'
*
* reports "true on intervals [m1:n1][m2:n2] ..."
* (or a parser or processing error).
*
* The command:
*
*  pslcheck -all -fl   '<FL>'   -path '<PATH>'
*
* reports "true at times t1,t2, ..."
* (or a parser or processing error).
*
* Arguments have to be in the order shown here.
******************************************************************************)

fun intervalsToString [] = ""
 |  intervalsToString ((m,n)::il) =
     ("[" ^ Int.toString m ^ ":" ^ Int.toString n ^ "]" ^ intervalsToString il);

fun timesToString []      = ""
 |  timesToString [m]     = Int.toString m
 |  timesToString (m::il) = (Int.toString m ^ "," ^ timesToString il);

fun process_args ["-all","-sere",r,"-path",p] =
     ("true on intervals " ^ intervalsToString(EvalAllSERE(p,r)))
 |  process_args ["-all","-fl",f,"-path",p] =
     ("true at times " ^ timesToString(EvalAllFL(p,f)))
 |  process_args ["-sere",r,"-path",p] =
     if rhs(concl(EVAL(pathsereToTerm(parsePath p, parseSere r)))) = T
      then "true"
      else "false"
 |  process_args ["-fl",f,"-path",p] =
     if rhs(concl(EVAL(pathflToTerm(parsePath p, parseFl f)))) = T
      then "true"
      else "false"
 |  process_args _ = "bad arguments to pslcheck";

(*
process_args ["-all", "-sere", "{{a;b}@clk1;c}@clk2",
                      "-path", "{clk2}{clk1,a}{a}{clk1,b,clk2}{c}{clk1}{c,clk2}{clk1}"];

process_args [        "-sere", "{{a;b}@clk1;c}@clk2",
                      "-path", "{clk2}{clk1,a}{a}{clk1,b,clk2}{c}{clk1}{c,clk2}{clk1}"];

process_args ["-all", "-fl",   "(a until! b)@clk",
                      "-path", "{}{clk}{}{clk,a}{a}{clk,a,b}{}{clk,b}{b}{clk}"];

process_args [        "-fl",   "(a until! b)@clk",
                      "-path", "{}{clk}{}{clk,a}{a}{clk,a,b}{}{clk,b}{b}{clk}"];

*)

