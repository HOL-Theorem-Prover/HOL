(*****************************************************************************)
(*  HolSatLib.sml                                                            *)
(*                                                                           *)
(*  MJCG: Tue May 29                                                         *)
(*****************************************************************************)

structure HolSatLib :> HolSatLib = struct

(* 
** Use Binaryset to encode mapping between HOL variable names
** and DIMACS format variable numbers as a set of string*int pairs.
*)

(*
load "Binaryset";
load "FileSys";
load "TextIO";
load "Process";
load "Char";
load "String";
load "Substring";
load "tautLib";
load "Conv";
*)

open SatSolvers;

local
open Lib;
open boolLib;
open Globals;
open Parse;
open Term;
open Type;
open Thm;
open Drule;
open Psyntax;
open Conv;
in

infix |->;

(* 
** Compare values of type string*int by first comparing second components
** and if they are equal comparing first components
** (this should never actually be necessary as set is encoding a 1-1 map)
*)

fun pcompare((s1:string,n1),(s2:string,n2)) = 
 case Int.compare(n1,n2) of
   LESS    => LESS
 | GREATER => GREATER 
 | EQUAL   => String.compare(s1,s2);

(*
** Mapping from HOL variable names to DIMACS format variable numbers
** is stored in a global assignable (i.e. reference) variable sat_var_map.
** The type of sat_var_map is (int * (string * int) set) ref and
** ther integer first component is the next available number
** (i.e. it is one plus the number of elements in the set)
*)

(* 
** Initialise sat_var_map to integer 1 paired with the empty set
** (in DIMACS format variable numbering starts from 1 because 0
** is the clause separator)
*)

val sat_var_map = ref(1, Binaryset.empty pcompare); 

(*
** Reinitialise sat_var_map.
** Needs to be done for each translation of a term to DIMACS format
** as numbers must be an initial segment of 1,2,3,...
** (otherwise crasp, zchaff etc may crash)
*)

fun initSatVarMap() = (sat_var_map := (1, Binaryset.empty pcompare));

(* 
** Lookup the number corresponding to a string, possibly extending sat_var_map 
*)

fun lookup_sat_var s =
 let val (c,svm) = !sat_var_map
 in
 case Binaryset.find (fn p => fst p = s) svm of
   SOME(_,n) => n
 | NONE      => let val svm' = Binaryset.add(svm,(s,c))
                    val _    = (sat_var_map := (c+1,svm'))
                in
                 c
                end
 end;

(* 
** Lookup the string corresponding to a number 
*)

exception lookup_sat_numError;
fun lookup_sat_num n =
 case Binaryset.find (fn p => snd p = n) (snd(!sat_var_map)) of
   SOME(s,_) => s
 | NONE      =>  raise lookup_sat_numError;

(* 
** Show sat_var_map as a list of its elements
*)

fun showSatVarMap() = 
 let val (c,st) = !sat_var_map
 in
  (c, Binaryset.listItems st)
 end;

(* 
** Print a term showing types 
*)

val print_all_term = with_flag(show_types,true)print_term;

(* 
** Convert a literal to a (bool * integer) pair, where
** the boolean is true iff the literal is negated, 
** if necessary extend sat_var_map 
*)

exception literalToIntError;
fun literalToInt t =
 let val (sign,v) =
      if is_var t andalso type_of t = bool then (false, fst(dest_var t)) else
      if is_neg t 
       then 
        let val t1 = dest_neg t
        in if is_var t1 andalso type_of t1 = bool 
            then (true,fst(dest_var t1))
            else (print "``"; print_all_term t; print "``";
                  print " is not a literal"; raise literalToIntError)
        end 
       else (print "``"; print_all_term t; print "``\n";
             print " is not a clause or literal\n"; raise literalToIntError)
     val v_num = lookup_sat_var v
 in
  (sign, v_num)
 end;

(* 
** Convert an integer to a literal, 
** raising lookup_sat_numError if the absolute value of
** the integer isn't in sat_var_map
*)

fun intToLiteral n =
 let val s = lookup_sat_num(abs n) 
     val v = mk_var(s,bool)
 in
  if n >= 0 then v else mk_neg v
 end;

(*
** termToDimacs t
** checks t is CNF of the form
**  ``(v11 \/ ... \/ v1p) /\ (v21 \/ ... \/ v2q) /\ ... /\ (vr1 \/ ... \/vrt)``
** where vij is a literal, i.e. a boolean variable or a negated
** boolean variable.
** If t is such a CNF then termToDimacs t returns a list of lists of integers
** [[n11,...,n1p],[n21,...,n2q], ... , [nr1,...,nrt]]
** If vij is a boolean variable ``v`` then nij is the entry 
** for v in sat_var_map. If vij is ``~v``, then nij is the negation
** of the entry for v in sat_var_map
** N.B. Definition of termToDimacs processes last clause first, 
**      so variables are not numbered in the left-to-right order.
**      Not clear if this matters.
*)

fun termToDimacs t = 
 foldr
  (fn (c,d) =>  (map literalToInt (strip_disj c)) :: d) 
  [] 
  (strip_conj t);

(* Test data
val t1 = ``x:bool``;
val t2 = ``~x``;
val t3 = ``x \/ y \/ ~z \/ w``;
val t4 = ``(x \/ y \/ ~z \/ w) /\ (~w \/ ~x \/ y)``;
val t5 = ``(x \/ y \/ ~z \/ w) /\ !x. (~w \/ ~x \/ y)``;
val t6 = ``(x \/ y \/ ~z \/ w) /\ (~w)``;
val t7 = ``(x \/ y \/ ~z \/ w) /\ (~w) /\ (w \/ x) /\ (p /\ q /\ r)``;
*)

(*
** reference containing prefix used to make variables from numbers
** when reading DIMACS format
*)

val prefix = ref "v";

(*
** intToPrefixedLiteral n = ``(!prefix)n``
** intToPrefixedLiteral (~n) = ``~(!prefix)n``
*)

fun intToPrefixedLiteral n =
 if n >= 0 
  then mk_var(((!prefix) ^ Int.toString n), Type.bool)
  else mk_neg(mk_var(((!prefix) ^ Int.toString(Int.abs n)), Type.bool));

(*
** buildClause [n1,...,np] builds
** ``(!prefix)np /\ ... /\ (!prefix)n1``
** Raises exception Empty on the empty list
*)

fun buildClause l =
 foldl 
  (fn (n,t) => mk_disj(intToPrefixedLiteral n, t)) 
  (intToPrefixedLiteral (hd l))
  (tl l);

(*
** dimacsToTerm l
** converts a list of integers
** [n11,...,n1p,0,n21,...,n2q,0, ... , 0,nr1,...,nrt,0]
** into a term in CNF of the form
**  ``(v11 \/ ... \/ v1p) /\ (v21 \/ ... \/ v2q) /\ ... /\ (vr1 \/ ... \/vrt)``
** where vij is a literal, i.e. a boolean variable or a negated boolena variable.
** If nij is non-negative then vij is ``(!prefix)nij``;
** If nij is negative ~mij then vij is ``~(!prefix)mij``;
*)

local (* dimacsToTerm_aux splits off one clause, dimacsToTerm iterates it *)
fun dimacsToTerm_aux []     acc = (buildClause acc,[])
 |  dimacsToTerm_aux (0::l) acc = (buildClause acc,l)
 |  dimacsToTerm_aux (x::l) acc = dimacsToTerm_aux l (x::acc)
in
fun dimacsToTerm l =
 let val (t,l1) = dimacsToTerm_aux l []
 in
  if null l1 then t else mk_conj(t, dimacsToTerm l1)
 end
end;

(*
** Convert (true,n) to "-n" and (false,n) to "n"
*)

fun LiteralToString(b,n) = if b then ("-" ^ (Int.toString n)) else Int.toString n;

(*
** termToDimacsFile t
** converts t to DIMACS format and then writes out a 
** file into the temporary directory.
** the name of the temporary file (without extension ".cnf") is returned.
*)

(*
** Refererence containing name of temporary file used
** for last invocation of a SAT solver
*)

val tmp_name = ref "undefined";

fun termToDimacsFile t =
 let open TextIO;
     val var_count    = length(all_vars t)
     val clause_count = length(strip_conj t)
     val _            = initSatVarMap()
     val dlist        = termToDimacs t
     val tmp          = FileSys.tmpName()
     val tmpname      = tmp^".cnf";
     val outstr       = TextIO.openOut tmpname
     fun out s        = output(outstr,s)
 in
 (out "c File "; out tmpname; out " generated by HolSatLib\n";
  out "c\n";
  out "p cnf ";
  out (Int.toString var_count); out " ";
  out (Int.toString clause_count); out "\n";
  app 
   (fn l => (app (fn p => (out(LiteralToString p); out " ")) l; out "\n0\n")) 
   dlist;
  flushOut outstr;
  closeOut outstr;
  tmp_name := tmp;
  tmp)
 end;

(* Functions for parsing the output of SAT solvers *)

(*
** substringContains s ss
** tests whether substring ss contains string s
*)

fun substringContains s ss = not(Substring.isEmpty(snd(Substring.position s ss)));

(*
** substringToInt converts a substring to an integer
*)

exception substringToIntError;
fun substringToInt ss =
 case Int.fromString(Substring.string ss) of
   SOME n => n
 | _      => raise substringToIntError;

(*
** parseSat (s1,s2) ss 
** returns a list of numbers corresponding to the tokenised
** substring of ss (tokenised wrt Char.isSpace) that starts immediately 
** after the first occurrence of s1 and ends just before the first 
** occurrence of s2 that is after the first occurrence of s1
*)

fun parseSat (s1,s2) ss =
 let val (ss1,ss2) = Substring.position s1 ss
     val ss3       = Substring.triml (String.size s1) ss2
     val (ss4,ss5) = Substring.position s2 ss3
     val ssl       = Substring.tokens Char.isSpace ss4
 in
  List.map substringToInt ssl
 end;


(*
** invokeSat solver t
** invokes solver on t and returns SOME s (where s is the satisfying instance
** as a string of integers) or NONE, if unsatisfiable
*)

(*
** Reference containing last command used to invoke a SAT solver
*)

val sat_command = ref "undef";

(*
** Test for success of the result of Process.system
** N.B. isSuccess expected to primitive in next release of
** Moscow ML, and Process.status will lose eqtype status
*)

fun isSuccess s = (s = Process.success);

fun invokeSat sat_solver t =
 let val SatSolver {name,
                    URL,
                    executable,
                    notime_run,
                    time_run,
                    only_true,
                    failure_string,
                    start_string,
                    end_string} = sat_solver
     val tmp        = termToDimacsFile t
     val infile     = tmp ^ ".cnf"
     val outfile    = tmp ^ "." ^ name
     val ex         = Globals.HOLDIR ^ "/src/HolSat/" ^ executable
     val run_cmd    = notime_run ex (infile,outfile)
     val _          = (sat_command := run_cmd)
     val code       = Process.system run_cmd
     val _          = if isSuccess code
                       then ()
                       else print("Warning:\n Process.system reports failure signal returned by\n " ^ run_cmd ^ "\n")
     val ins        = TextIO.openIn outfile
     val sat_res    = TextIO.inputAll ins
     val _          = TextIO.closeIn ins
     val sat_res_ss = Substring.all sat_res
     val result     = substringContains failure_string sat_res_ss
 in
  if result 
   then NONE
   else 
    let val model1 = parseSat(start_string,end_string)sat_res_ss
        val model2 = if only_true 
                      then model1
                           @
                           (map 
                             (fn n => 0-n) 
                             (subtract(map snd (snd(showSatVarMap())))model1))
                      else model1
    in
     SOME(map intToLiteral model2)
    end
 end;

(*
** satOracle sat_solver t
** invokes sat_solver on t and returns a theorem tagged by the solver name
** of the form |- (l1 /\ ... ln) ==> t (satisfied with literals l1,...,ln)
** or |- ~t (failure)
*)

(*
val _ = (show_tags := true);
*)

fun satOracle sat_solver t =
 let val SatSolver {name,
                    URL,
                    executable,
                    notime_run,
                    time_run,
                    only_true,
                    failure_string,
                    start_string,
                    end_string} = sat_solver
     val res = invokeSat sat_solver t
 in
  case res of
    SOME l => Thm.mk_oracle_thm (Tag.read name) ([], mk_imp(list_mk_conj l, t))
  | NONE   => Thm.mk_oracle_thm (Tag.read name) ([], mk_neg t)
 end;

(*
** satProve sat_solver t
** invokes sat_solver on t and if a model is found then
** then it is verified using proof in HOL and a theorem
** |- (l1 /\ ... /\ ln) ==> t is returned
** (where l1,...,ln are the literals making up the model);
** Raises satProveError if no model is found.
** Raises satCheckError if the found model is bogus
*)

(*
** satCheck [l1,...,ln] t 
** attempts to prove (l1 /\ ... /\ ln) ==> t 
** if it succeeds then the theorem is returned, else
** exception satCheckError is raised
*)

val EQT_Imp1 = tautLib.TAUT_PROVE ``!b. b ==> (b=T)``
and EQF_Imp1 = tautLib.TAUT_PROVE ``!b. (~b) ==> (b=F)``
and EQT_Imp2 = tautLib.TAUT_PROVE ``!b. (b=T) ==> b``;

exception satCheckError;
fun satCheck model t =
 (let val mtm  = list_mk_conj model
      val th1  = ASSUME mtm
      val thl  = map 
                  (fn th => if is_var(concl th) 
                             then MP (SPEC(concl th)EQT_Imp1) th 
                             else MP (SPEC (dest_neg(concl th))EQF_Imp1) th)
                  (CONJUNCTS th1)
      val subl = map (fn th => lhs(concl th) |-> th) thl
      val th2 = SUBST_CONV subl t t
      val th3 = CONV_RULE(RHS_CONV(Rewrite.REWRITE_CONV[])) th2
      val th4 = MP (SPEC t EQT_Imp2) th3
  in
   DISCH mtm th4
  end)  handle Interrupt => raise Interrupt
                    |  _ => raise satCheckError;

exception satProveError;
fun satProve sat_solver t =
 case invokeSat sat_solver t of
   SOME model => satCheck model t
 | NONE       => raise satProveError;



(*
** readDimacs filename
** reads a DIMACS format file called filename and returns
** a term in CNF in which each number n in the DIMACS file
** is a boolean variable (!prefix)n
** Code below by Ken Larsen (replaces earlier implementation by MJCG)
*)


fun isNewline #"\n" = true
  | isNewline _     = false;

fun dropLine get src = 
    StringCvt.dropl isNewline get (StringCvt.dropl (not o isNewline) get src);

fun stripPreamble get src =
    case get src of
        SOME(c, src') => if c = #"c" orelse c = #"p" 
                         then stripPreamble get (dropLine get src')
                         else SOME src
      | _             => NONE;

fun getInt get = Int.scan StringCvt.DEC get;

fun getIntClause get src =
    let fun loop src acc = 
            case getInt get src of
                SOME(i, src) => if i = 0 then SOME(acc, src)
                                else loop src (i::acc)
              | NONE         => if List.null acc then NONE
                                else SOME(acc, src)
    in  loop src []
    end;

(* This implementation is inspired by (and hopefully faithful to)
** dimacsToTerm.
*)

fun getTerms get src =
    let fun loop src acc =
            case getIntClause get src of
                SOME(ns, src) => loop src (mk_conj(acc, buildClause ns))
              | NONE          => SOME(acc, src)
    in  case getIntClause get src of
            SOME(ns, src) => loop src (buildClause ns)
          | NONE          => NONE
    end;

fun readTerms get src = 
    case stripPreamble get src of
        SOME src => getTerms get src
      | NONE     => NONE;

exception readDimacsError;

fun readDimacs filename =
 let val fullfilename = Path.mkAbsolute(filename, FileSys.getDir())
     val ins          = TextIO.openIn fullfilename
     val term         = TextIO.scanStream readTerms ins
 in  (TextIO.closeIn ins; 
      case term of SOME t => t | NONE => raise readDimacsError)
 end;

end
end
