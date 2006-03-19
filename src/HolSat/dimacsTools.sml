 
structure dimacsTools = struct

local 

open Lib boolLib Globals Parse Term Type Thm Drule Psyntax Conv Feedback

 



in 


(*
** Mapping from HOL variable names to DIMACS  variable numbers
** is stored in a global assignable (i.e. reference) variable sat_var_map.
** The type of sat_var_map is (int * (term * int) set) ref and
** the integer first component is the next available number
** (i.e. it is one plus the number of elements in the set)
** in th second component (t,n), if n<0 then the literal represented is ~t (the stored t is never negated)
*)

(* 
** Initialise sat_var_map to integer 1 paired with the empty set
** (in DIMACS  variable numbering starts from 1 because 0
** is the clause separator)
*)

val sat_var_map = ref(1, Redblackmap.mkDict Term.compare);
val sat_var_arr = ref(Array.array(0,T)) (* varnum->+ve lit. *)

(*
** Reinitialise sat_var_map.
** Needs to be done for each translation of a term to DIMACS 
** as numbers must be an initial segment of 1,2,3,...
** (otherwise grasp, zchaff etc may crash)
*)

fun initSatVarMap var_count = (sat_var_map := (1, Redblackmap.mkDict Term.compare);
			       sat_var_arr := Array.array(var_count+1,T)); (*+1 'cos var numbers start at 1*)

(* 
** Lookup the var number corresponding to a +ve literal s, possibly extending sat_var_map 
*)

fun lookup_sat_var s =
 let val (c,svm) = !sat_var_map
 in
 case Redblackmap.peek(svm,s) of
   SOME(_,n) => n
 | NONE      => let val svm' = Redblackmap.insert(svm,s,(s,c))
                    val _    = (sat_var_map := (c+1,svm'))
		    val _    = Array.update(!sat_var_arr,c,s) 
			handle Subscript => 
			       failwith ("lookup_sat_varError: "^(term_to_string s)^"::"^(int_to_string c)^"\n")
                in c end
 end;

(* 
** Lookup the +ve lit corresponding to a var number 
*)
fun lookup_sat_num n = Array.sub(!sat_var_arr,n) 
    handle Subscript => failwith ("lookup_sat_numError: "^(int_to_string n)^"\n")
    

(* 
** Show sat_var_map as a list of its elements
*)

fun showSatVarMap() = 
 let val (c,st) = !sat_var_map
 in
  (c, List.map snd (Redblackmap.listItems st))
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
      if is_neg t 
       then 
        let val t1 = dest_neg t
        in if type_of t1 = bool 
            then (true, t1)
            else (print "``"; print_all_term t; print "``";
                  print " is not a literal"; raise literalToIntError)
        end
       else if type_of t = bool then (false, t)        
       else (print "``"; print_all_term t; print "``\n";
             print " is not a clause or literal\n"; raise literalToIntError)
     val v_num = lookup_sat_var v
 in
  (sign, v_num)
 end;

(* 
** Convert an integer (a possibly negated var number) to a literal, 
** raising lookup_sat_numError if the absolute value of
** the integer isn't in sat_var_map
*)
fun intToLiteral n = 
    let val t = lookup_sat_num (abs n)
    in if n>=0 then t else mk_neg t end

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
** when reading DIMACS 
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
** converts t to DIMACS  and then writes out a 
** file into the temporary directory.
** the name of the temporary file (without extension ".cnf") is returned.
*)

(*
** Refererence containing name of temporary file used
** for last invocation of a SAT solver
*)

val tmp_name = ref "undefined";

fun termToDimacsFile fname t var_count =
 let open TextIO;
      val clause_count = length(strip_conj t)
     val _            = initSatVarMap var_count
     val dlist        = termToDimacs t
     val tmp          = FileSys.tmpName()
     val tmpname      = if isSome fname then (valOf fname)^".cnf" else tmp^".cnf";
     val outstr       = TextIO.openOut tmpname
     fun out s        = output(outstr,s)
     val res = (out "c File "; out tmpname; out " generated by HolSatLib\n";
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
		if isSome fname then tmpname else tmp) 
  in res end

(*
** readDimacs filename
** reads a DIMACS  file called filename and returns
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
                SOME(ns, src) => loop src (mk_conj(buildClause ns, acc))
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
