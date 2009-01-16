 
structure dimacsTools = struct

local 

open Lib boolLib Globals Parse Term Type Thm Drule Conv Feedback
open satCommonTools

 
in 


(*
** Mapping from HOL variable names to DIMACS  variable numbers
** is stored in a global assignable (i.e. reference) variable sat_var_map.
** The type of sat_var_map is (int * (term * int) set) ref and
** the integer first component is the next available number
** (i.e. it is one plus the number of elements in the set)
** in th second component (t,n), if n<0 then the literal represented is ~t
   (the stored t is never negated)
*)

(* 
** Initialise sat_var_map to integer 1 paired with the empty set
** (in DIMACS  variable numbering starts from 1 because 0
** is the clause separator)
*)

structure SVM = Redblackmap

val var_to_string = fst o dest_var

(*
** Reinitialise sat_var_map.
** Needs to be done for each translation of a term to DIMACS 
** as numbers must be an initial segment of 1,2,3,...
** (otherwise grasp, zchaff etc may crash)
*)

val ttt0 = ref T
val ttt1 = ref T

fun rbmcomp (t0,t1) = 
    Term.compare(t0,t1)
    handle Out_of_memory => (ttt0:=t0;ttt1:=t1; print "rbmcomp\n"; raise Out_of_memory)



(* 
** Lookup the var number corresponding to a +ve literal s, possibly extending sat_var_map 
*)

fun lookup_sat_var svm sva s =
 let val (c,svm1) = svm
     val respeek = SVM.peek(svm1,s) 
 in
 (case respeek of
   SOME(_,n) => (n,svm)
 | NONE      => let val svm2 = SVM.insert(svm1,s,(s,c))
                    val svm'    =  (c+1,svm2)
		    val _    = Array.update(sva,c,s) 
			handle Subscript => 
			       (failwith ("lookup_sat_varError: "^(term_to_string s)^"::"
					  ^(int_to_string c)^"\n"))
                in (c,svm') end)
 end;

(* 
** Lookup the +ve lit corresponding to a var number 
*)
fun lookup_sat_num sva n = Array.sub(sva,n) 
    handle Subscript => failwith ("lookup_sat_numError: "^(int_to_string n)^"\n")
    

(* 
** Show sat_var_map as a list of its elements
*)

fun showSatVarMap svm = 
 let val (c,st) = svm
 in
  (c, List.map snd (SVM.listItems st))
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
fun literalToInt svm sva t =
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
     val (v_num,svm') = lookup_sat_var svm sva v
 in
  ((sign, v_num),svm')
 end;

(* 
** Convert an integer (a possibly negated var number) to a literal, 
** raising lookup_sat_numError if the absolute value of
** the integer isn't in sat_var_map
*)
fun intToLiteral sva n = 
    let val t = lookup_sat_num sva (abs n)
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
(* FIXME: if is_cnf, then assume the .cnf file is already present, and use that *)
fun termToDimacs0 svm sva t = 
    foldr
    (fn (c,(d,svm)) => 
	let val (l,svm') = (foldr (fn (p,(d,svm)) => 
				      let val (n,svm') = literalToInt svm sva p
				      in (n::d,svm') end) ([],svm) (strip_disj c)) 
	in (l :: d,svm') end) 
	    ([],svm) 
	    (strip_conj t)

(* tail recursive version*)
fun termToDimacs svm sva clauses numclauses = 
    Array.foldli (fn (ci,c,svm) => 
	let val (l,svm') = (List.foldl (fn (p,(d,svm)) => 
				      let val (n,svm') = literalToInt svm sva p
				      in (n::d,svm') end) ([],svm) (List.rev (strip_disj c))) 
	in (Array.update(numclauses,ci,l);svm') end) 
	    svm (clauses,0,NONE)

(*
** reference containing prefix used to make variables from numbers
** when reading DIMACS 
*)
val prefix = ref "v";

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
** Refererence containing name of temporary file used
** for last invocation of a SAT solver
*)

val tmp_name = ref "undefined";

(*
** termToDimacsFile t, where t is in CNF, 
** converts t to DIMACS  and then writes out a 
** file into the temporary directory.
** the name of the temporary file (without extension ".cnf") is returned,
** as well as a map from vars to DIMACS numbers, and an array inverting the map
*)

fun termToDimacsFile fname clause_count var_count clauses =
    let open TextIO;
	val svm          = (1,  SVM.mkDict rbmcomp) (* sat_var_map *)
	val sva          = Array.array(var_count+1,T) (* sat_var_arr *)
    in if var_count <> 0 then (* so we don't waste time creating empty cnf file *)
	   let val numclauses = Array.array(clause_count,[(false,0)])
	       val svm'  = termToDimacs svm sva clauses numclauses
	       val tmp          = FileSys.tmpName()
	       val cnfname      = if isSome fname then (valOf fname) else tmp^".cnf";
	       val outstr       = TextIO.openOut cnfname
	       fun out s        = output(outstr,s)
	       val res = (out "c File "; out cnfname; out " generated by HolSatLib\n";
			  out "c\n";
			  out "p cnf ";
			  out (Int.toString var_count); out " ";
			  out (Int.toString clause_count); out "\n";
			  Array.app 
			      (fn l => (List.app (fn p => (out(LiteralToString p); out " ")) l;
					out "\n0\n")) 
			      numclauses;
			  flushOut outstr;
			  closeOut outstr;
			  tmp_name := tmp;
			  (tmp,cnfname,svm',sva))
	   in res end else 
       ("","",svm,sva)
    end

(*Write out DIMACS file and build svm and sva*)
fun generateDimacs vc t clauseth nr = 
    let 
	val var_count  = if isSome vc then valOf vc else length(all_vars t)
	val clauses = if isSome clauseth 
		      then Array.tabulate(Array.length (valOf clauseth), 
				       fn i => fst (Array.sub(valOf clauseth,i)))
		      else Array.fromList (strip_conj t)
	val clause_count = if isSome nr then valOf nr else Array.length clauses
	val (tmp,cnf,svm,sva) = termToDimacsFile NONE clause_count var_count clauses
    in (tmp,cnf,sva,svm) end

(*
** readDimacs filename
** reads a DIMACS  file called filename and returns
** a term in CNF in which each number n in the DIMACS file
** is a boolean variable (!prefix)n
** Code below by Ken Larsen (replaces earlier implementation by MJCG)
** Changed by HA to not reverse order of clauses, and to return var count
*)


fun isNewline #"\n" = true
  | isNewline _     = false;

fun dropLine get src = 
    StringCvt.dropl isNewline get (StringCvt.dropl (not o isNewline) get src);

fun skip_p get src i = 
    if i=5 then SOME src
    else case get src of 
	     SOME (c,src') => skip_p get src' (i+1)
	   | NONE => NONE

fun getInt get = Int.scan StringCvt.DEC get;

fun stripPreamble get src =
    case get src of
        SOME(c, src') => 
	(case c of 
	     #"c" => stripPreamble get (dropLine get src')
	   | #"p" => 
	     let val src'' = skip_p get src 0
		 val res = getInt get (valOf src'')
	     in case res of 
		    SOME (vc,src') => SOME (dropLine get src',vc)
		  | _ =>  NONE
	     end
	   | _ => NONE)
      | _ => NONE

fun update_maps svm sva s i =
    if is_T (Array.sub(sva,i)) 
    then let val (c,svm1) = svm
	     val svm2 = SVM.insert(svm1,s,(s,i))
	     val c' = if i>c then i else c
             val svm'    =  (c'+1,svm2)
	     val _    = Array.update(sva,i,s) 
		 handle Subscript => 
			(failwith ("update_mapsError: "^(term_to_string s)^"::"
				   ^(int_to_string i)^"\n"))
         in svm' end
    else svm


fun getIntClause sva svm get src =
    let fun loop src (acc,svm) = 
            case getInt get src of
                SOME(i, src) => if i = 0 then SOME((acc,svm), src)
                                else 
				    let val ai = (if i<0 then ~i else i)
					val v = intToPrefixedLiteral ai
					val svm' = update_maps svm sva v ai
				    in loop src ((i::acc),svm') end
              | NONE         => if List.null acc then NONE
                                else SOME((acc,svm), src)
    in  loop src ([],svm)
    end

(* This implementation is inspired by (and hopefully faithful to)
** dimacsToTerm.
*)

fun getTerms sva svm get src =
    let fun loop src (acc,svm,sva) =
            let val res =  getIntClause sva svm get src 
	    in case res of
                SOME((ns,svm'), src) => loop src (buildClause ns::acc,svm',sva)
              | NONE          => SOME((acc,svm,sva), src)
	    end
    in case getIntClause sva svm get src of
           SOME((ns,svm'), src) => loop src ([buildClause ns],svm',sva)
         | NONE          => NONE
    end;

fun readTerms get src =
    case stripPreamble get src of
        SOME (src,var_count) => 
		  let val svm = (0,  SVM.mkDict rbmcomp) (* sat_var_map *)
		      val sva = Array.array(var_count+1,T) (* sat_var_arr *)
		  in getTerms sva svm get src end
      | NONE     => NONE


exception readDimacsError;

fun genReadDimacs filename =
 let val fullfilename = Path.mkAbsolute(filename, FileSys.getDir())
     val ins          = TextIO.openIn fullfilename
     val res = TextIO.scanStream readTerms ins
 in  (TextIO.closeIn ins; 
      case res of 
	  SOME (cs,svm,sva) => (list_mk_conj (List.rev cs),svm,sva)
	| NONE => raise readDimacsError)
 end;

fun readDimacs filename = #1 (genReadDimacs filename)

end
end
