 
structure minisatParse = 
struct

local 

open Globals Parse HolKernel boolSyntax boolTheory (* HOL4 term parsers etc *)  
open Array (* ML *)
open dimacsTools satCommonTools SatSolvers minisatResolve

 
in 

fun sat_fileopen s = BinIO.openIn s	

fun sat_fileclose is = BinIO.closeIn is

local open Word in 

(*read in the next byte*)
fun sat_getChar is = 
    let val v = BinIO.input1 is
    in if isSome v 
       then Word8.toLargeWord(valOf v) 
       else raise Domain end

infix orb
infix andb
infix <<
infix >>

(* adapted from Minisat-p_v1.14::File::getUInt*)
(* reads the next int, which may be encoded in 8, 16, 32 or 64 bits*)
(* FIXME: Currently this is untested and will likely crash on 64 bit archs*)
fun sat_getint' is = 
 let val  byte0 = sat_getChar is 
 in  if ((byte0 andb (0wx80))=(0wx0)) (* 8 *)
	then toInt(byte0)
    	else
        case toInt((byte0 andb (0wx60)) >> (Word.fromInt 5)) of
         0 => let val byte1 = sat_getChar is
             in toInt(((byte0 andb (0wx1F)) << (Word.fromInt 8)) orb byte1) end (* 16 *)
        | 1 => let val byte1 = sat_getChar is
                   val byte2 = sat_getChar is
            in 	toInt((((byte0 andb (0wx1F)) << (Word.fromInt 16)) 
			   orb (byte1 << (Word.fromInt 8))) orb byte2) end
        | 2 => let val byte1 = sat_getChar is
                   val byte2 = sat_getChar is
                   val byte3 = sat_getChar is
            in toInt(((((byte0 andb (0wx1F)) << (Word.fromInt 24)) 
			   orb (byte1 << (Word.fromInt 16))) 
			  orb (byte2 << (Word.fromInt 8))) orb byte3) end
	(* default case is only place where int64 is needed since we do a << 32*)
        | _ => let val byte0 = sat_getChar is
            	   val byte1 = sat_getChar is
            	   val byte2 = sat_getChar is
            	   val byte3 = sat_getChar is
            	   val byte4 = sat_getChar is
            	   val byte5 = sat_getChar is
            	   val byte6 = sat_getChar is
            	   val byte7 = sat_getChar is 
               in toInt((((byte0 << (Word.fromInt 24)) 
			      orb (byte1 << (Word.fromInt 16)) 
			      orb (byte2 << (Word.fromInt 8)) 
			      orb byte3) << (Word.fromInt 32)) 
			    orb ((byte4 << (Word.fromInt 24)) 
				     orb (byte5 << (Word.fromInt 16)) 
				     orb (byte6 << (Word.fromInt 8)) orb byte7))
	    end
        end	

fun sat_getint fin = 
    let val i = sat_getint' fin
    in i end

end

(* bitwise rightshift by 1 bit*)
fun rshift w = Word.toInt((op Word.>>) (Word.fromInt w,Word.fromInt 1))

(* parse resolution chain *)
fun getIntBranch fin id h = 
    let 
 	fun loop acc len = 
	    let val v = (sat_getint fin)-1 (*-1 is purely a decoding step 
				           (i.e. not translating b/w HolSat and ms)*)
 	    in if v=(~1) then ((v,h)::(rev acc),len+1)
	       else let val ci = id-(sat_getint fin)
 		    in loop ((v,ci)::acc) (len+1) end
	    end
	val res = loop [] 0
     in res  end

(* parse a resolution chain and add to sr stack as a (clause,var) list *)
(* the var component of the first pair is a dummy value ~1 *)
fun addBranch cl sva mcth rt2o fin cc id tc =
    let 
 	val (br,brl) = getIntBranch fin id (id-(rshift tc))
	val res = if brl=1 (*(tl br = []) *)
		  then (cc,false) (* delete *)
		  else let val _ = resolveChain sva rt2o mcth cl (br,brl) cc
		       in (cc+1,true) end (* resolve *) 
     in res
    end

(* Parse a root clause. Final result is int list of literals *) 
fun getIntRoot fin idx = 
    let  
 	fun loop idx' acc =  
	    let val v = sat_getint fin 
 	    in if v=0 then idx::(rev acc) else loop (idx'+v) ((idx'+v)::acc) end 
	val res = loop idx []
     in res  end

(* Parse a root clause and add it to the sr stack
   This advances the file read pointer 
	but we pick up the actual clause term from the vector 
        of clauses we already have, using the orc value.
   This is because minisat-p removes duplicate literals and sorts the literals so I can't
     efficiently find the corresponding clause term in HOL
   So this is faster (time and space) than building the clause term from the proof log.
*)
fun addClause cl svm sva rt2o vc cc mcth fin lit1 = 
    let  
         val orc = (rshift lit1)-1 (*-1 because right now orc's in proof log start at 1*)
	val l = getIntRoot fin (sat_getint fin) 	
	val res = case l of
	    []  => failwith ("addClause:Failed parsing clause "^(int_to_string (cc))^"\n")  
	  | _ => let 
 		     val ll = concl (Array.sub(mcth,orc)) 
		     val _ = Dynarray.update(rt2o,cc,orc)
			 handle Subscript => failwith("addClause"^(int_to_string (cc))^"\n")
		     val _ = Dynarray.update(cl,cc,prepareRootClause rt2o mcth cl cc)
		 in cc+1 end 
     in res end

(* SML equivalent of  C-style eval of v&1=0 *)
fun isRoot v = Word.compare(Word.andb(Word.fromInt v,Word.fromInt 1),(Word.fromInt 0))=EQUAL

(*cc is clause count (inc learnt) *)
 fun readTrace cl svm sva rt2o vc cc mcth fin id =
    if BinIO.endOfStream fin 
    then cc
    else 
	let val tmp = sat_getint fin
	in if isRoot tmp 
	   then let val cc = addClause cl svm sva rt2o vc cc mcth fin tmp
		in readTrace cl svm sva rt2o vc cc mcth fin (id+1) end
	   else (let val (cc,isch) = addBranch cl sva mcth rt2o fin cc id tmp 
		 in if isch 
		    then readTrace cl svm sva rt2o vc cc mcth fin (id+1) (* chain *)
		    else readTrace cl svm sva rt2o vc cc mcth fin id end) (* deletion *)
	end 
 
exception Trivial 

(*build the clause/chain list *)
fun parseTrace cl svm sva rt2o nr fname solver vc mcth = 
    let 
 	val fin = sat_fileopen (fname^"."^(getSolverName solver)^".proof")
	val cc = readTrace cl svm sva rt2o vc 0 mcth fin 0 
	val _ = sat_fileclose fin 
     in SOME cc end
handle Io _ => NONE

(*
nr: number of root clause
fname: filename of proof log
vc: number of variables (includes variables added by def CNF conversion)
mcth: root clause vector. mcth[i] is i'th root clause from original problem
*)
fun replayMinisatProof svm sva rt2o nr fname solver vc mcth = 
    let val _ = (minisatResolve.counter:=0)
	val cl = Dynarray.array((Array.length mcth) * 2,TRUTH)
	val cc = parseTrace cl svm sva rt2o nr fname solver vc mcth 
	val rth = Dynarray.sub(cl,(valOf cc)-1)
    in rth end

end
end
