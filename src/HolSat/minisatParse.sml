 
structure minisatParse = 
struct

local 

open Globals Parse HolKernel boolSyntax boolTheory (* HOL4 term parsers etc *)  
open Array (* ML *)
open satCommonTools minisatResolve SatSolvers

 
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
fun sat_getint is = 
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

(* parse and resolve a chain : assumes all dependencies already calculated *)
(* the var component of the first pair is a dummy value ~1 *)
fun addBranch lfn cl sva fin tc id =
    let val (br,brl) = getIntBranch fin id (id-(rshift tc))
	val res = if brl=1 (*(tl br = []) *)
		  then false (* delete *)
		  else 
		      ((*print "\nB ";print( (int_to_string id)^": "); 
		       List.app (fn (i,j) => 
				    print ((int_to_string i)^","^(int_to_string j)^" ")) br; *)
		      resolveChain lfn sva cl (br,brl) id; true) (* resolve *) 
    in res end

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
fun addClause lfn cl  sva vc clauseth fin lit1 id = 
    let val orc = (rshift lit1)-1 (*-1 because right now orc's in proof log start at 1*)
	val l = getIntRoot fin (sat_getint fin) 
	(*val _ = (print "\nR ";print((int_to_string orc)^"~"^(int_to_string id)^": "); 
		 List.app (fn i => print ((int_to_string i)^" ")) l) *)
    in case l of
	   []  => failwith ("addClause:Failed parsing clause "^(int_to_string id)^"\n")  
	 | _ => prepareRootClause lfn orc clauseth cl id
    end

(* SML equivalent of  C-style eval of v&1=0 *)
fun isRoot v = Word.compare(Word.andb(Word.fromInt v,Word.fromInt 1),(Word.fromInt 0))=EQUAL
	       
fun readTrace lfn cl sva vc clauseth fin id =
    if BinIO.endOfStream fin 
    then id
    else 
	let val tmp = sat_getint fin
	in if isRoot tmp 
	   then let val _ = addClause lfn cl sva vc clauseth fin tmp id
		in readTrace lfn cl  sva vc clauseth fin (id+1) end
	   else (let val isch = addBranch lfn cl sva fin tmp id
		 in if isch 
		    then readTrace lfn cl sva vc clauseth fin (id+1) (* chain *)
		    else readTrace lfn cl sva vc clauseth fin id end) (* deletion *)
	end 
 
exception Trivial 

(*build the clause/chain list *)
fun parseTrace cl sva nr fname solver vc clauseth lfn proof = 
    let 
 	val fin = sat_fileopen (if isSome proof then valOf proof 
				else fname^"."^(getSolverName solver)^".proof")
	val id = readTrace lfn cl sva vc clauseth fin 0 
	val _ = sat_fileclose fin 
     in SOME id end
handle Io _ => NONE

(*
nr: number of root clauses
fname: filename of proof log
vc: number of variables (includes variables added by def CNF conversion)
clauseth: root clause vector. clauseth[i] is i'th root clause from original problem
*)
fun replayProof sva nr fname solver vc clauseth lfn proof = 
    let val _ = (minisatResolve.counter:=0)
	val cl = Dynarray.array((Array.length clauseth) * 2,TRUTH)
    in case parseTrace cl sva nr fname solver vc clauseth lfn proof of
	   SOME id => SOME (Dynarray.sub(cl,id-1))
	 | NONE => NONE
    end

end
end
