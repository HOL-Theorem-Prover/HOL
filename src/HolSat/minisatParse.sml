 
structure minisatParse = 
struct

local 

open Globals Parse HolKernel bossLib 
open Array boolSyntax boolTheory AC Drule Conv Rewrite BinIO Feedback
open satCommonTools dimacsTools 

 
in 

datatype rootc = RTHM of thm * (bool * int) set * term * thm | LL of term * (bool * int) set

datatype clause = BLANK 
		| CHAIN of (int * int) list * int (* var, cl index list and the length of that list *) 
		| ROOT of rootc
		| LEARNT of thm * (bool * int) set (* clause  thm, lits as nums set *)

fun sat_fileopen s = openIn s	

fun sat_fileclose is = closeIn is

local open Word in 

fun sat_getChar is = 
let val v = input1 is
    (*val _ = print ("c:"^(Int.toString(toInt(Word8.toLargeWord(valOf v))))) val _ = print "\n"*)
in if isSome v then Word8.toLargeWord(valOf v) else raise Domain end

infix orb
infix andb
infix <<
infix >>

(* copied from Minisat-p_v1.14::File::getUInt*)
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
            in 	toInt( (((byte0 andb (0wx1F)) << (Word.fromInt 16)) orb (byte1 << (Word.fromInt 8))) orb byte2) end
        | 2 => let val byte1 = sat_getChar is
                   val byte2 = sat_getChar is
                   val byte3 = sat_getChar is
            in toInt(((((byte0 andb (0wx1F)) << (Word.fromInt 24)) orb (byte1 << (Word.fromInt 16))) 
			orb (byte2 << (Word.fromInt 8))) orb byte3) end
(* default case is only where int64 is needed since we do a << 32*)
        | _ => let val byte0 = sat_getChar is
            	   val byte1 = sat_getChar is
            	   val byte2 = sat_getChar is
            	   val byte3 = sat_getChar is
            	   val byte4 = sat_getChar is
            	   val byte5 = sat_getChar is
            	   val byte6 = sat_getChar is
            	   val byte7 = sat_getChar is 
               in toInt((((byte0 << (Word.fromInt 24)) orb (byte1 << (Word.fromInt 16)) orb (byte2 << (Word.fromInt 8)) orb byte3) << (Word.fromInt 32)) orb  ((byte4 << (Word.fromInt 24)) orb (byte5 << (Word.fromInt 16)) orb (byte6 << (Word.fromInt 8)) orb byte7))
	    end
        end	

fun sat_getint fin = 
let val i = sat_getint' fin
(*val _ = print (Int.toString i) val _ = print "\n"*)
in i end

end

val lnscf = Int.compare o (snd##snd)

fun isRootClauseIdx cl ci = case Array.sub(cl,ci) of ROOT _ => true | _ => false 
	    
(* p is a literal *)
(* this mapping allows shadow ac-normalisation which keeps the lits for a given var together *)
(* the -1 is because literalToInt returns HolSatLib var numbers (base 1) *)
fun literalToInt2 p = 
    let val (sign,vnum) = literalToInt p
    in 2*(vnum-1)+(if sign then 1 else 0) end

fun literalToInt3 p = let val (sign,vnum) = literalToInt p in (sign,vnum-1) end

(* parse a root clause *) 
fun getIntRoot fin idx = 
    let  
 	fun loop idx' acc =  
	    let val v = sat_getint fin 
 	    in if v=0 then idx::(rev acc) else loop (idx'+v) ((idx'+v)::acc) end 
	val res = loop idx []
     in res  end

fun rshift w = Word.toInt((op Word.>>) (Word.fromInt w,Word.fromInt 1))

(*l1 and l2 are number reps of lits. Are they complements? *)
fun is_compl l1 l2 = (abs(l2-l1)=1) andalso (l1 div 2 = 0) 

(*il is clause input from minisat proof trace, 
  sl is internal clause sorted and unduped, with diff in var numbering account for *)
(* thus if il and sl are not exactly the same, then the clause represented by sl was skipped *)
fun isSameClause (ilh::ilt) (slh::slt) = (ilh=slh) andalso isSameClause ilt slt 
  | isSameClause [] (slh::slt) = false
  | isSameClause (ilh::ilt) [] = false
  | isSameClause [] [] = true

fun getNextRootClause scl vc cc lr il rcv = 
    let val rc = Vector.sub(rcv,lr)
 	val rcl = (strip_disj rc)
	val lnl = List.map literalToInt3 rcl
 	val lns = HOLset.addList(HOLset.empty lnscf,lnl)
        val slnl = List.map (fn (isn,vi) => if isn then 2*vi+1 else 2*vi) (HOLset.listItems lns)
     in if isSameClause il slnl
	   then (Array.update(scl,lr,cc);(lr,(rc,lns))) 
       else (();getNextRootClause scl vc cc (lr+1) il rcv) end

(* this advances the file read pointer but we pick up the actual clause from the list of clauses we already have
   this is because minisatp removes duplicate literals and sorts the literals so I can't
     efficiently find the corresponding clause term in HOL
   assert: minisatp logs the root clauses in order of input*)
fun addClause scl vc cc lr rcv fin sr lit1 = 
    let  
 	val l = getIntRoot fin (rshift lit1) 
	val res = case l of
	    []  => failwith ("addClause:Failed parsing clause "^(int_to_string (cc))^"\n")  
	  | _ => let 
 		     val (lr,ll) = getNextRootClause scl vc cc lr l rcv
		 in (cc+1,lr+1,(ROOT (LL ll))::sr) end 
     in res end

(* parse resolve chain *)
fun getIntBranch fin id h = 
    let 
 	fun loop acc len = 
	    let val v = (sat_getint fin)-1 (*-1 is purely a decoding step 
						    (i.e. not translating b/w HolSat and ms representation)*)
 	    in if v=(~1) then ((v,h)::(rev acc),len+1)
	       else let val ci = id-(sat_getint fin)
 		    in loop ((v,ci)::acc) (len+1) end
	    end
	val res = loop [] 0
     in res  end

fun addBranch fin sr cc id tc =
    let 
 	val (br,brl) = getIntBranch fin id (id-(rshift tc))
	val res = if brl=1 (*(tl br = []) *)
		  then (cc,false,sr) (* delete *)
		  else (cc+1,true,(CHAIN (br,brl))::sr) (* resolve *) 
     in res
    end

(* v&1=0 C-style eval *)
fun isRoot v = Word.compare(Word.andb(Word.fromInt v,Word.fromInt 1),(Word.fromInt 0))=EQUAL

(*this is modelled on MiniSat::Proof::traverse, except we first read in everything then resolve backwards *)
(*sr is stack for originally reading in the clauses *)
(*lr is unskipped root clause count. *)
(*cc is clause count (inc learnt) *)
fun readTrace_aux scl vc cc lr rcv fin sr id =
    let
 	val res = let val tmp = sat_getint fin
		  in if isRoot tmp 
			 then let val (cc,lr,sr) = addClause scl vc cc lr rcv fin sr tmp
			      in readTrace_aux scl vc cc lr rcv fin sr (id+1) end
		     else (let val (cc,isch,sr') = addBranch fin sr cc id tmp 
			   in if isch then readTrace_aux scl vc cc lr rcv fin sr' (id+1) (* chain *)
			      else readTrace_aux scl vc cc lr rcv fin sr' id end)	(* deletion *)		      
		  end handle Domain => (cc,sr)
     in res end

fun a2l a = Array.foldl (fn (ae,l) => ae::l) [] a

exception Trivial 

(*fill in the root clause and chain array*)
fun parseTrace nr fname vc rcv = 
    let 
 	val fin = sat_fileopen fname 
	val scl = Array.array(nr,~1) (*cl[scl[i]]=rcv[i] or scl[i]=~1 if rcv[i] was trivial *)
	val (cc,sr) = readTrace_aux scl vc 0 0 rcv fin [] 0 
	val _ = sat_fileclose fin 
     in SOME (cc,sr,scl) end
handle Io _ => NONE

fun getChain (CHAIN ch) = fst ch
  | getChain _ = failwith("getChain: not a CHAIN")

(*make backwards pass through cl, returning only the chains actually used in deriving F*)
fun mk_sk cl ca ci =     
    let val ch = List.foldl (fn ((v,cci),ch) => if Array.sub(ca,cci) orelse isRootClauseIdx cl cci 
						then ch 
						else (mk_sk cl ca cci)::ch) [] 
			    (getChain (Array.sub(cl,ci)))
    in (Array.update(ca,ci,true);ci::(List.concat ch)) end

fun parseMinisatProof nr fname vc rcv = 
    case parseTrace nr fname vc rcv of
	SOME (cc,sr,scl) => 
	    let val lsr = List.length sr
		val cl = Array.array(lsr,BLANK) (*stores clauses as root clauses, learnt clauses or unresolved chains *)
 		val _ = List.foldl (fn (c,i) => (Array.update(cl,i-1,c);i-1)) cc sr 
		val sk = mk_sk cl (Array.array(lsr,false)) (cc-1)
	    in SOME (cl,sk,scl,lsr,cc) end  
      | NONE => NONE
end
end
