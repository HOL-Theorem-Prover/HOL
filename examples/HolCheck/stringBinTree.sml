
(*List.app load ["bossLib","stringTheory","stringLib","HolBddLib","pairTheory","pred_setLib","listLib","CTL","pairSyntax","pairRules","pairTools","muTheory","boolSyntax","Drule","Tactical","Conv","Rewrite","Tactic","boolTheory","stringBinTreeTheory","computeLib"];*)

(* balanced strict bin tree term. At the moment we support one-time construction and find on string keys only *)
(* further, the string keys can only have dot, underscore, digits and upper/lower-case letters *)
(* this is useful for efficiently representing maps with string domains as HOL terms *)

structure stringBinTree =
struct

local 

open Globals HolKernel Parse goalstackLib;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;
open Psyntax;

open bossLib;
open pairTheory;
open pred_setTheory;
open pred_setLib;
open stringLib;
open listTheory;
open simpLib;
open pairSyntax; 
open pairLib;
open Binarymap;
open PairRules;
open pairTools;
open boolSyntax;
open Drule;
open Tactical;
open Conv;
open Rewrite;
open Tactic;
open boolTheory;
open listSyntax; 
open stringTheory;
open boolSimps; 
open pureSimps;
open listSimps;
open numLib;
open computeLib;

fun term_to_string2 t = with_flag (show_types,false) term_to_string t;

val ONCE_BETA_LET_CONV = (ONCE_DEPTH_CONV BETA_CONV) THENC (ONCE_DEPTH_CONV let_CONV);
val simpLib.SSFRAG bool_ss_thms = BOOL_ss;
val no_beta_BOOL_ss = rewrites (#rewrs bool_ss_thms) (* this is BOOL_ss w/o beta-reduction *)

(*apply first arg(conv) to test part of the cond term which is on the rhs of the snd arg (an eq term)*) 
val RHS_COND_TEST_CONV = RHS_CONV o RATOR_CONV o RATOR_CONV o RAND_CONV 

fun rmid L = List.nth(L,(List.length L) div 2); (* return middle or right middle element *)

(* take key list sorted in increasing order and return inorder traversal of corresponding balanced BST *)
fun inorder [] = []
|   inorder L = rmid(L)::(inorder(List.take(L,(List.length L) div 2)))@(inorder(List.drop(L,((List.length L) div 2)+1))) 

(* append a string of the minimum character, of the same length as the longest key (mxl), to all keys *)
(* this is so that char access for all keys is well-defined, for all indices < mxl *)
fun stuff_keys keys mxl = 
let  val stuffing = String.implode (List.tabulate(mxl,fn n => chr 33));
     in  (stuffing,Listsort.sort String.compare (List.map (fn k => k^stuffing) keys)) end 

(* rnkv[i] gives the index within keys of the ith most discriminiting characeter *)
(* clv[i] gives a list of all chars that occur at index i in the keys, with duplicates removed *) 
fun mk_rank keys mxl = 
  let  val cl0 = List.tabulate(mxl,fn n => Binaryset.empty Char.compare)
       val cl = List.foldl (fn (k,acl) => List.foldr 
			(fn ((bs,kc),acl2)=> (Binaryset.add(bs,kc))::acl2) [] (ListPair.zip(acl,explode k))) cl0 keys
       val (_,rnk) = ListPair.unzip(List.rev(Listsort.sort (fn ((r1,i1),(r2,i2)) => Int.compare(r1,r2)) 
			(ListPair.zip(List.map (fn bs => Binaryset.numItems bs) cl,List.tabulate(mxl,fn n => n)))))
       val rnkv = Vector.fromList rnk
       val clv = Vector.fromList (List.map Binaryset.listItems cl)
  in (rnkv,clv) end

(* constructs a term (HD o TL^n) *)
fun mk_list_nth n = List.foldl (fn (t,at) => ``^at o ^t``) ``HD:char list -> char`` 
							(List.tabulate(n,fn n => ``TL:char list -> char list``)); 

fun string_char_swap s i j = 
	String.implode(List.map (fn (c,k) => if (k=i) then String.sub(s,j) 
			      else if (k=j) then String.sub(s,i) else c)
	  (ListPair.zip(String.explode s,List.tabulate(String.size s,fn n => n))))

fun mk_leaf keymap ranks s mxl dummy =
    let val idx = (List.tabulate(mxl,fn n => n))
        val key = implode(List.filter (fn c => not(Char.compare(c,#"!")=EQUAL)) 
			(List.foldl (fn (i,al) => List.map 
				(fn (j,c) => if (j=(Vector.sub(ranks,i))) then String.sub(s,i) else c) 
					(ListPair.zip(idx,al))) (List.tabulate(mxl,fn n => #"+")) idx)
		  )

        (*val _ = printVal mxl; val _ = print " mxl\n"; 
        val _ = printVal ranks; val _ = print (" ranks\n");
	val _ = printVal s; val _ = print (" s\n");
        val _ = printVal key; val _ = print (" key\n");*)
    in Binarymap.find(keymap,key) handle NotFound => dummy end

(* chars at index i are all the same *)
fun areSame k i = fst(List.foldl (fn (ky,(b,c)) => if (not (Option.isSome c)) then (b,SOME (List.nth(explode ky,i))) 
						   else if (Char.compare(Option.valOf c,List.nth(explode ky,i))=EQUAL) 
						        then (b,c) 
						        else (false,c)) (true,NONE) k)


(* builds the BST for index i in the keys *)
fun mk_subtree keymap ranks cl mxl ccl i s k dummy = 
    if (List.null ccl) 
    then mk_tree_aux keymap ranks cl mxl (i+1) 
		     (s^(if (List.null k) then "+" else Char.toString (String.sub(hd k,Vector.sub(ranks,i))))) k dummy
    else let val (kl,kr) = List.partition (fn ky => String.sub(ky,Vector.sub(ranks,i))<(hd ccl)) k;
	     val dl = areSame kl (Vector.sub(ranks,i)); 
	     val dr = areSame kr (Vector.sub(ranks,i))
	     val lt = if dl then mk_tree_aux keymap ranks cl mxl (i+1) 
					     (s^(if (List.null kl) then "+" 
						 else Char.toString(String.sub(hd kl,Vector.sub(ranks,i))))) kl dummy
		      else mk_subtree keymap ranks cl mxl (List.take((tl ccl),(List.length ccl) div 2)) i s kl dummy
             val rt = if dr then mk_tree_aux keymap ranks cl mxl (i+1) 
					     (s^(if (List.null kr) then "+" 
						 else Char.toString(String.sub(hd kr,Vector.sub(ranks,i))))) kr dummy
		      else mk_subtree keymap ranks cl mxl (List.drop((tl ccl),(List.length ccl) div 2)) i s kr dummy
	 in mk_cond(list_mk_comb(numSyntax.less_tm,[mk_comb(``ORD``,mk_comb(mk_list_nth(Vector.sub(ranks,i)),
							      mk_var("x",``:char list``))),
					   numSyntax.mk_numeral(Arbnum.fromInt(ord(hd ccl)))]),lt,rt) end

(* glues together the BST's returned from mk_subtree *)
and mk_tree_aux keymap ranks cl mxl i s keys dummy = 
    if (i=mxl) 
    then mk_leaf keymap ranks s mxl dummy
    else let val ccl = Vector.sub(cl,Vector.sub(ranks,i))        
	 in if (((List.length ccl) = 1)  (* one-way branch, ignore *)
		orelse (areSame keys (Vector.sub(ranks,i)))) (* redundant branching, ignore *)
	    then mk_tree_aux keymap ranks cl mxl (i+1) 
			     (s^(if (List.null keys) then "+" (* "+" indicates a dummy node *)
				 else Char.toString (String.sub(hd keys,Vector.sub(ranks,i))))) keys dummy
	    else mk_subtree keymap ranks cl mxl (inorder ccl) i s keys dummy end

in

(* builds Patricia trie term for the given map *)
fun mk_tree abs keymap = 
  let val keys = fst(ListPair.unzip keymap)
      val keymap2 = List.foldl (fn ((k,v),bm) => Binarymap.insert(bm,k,v)) (Binarymap.mkDict String.compare) keymap
      (*val _ = printVal (Binarymap.listItems keymap2); val _ = print " keymap2\n";*)
      val mxl =  List.foldl (fn (k,msz) => if (msz<(String.size k)) then (String.size k) else msz) 0 keys;
      (*val _ = printVal mxl; val _ = print " mxl\n";*)
      val (stuffing,sk) =  stuff_keys keys mxl
     (*val _ = printVal sk; val _ = print " sk\n";*)
      val (ranks,cl) = mk_rank sk mxl
     (*val _ = printVal ranks; val _ = print " ranks\n";*)
     (*val _ = printVal cl; val _ = print " cl\n";*)
      val dummy = if (List.null keys) then ``ARB`` else ``ARB:^(ty_antiq(type_of (snd(hd keymap))))``
      val tree = mk_let(mk_abs(mk_var("x",``:char list``),
			       mk_tree_aux keymap2 ranks cl mxl 0 "" sk dummy),
					   ``EXPLODE (STRCAT t ^(fromMLstring stuffing))``)
  in mk_abs(mk_var("t",``:string``),if isSome abs then mk_pabs(valOf abs,tree) else tree) end

val find_CONV = 
    let val rws = new_compset [lazyfy_thm COND_CLAUSES,stringTheory.EXPLODE_EQNS,strictify_thm LET_DEF,strictify_thm literal_case_DEF,combinTheory.o_DEF,
			       listTheory.HD,listTheory.TL,listTheory.APPEND,stringTheory.IMPLODE_EQNS,
			       stringTheory.STRCAT]       
        val _ = add_conv (stringSyntax.ord_tm,1,stringLib.ORD_CHR_CONV) rws;
	val _ = add_conv (numSyntax.less_tm,2,numLib.REDUCE_CONV) rws;
    in CBV_CONV rws end
end
end;

(* 
load "stringBinTree";
open stringBinTree;
val k1 = [("m",``0``),("v0_0",``1``),("u0_0",``2``)];
val k2 = [("ac1",``1``),("ac",``2``),("bc",``3``),("cc",``4``)]; 
val ap = ["m","v2_2","v2_1","v2_0","v1_2","v1_1","v1_0","v0_2","v0_1","v0_0","u2_2","u2_1","u2_0","u1_2","u1_1","u1_0","u0_2","u0_1","u0_0"];
val k3 = List.map (fn s => (s,mk_var(s,``:bool``))) ap;
*)


