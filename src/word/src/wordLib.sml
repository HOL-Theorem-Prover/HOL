structure wordLib :> wordLib =
struct

local open wordTheory in end;

open res_quanLib listLib numLib;
open HolKernel Parse boolLib Prim_rec Rsyntax;
infix THEN THENL THENC ##;

 type term = Term.term
 type tactic = Abbrev.tactic
 type conv = Abbrev.conv

fun WORD_LIB_ERR {function,message} =
               HOL_ERR{origin_structure = "wordLib",
                       origin_function = function,
                       message = message};


val word_CASES_TAC =
    let val cthm = word_baseTheory.word_cases
    in
      fn w => CHOOSE_THEN SUBST1_TAC (ISPEC w cthm)
    end ;

val word_INDUCT_TAC =
    let val ithm = word_baseTheory.word_induct
    in
    (INDUCT_THEN ithm (fn t => ALL_TAC))
    end;

val RESQ_WORDLEN_TAC =
    (CONV_TAC RESQ_FORALL_CONV THEN word_INDUCT_TAC
     THEN PURE_ONCE_REWRITE_TAC[word_baseTheory.PWORDLEN_DEF]
     THEN GEN_TAC THEN DISCH_TAC);


(* --------------------------------------------------------------------- *)
(* BIT_CONV : conv   	    	    					*)
(* BIT_CONV (--`BIT k (WORD [bn-1,...,bk,...b0])`--) returns a theorem	*)
(* |- BIT k (WORD [bn-1,...,bk,...b0]) = bk				*)
(* --------------------------------------------------------------------- *)
val BIT_CONV =
  let val defthm = word_baseTheory.BIT_DEF
  fun check tm = assert (fn t => #Name(dest_const t) = "BIT") tm
  val int_of_term = string_to_int o #Name o dest_const
  in
  fn tm =>
    let val (_,[N,W]) = (check ## I) (strip_comb tm)
    val LST =  #Rand (dest_comb W)
    val lst = (#1 o listSyntax.dest_list) LST
    val n = int_of_term N
    in
    if not(n < (length lst))
    then raise WORD_LIB_ERR {function="BIT_CONV",message="index too large"}
    else (RIGHT_CONV_RULE ELL_CONV (ISPECL[N, LST] defthm))
    end
  end
     handle HOL_ERR {message = message,...} =>
            (raise WORD_LIB_ERR {function="BIT_CONV",
                                      message=message});


(* --------------------------------------------------------------------- *)
(* WSEG_CONV : conv   	    	    					*)
(* WSEG_CONV (--`WSEG m k (WORD [bn-1,...,bk,...b0])`--) returns a theorem	*)
(* |- WSEG m k (WORD [bn-1,...,bk,...b0]) = WORD [b(m+k-1), ..., bk]	*)
(* --------------------------------------------------------------------- *)
val WSEG_CONV =
  let val defthm = word_baseTheory.WSEG_DEF
  fun check tm = assert (fn t =>  #Name(dest_const t) = "WSEG") tm
  val int_of_term = string_to_int o #Name o dest_const
  in
  fn tm =>
    let val (_,[N,INX,W]) = (check ## I) (strip_comb tm)
    val LST =  #Rand (dest_comb W)
    val lst = (#1 o listSyntax.dest_list) LST
    val n = int_of_term N and inx = int_of_term INX
    in
    if ((n+inx) > (length lst))
    then raise WORD_LIB_ERR {function="WSEG_CONV",message="index too large"}
    else (RIGHT_CONV_RULE (((RAND_CONV o RAND_CONV)
                 BUTLASTN_CONV)
       THENC (RAND_CONV LASTN_CONV))
                      (ISPECL[N, INX, LST] defthm))
    end
  end
     handle HOL_ERR {message = message,...} =>
            raise WORD_LIB_ERR {function="WSEG_CONV",
                                      message=message};


(* --------------------------------------------------------------------- *)
(* PWORDLEN_CONV : term list -> conv					*)
(* PWORDLEN_CONV tms (--`PWORDLEN n tm`--) returns a theorem A |- PWORDLEN n tm*)
(* The input term tm should be in the following form:			*)
(*  WORD [ bs ]	    	    	    					*)
(*  WSEG m k tm' and tms should be [ N ] which indicates the size of tm'	*)
(*   	(m + k) <= N	    	    					*)
(*  WNOT tm' 	    PWORDLEN n tm' |- PWORDLEN n (WNOT tm')		*)
(*  WAND tm' tm''    PWORDLEN n tm', PWORDLEN n tm'' 			*)
(*   	    	    |- PWORDLEN n (WAND tm' tm'')			*)
(*  WOR tm' tm''     PWORDLEN n tm', PWORDLEN n tm'' 			*)
(*   	    	    |- PWORDLEN n (WOR tm' tm'')			*)
(*  WXOR tm' tm''    PWORDLEN n tm', PWORDLEN n tm'' 			*)
(*   	    	    |- PWORDLEN n (WXOR tm' tm'')			*)
(*  WCAT (tm',tm'')  tms should be [ n1, n2 ] and n1 + n2 = n		*)
(*   	    	    PWORDLEN n1 tm', PWORDLEN n2 tm''			*)
(*   	    	    |- PWORDLEN n (WCAT tm', tm'')			*)
(* --------------------------------------------------------------------- *)

val term_of_int =
    let val ty = (==`:num`==) in
      fn n =>  mk_const{Name=int_to_string n,Ty=ty}
    end ;

val int_of_term = string_to_int o #Name o dest_const ;

val LESS_MONO_EQ = arithmeticTheory.LESS_MONO_EQ
and LESS_ANTISYM = arithmeticTheory.LESS_ANTISYM
and NOT_LESS = arithmeticTheory.NOT_LESS
and NOT_LESS_EQ = prim_recTheory.NOT_LESS_EQ
and LESS_0 = prim_recTheory.LESS_0;

val LESS_CONV =
  let fun check s = assert (fn x =>  #Name(dest_const x) = s)
  fun less_conv t = EQT_INTRO (REWRITE_RULE[LESS_MONO_EQ,LESS_0]
    	                                   (REDEPTH_CONV num_CONV t))
  in
  fn tm =>
    let val (_,[M,N]) = ((check "<") ## I) (strip_comb tm)
    val m = int_of_term M and n = int_of_term N
    in
     if (m < n)
     then  let val t = mk_comb{Rator=mk_comb{Rator=(--`<`--),Rand=M},Rand=N}
           in
    	       less_conv t
           end
     else if (m = n)
     then EQF_INTRO (MATCH_MP NOT_LESS_EQ
                         (EQT_ELIM (reduceLib.NEQ_CONV (--`^M = ^N`--))))
     else  let val t = mk_comb{Rator=mk_comb{Rator=(--`<`--),Rand=M},Rand=N}
           in
    	    EQF_INTRO (PURE_REWRITE_RULE[AND_CLAUSES, less_conv t]
    	                     (SPECL[M,N]LESS_ANTISYM))
           end
   end
  end;

(* --------------------------------------------------------------------- *)
(* LESS_EQ_CONV : conv  	    	    					*)
(* LESS_EQ_CONV (--`m <= n`--)  ---> |- (m <= n) = T iff m < n		*)
(*   	    	    	      |- (m <= n) = F otherwise			*)
(* --------------------------------------------------------------------- *)

val LESS_EQ_CONV =
  let val MATCH_EQ_MP = fn eq => fn lh =>
              EQ_MP (PART_MATCH lhs eq (concl lh)) lh
  fun check s = assert (fn x => #Name(dest_const x) = s)
  val nthm = GEN_ALL (PURE_REWRITE_RULE[NOT_CLAUSES,
    	GEN_ALL (SYM (el 4 (CONJ_LIST 4 (SPEC_ALL EQ_CLAUSES))))]
    	(AP_TERM (--`$~`--) (SPEC_ALL NOT_LESS)))
  in
   fn tm =>
    let val (_,[M,N]) = ((check "<=") ## I) (strip_comb tm)
    val m = int_of_term M
    val n = int_of_term N
    in
     if (m > n)
     then  let val t = mk_comb{Rator=mk_comb{Rator=(--`<`--),Rand=N},Rand=M}
           in
    	    MATCH_EQ_MP nthm (EQT_ELIM (LESS_CONV t))
           end
     else if (m = 0) then (EQT_INTRO
               (SPEC N (arithmeticTheory.ZERO_LESS_EQ)))
     else (EQT_INTRO (REWRITE_RULE[arithmeticTheory.LESS_EQ_MONO,
                                   arithmeticTheory.ZERO_LESS_EQ]
    	     (REDEPTH_CONV num_CONV tm)))
    end
  end;

val word_inst_thm = fn (n,w) => fn th => (RESQ_SPEC w (SPEC n th));

val WNOT_PWORDLEN = RESQ_MATCH_MP word_bitopTheory.PBITOP_PWORDLEN
                                  bword_bitopTheory.PBITOP_WNOT;

val [WAND_PWORDLEN, WOR_PWORDLEN, WXOR_PWORDLEN] =
    let val pthm =  word_bitopTheory.PBITBOP_PWORDLEN
    in
    map (RESQ_MATCH_MP pthm)
        [bword_bitopTheory.PBITBOP_WAND,
         bword_bitopTheory.PBITBOP_WOR,
         bword_bitopTheory.PBITBOP_WXOR]
    end;

val pwordlen_bitop_funs =
    [("WNOT", WNOT_PWORDLEN),
     ("WAND", WAND_PWORDLEN),
     ("WOR",  WOR_PWORDLEN),
     ("WXOR", WXOR_PWORDLEN)];

val pwordlen_funs =
    let val PWORDLEN_DEF = word_baseTheory.PWORDLEN_DEF
    in
    	[("WORD",  (fn tms => fn  n => fn w =>
    	    if (int_of_term n) = 0 then
              REWRITE_RULE[rich_listTheory.LENGTH]
                   (ISPECL[n,hd w] PWORDLEN_DEF)
    	    else
              REWRITE_RULE[]
    	      (CONV_RULE ((RAND_CONV o RAND_CONV) LENGTH_CONV)
                (ISPECL[n,(hd w)]PWORDLEN_DEF)))),
    	 ("WSEG",   fn tms => fn  n => fn w =>
    	    let fun prove_less_eq m n =
    	      let val th = LESS_EQ_CONV
    	        (mk_comb{Rator=mk_comb{Rator=(--`$<=`--),
                                       Rand=term_of_int m},
                         Rand=term_of_int n})
              in
    	       if (m > n) then EQF_ELIM th else EQT_ELIM th
              end
            val [m,k,wd] =  w
            in
    	       MP (CONV_RULE
    	          ((RATOR_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
                     reduceLib.ADD_CONV)
    	          (SPECL [m,k] (word_inst_thm ((hd tms), wd)
    	    	   (word_baseTheory.WSEG_PWORDLEN))))
       	         (prove_less_eq ((int_of_term m) + (int_of_term k))
    	    	      (int_of_term (hd  tms)))
           end ),
    	 ("WNOT",  (fn tms => fn  n => fn w =>
    	    word_inst_thm (n, (hd w)) WNOT_PWORDLEN) ),
    	 ("WAND", (fn tms => fn  n => fn w =>
    	    (RESQ_SPECL w (SPEC n WAND_PWORDLEN)))  ),
    	 ("WOR",  (fn tms => fn  n => fn w =>
    	    (RESQ_SPECL w (SPEC n WOR_PWORDLEN)))  ),
    	 ("WXOR", (fn tms => fn  n => fn w =>
    	    (RESQ_SPECL w (SPEC n WXOR_PWORDLEN)))  ),
         ("WCAT", fn tms => fn  n => fn w =>
    	    let val (w1, w2) = pairSyntax.dest_pair (hd w)
    	    val n1 = hd tms and n2 = hd(tl tms)
    	    val N1 = int_of_term n1 and N2 = int_of_term n2
            in
     	    (if not((int_of_term n) = (N1 + N2))
     	     then raise WORD_LIB_ERR{function="pwordlen_funs",
                                      message="theorems and term do not match"}
     	     else
    	     (CONV_RULE ((RATOR_CONV o RAND_CONV) reduceLib.ADD_CONV)
    	      (itlist word_inst_thm [(n2,w2), (n1,w1)]
    	    	(word_baseTheory.WCAT_PWORDLEN))))
            end )
    	 ]
   end;

fun check s = assert (fn x => #Name(dest_const x) = s) ;

fun pick_fn s l oper =
    	let val ops = #Name (dest_const oper)
        in
         snd (first (fn (s,t) => (s = ops)) l)
        end
           handle _ =>
            raise WORD_LIB_ERR {function="pick_fn",  message=s};

val PWORDLEN_CONV =
  fn tms => fn tm =>
    let val (_,[n,w']) = ((check "PWORDLEN") ## I) (strip_comb tm)
    val (wc,w) = strip_comb w'
    val f = pick_fn "unknown constant" pwordlen_funs wc
    in
       EQT_INTRO(f tms n w)
    end
     handle HOL_ERR {message = message,...} =>
            raise WORD_LIB_ERR {function="PWORDLEN_CONV",
                                      message=message};

(* --------------------------------------------------------------------- *)
(* PWORDLEN_bitop_CONV : conv						 *)
(* PWORDLEN_bitop_CONV tms (--`PWORDLEN n tm`--) returns a theorem	 *)
(* A |- PWORDLEN n tm	    	    					 *)
(* The input term tm should be in the following form:			 *)
(*  WNOT tm' 	     PWORDLEN n vi,... |- PWORDLEN n (WNOT tm')		 *)
(*  WAND tm' tm''    PWORDLEN n vi,... |- PWORDLEN n (WAND tm' tm'')	 *)
(*  WOR tm' tm''     PWORDLEN n vi,... |- PWORDLEN n (WOR tm' tm'')	 *)
(*  WXOR tm' tm''    PWORDLEN n vi,... |- PWORDLEN n (WXOR tm' tm'')	 *)
(* where the vi's are variables in tm'.					 *)
(* --------------------------------------------------------------------- *)

fun PWORDLEN_bitop_CONV tm =
     let val {Rator=pw,Rand=w'} = dest_comb tm
     val _ = check "PWORDLEN"  (#Rator(dest_comb pw))
     val n =  #Rand(dest_comb pw)
     in
     if (is_var w') then (ASSUME tm)
     else
         let val (wc,w) = strip_comb w'
    	 val thm1 = GQSPECL (n :: w)
    	    (pick_fn "unknown bitop" pwordlen_bitop_funs wc)
         in
         EQT_INTRO(itlist PROVE_HYP (map PWORDLEN_bitop_CONV (hyp thm1)) thm1)
         end
    end
     handle HOL_ERR {message = message,...} =>
            raise WORD_LIB_ERR {function="PWORDLEN_bitop_CONV",
                                      message=message};


(* ---------------------------------------------------------------------*)
(* WSEG_WSEG_CONV (--`N`--) (--`WSEG m2 k2 (WSEG m1 k1 w)`--) --->	*)
(* PWORDLEN N w |- WSEG m2 k2 (WSEG m1 k1 w) = WSEG m2 k w		*)
(*   where k = k1 + k2 and k1+m1 <= N /\ k2+m2 <= m1			*)
(*   and N, k1, k2, m1,m2 are all constants				*)
(* ---------------------------------------------------------------------*)

val WSEG_WSEG_CONV =
   let fun check s = assert (fn x => #Name(dest_const x) = s)
   val thm' = word_baseTheory.WSEG_WSEG
   fun add_less_eq_conv k m n =
    	(((RATOR_CONV o RAND_CONV) reduceLib.ADD_CONV) THENC LESS_EQ_CONV)
    	(mk_comb{Rator=mk_comb{Rator=(--`<=`--),
                               Rand=mk_comb{Rator=mk_comb{Rator=(--`$+`--),
                                                          Rand=k},
                                            Rand=m}
                              },
                 Rand=n})
   in
   fn N => fn tm =>
    let val  (_,[m2,k2,s]) = ((check "WSEG") ## I) (strip_comb tm)
    val (_,[m1,k1,w]) = ((check "WSEG") ## I) (strip_comb s)
    val thm = GQSPECL [N, w, m1, k1, m2, k2] thm'
    in
    (RIGHT_CONV_RULE ((RATOR_CONV o RAND_CONV) reduceLib.ADD_CONV)
    (MP thm (CONJ (EQT_ELIM (add_less_eq_conv m1 k1 N))
    	    	 (EQT_ELIM (add_less_eq_conv m2 k2 m1)))))
    end
   end;
(*
 * ---
 * Example calls:
 *
 * WSEG_WSEG_CONV (--`10`--)
 *    (--`WSEG 2 2 (WSEG 5 3 (w:num word))`--);
 * val it = . |- WSEG 2 2 (WSEG 5 3 w) = WSEG 2 5 w : thm
 *
 * WSEG_WSEG_CONV (--`10`--)
 *     (--`WSEG 2 2 (WSEG 5 3 (WORD[1;2;3;4;5;6;7;8;9;10]))`--);
 * val it =
 *   .
 *   |- WSEG 2 2 (WSEG 5 3 (WORD [1; 2; 3; 4; 5; 6; 7; 8; 9; 10])) =
 *      WSEG 2 5 (WORD [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]) : thm
 ************************************************************************)

(* --------------------------------------------------------------------- *)
(* PWORDLEN_TAC = -: term list -> tactic				*)
(*      A ?- PWORDLEN n tm   	    					*)
(*    ========================== PWORDLEN_TAC l				*)
(*      A, A' ?- PWORDLEN n tm'	    					*)
(* The input list is the same as PWORDLEN_CONV.				*)
(* let th = PWORDLEN_CONV l (--`PWORDLEN n tm`--)			*)
(*        = A' |- PWORDLEN n tm	    					*)
(* It solves the goal if all the hypotheses of th (ie. A') are already 	*)
(* in A, otherwise, returns the above subgoal.				*)
(* --------------------------------------------------------------------- *)

fun PWORDLEN_TAC l =
  fn (asm,gl) =>
(* Old code. let val th = PWORDLEN_CONV l gl.  Fix:Paul Curzon, Feb1,94   *)
    let val th = EQT_ELIM(PWORDLEN_CONV l gl)
    val hyps = hyp th
    in
    if null hyps
    then (ACCEPT_TAC th) (asm,gl)
    else
      let val mlist =
    	mapfilter (fn h => if not(mem h asm)
                           then h
                           else raise HOL_ERR {origin_function="PWORDLEN_TAC",
                                               origin_structure="",
                                                     message=""}) hyps
      in
      if null mlist then ((ACCEPT_TAC th) (asm,gl))
      else
        let val sgl = list_mk_conj mlist
        in
    	  (SUBGOAL_THEN sgl STRIP_ASSUME_TAC THENL[
    	    REPEAT CONJ_TAC, ACCEPT_TAC th]) (asm,gl)
        end
     end
   end;


end;
