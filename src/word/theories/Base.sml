structure Base =
struct

local
 open numLib arithLib
 open rich_listTheory pairTheory arithmeticTheory prim_recTheory numTheory
 open HolKernel Parse basicHol90Lib Num_conv Num_induct
 infix THEN THENL |->;

in
val _ = Portable.output(Portable.std_out, "\nloading Base.\n");
val LESS_EQ_SPLIT =
    let val asm_thm = ASSUME (--`(m + n) <= p`--)
    in
    GEN_ALL(DISCH_ALL
     (CONJ(MP(SPECL [(--`n:num`--),(--`m+n`--),(--`p:num`--)] LESS_EQ_TRANS)
       	      (CONJ (SUBS [SPECL [(--`n:num`--),(--`m:num`--)] ADD_SYM]
                     (SPECL [(--`n:num`--),(--`m:num`--)] LESS_EQ_ADD))
                    asm_thm))
	  (MP (SPECL [(--`m:num`--),(--`m+n`--),(--`p:num`--)] LESS_EQ_TRANS)
               (CONJ (SPEC_ALL LESS_EQ_ADD) asm_thm))))
    end;


val SUB_GREATER_EQ_ADD =
  ARITH_PROVE (--`!p n m. (p >= n) ==> (((p - n) >= m) = (p >= (m + n)))`--);

(*ba bb wa wb *)
(* ADD_LESS_EQ_SUB = |- !p n m. n <= p ==> ((n + m) <= p = m <= (p - n)) *)
val ADD_LESS_EQ_SUB =
   GSYM (REWRITE_RULE[GREATER_EQ] SUB_GREATER_EQ_ADD);

(*wa *)
val ADD_LESS_EQ_TRANS =
  ARITH_PROVE (--`!m n p q. ((m + n) <= p) /\ (q <= n) ==> ((m + q) <= p)`--);

(**)
val ADD_SUB_LEM =
  ARITH_PROVE (--`!m n p. p < n ==> ((m + n) - p = m + (n - p))`--)

(*ba wa wb *)
val LESS_EQ_0_EQ = prove(
    (--`!m. m <= 0 ==> (m = 0)`--),
    INDUCT_TAC THEN REWRITE_TAC[NOT_SUC_LESS_EQ_0]);

(*wb *)
val PRE_LESS_REFL = prove((--`!m . (0 < m) ==> (PRE m < m)`--),
  INDUCT_THEN INDUCTION MP_TAC THEN
  REWRITE_TAC [LESS_REFL,LESS_0,PRE,LESS_SUC_REFL]);

(*ba bn *)
(* LESS_DIV_EQ_ZERO = |- !r n. r < n ==> (r DIV n = 0) *)
val LESS_DIV_EQ_ZERO = arithmeticTheory.LESS_DIV_EQ_ZERO;

(*bn *)
(* MULT_DIV = |- !n q. 0 < n ==> ((q * n) DIV n = q) *)
val MULT_DIV = arithmeticTheory.MULT_DIV;

(* ba bn *)
val ADD_DIV_ADD_DIV = arithmeticTheory.ADD_DIV_ADD_DIV;

(*bn *)
val NOT_MULT_LESS_0 = prove(
    (--`!m n. (0 < m) /\ (0 < n) ==> 0 < (m * n)`--),
    REPEAT INDUCT_TAC THEN REWRITE_TAC[NOT_LESS_0]
    THEN STRIP_TAC THEN REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES,LESS_0]);

(*bn *)
val MOD_MULT_MOD = arithmeticTheory.MOD_MULT_MOD;
val MULT_RIGHT_1 = arithmeticTheory.MULT_RIGHT_1;

(*ba bn *)
(* |- !q. q DIV (SUC 0) = q *)
val DIV_ONE = arithmeticTheory.DIV_ONE;

(*ba bn *)
val DIV_DIV_DIV_MULT = arithmeticTheory.DIV_DIV_DIV_MULT;

val Less_lemma = prove(
Term`!m n. m<n ==> ?p. (n = m + p) /\ 0<p`,
 GEN_TAC THEN INDUCT_TAC THENL[
  REWRITE_TAC[NOT_LESS_0],
  REWRITE_TAC[LESS_THM]
    THEN DISCH_THEN (DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL[
      EXISTS_TAC (--`SUC 0`--) 
    	THEN REWRITE_TAC[LESS_0,ADD_CLAUSES],
    	RES_TAC THEN EXISTS_TAC (--`SUC p`--)
    	THEN ASM_REWRITE_TAC[ADD_CLAUSES,LESS_0]]]);

(*-----------------------------------------------------------------------*)
(* Derived inference rules   	    					 *)
(*-----------------------------------------------------------------------*)

val MATCH_EQ_MP = fn eq => fn lh => EQ_MP (PART_MATCH lhs eq (concl lh)) lh;

val REWRITE1_TAC = fn t => REWRITE_TAC[t];

fun ARITH_TAC (asml,gl) =
    let val a = filter is_presburger asml in
    (MAP_EVERY (MP_TAC o ASSUME) a THEN CONV_TAC ARITH_CONV)(asml,gl)
    end;

(* ----------------------------------------------------------------------
 * Some simple list reasoning functions, in order to avoid loading in the
 * entire library of lists.
 *---------------------------------------------------------------------------*)

fun WORD_ERR{function,message} =
     HOL_ERR{origin_structure="Word library",
             origin_function = function,
             message = message};

open Rsyntax;

val % = Parse.Term
val alpha_ty = ==`:'a`==
val bool_ty = ==`:bool`==


(* --------------------------------------------------------------------*)
(*   LIST_INDUCT: (thm # thm) -> thm			               *)
(*							               *)
(*     A1 |- t[[]]      A2 |- !tl. t[tl] ==> !h. t[CONS h t]           *)
(* ----------------------------------------------------------          *)
(*                   A1 u A2 |- !l. t[l]			       *)
(*							               *)
(* --------------------------------------------------------------------*)

fun LIST_INDUCT (base,step) =
   let val {Bvar,Body} = dest_forall(concl step)
       val {ant,conseq} = dest_imp Body
       val {Bvar=h,Body=con} = dest_forall conseq
       val P  = %`\^Bvar.^ant`
       val b1 = genvar bool_ty
       val b2 = genvar bool_ty
       val base'  = EQ_MP (SYM(BETA_CONV (%`^P []`))) base
       val step'  = DISCH ant (SPEC h (UNDISCH(SPEC Bvar step)))
       val hypth  = SYM(RIGHT_BETA(REFL (%`^P ^Bvar`)))
       val concth = SYM(RIGHT_BETA(REFL (%`^P(CONS ^h ^Bvar)`)))
       val IND    = SPEC P (INST_TYPE [{redex=alpha_ty, residue = type_of h}]
                                      list_INDUCT)
       val th1 = SUBST[b1 |-> hypth, b2 |-> concth]
                      (%`^(concl step') = (^b1 ==> ^b2)`)
                      (REFL (concl step'))
       val th2 = GEN Bvar (DISCH (%`^P ^Bvar`)
                                 (GEN h(UNDISCH (EQ_MP th1 step'))))
       val th3 = SPEC Bvar (MP IND (CONJ base' th2))
   in
   GEN Bvar (EQ_MP (BETA_CONV(concl th3)) th3)
   end
   handle _ => raise WORD_ERR{function="LIST_INDUCT", message = ""};


(* --------------------------------------------------------------------*)
(*							               *)
(* LIST_INDUCT_TAC					               *)
(*							               *)
(*             [A] !l.t[l]				               *)
(*  ================================			               *)
(*   [A] t[[]],  [A,t[l]] !h. t[CONS h t]		               *)
(*							               *)
(* --------------------------------------------------------------------*)

val LIST_INDUCT_TAC  = INDUCT_THEN list_INDUCT ASSUME_TAC;

(* --------------------------------------------------------------------*)
(*                                                                     *)
(* SNOC_INDUCT_TAC                                                     *)
(*                                                                     *)
(*             [A] !l.t[l]                                             *)
(*  ================================                                   *)
(*   [A] t[[]],  [A,t[l]] !h. t[SNOC x t]                              *)
(*                                                                     *)
(* --------------------------------------------------------------------*)
(* PC 11/7/94 *)

val SNOC_INDUCT_TAC = INDUCT_THEN SNOC_INDUCT ASSUME_TAC;


(* --------------------------------------------------------------------*)
(* Definition by primitive recursion for lists		               *)
(* (For compatibility of new/old HOL.)			               *)
(* --------------------------------------------------------------------*)

local val list_Axiom = listTheory.list_Axiom
in
fun new_list_rec_definition (name,tm) =
  new_recursive_definition{name=name,rec_axiom=list_Axiom,def=tm,fixity=Prefix}

fun new_infixl_list_rec_definition (name,tm,prec) =
   new_recursive_definition {name=name,rec_axiom=list_Axiom,def=tm,
                             fixity=Infixl prec}
fun new_infixr_list_rec_definition (name,tm,prec) =
   new_recursive_definition {name=name,rec_axiom=list_Axiom,def=tm,
                             fixity=Infixr prec}
end;


(* ------------------------------------------------------------------------- *)
(* EQ_LENGTH_INDUCT_TAC : tactic                                             *)
(*  A ?- !l1 l2. (LENGTH l1 = LENGTH l2) ==> t[l1, l2]                       *)
(* ==================================================== EQ_LENGTH_INDUCT_TAC *)
(*  A                       ?- t[ []/l1, []/l2 ]                             *)
(*  A,LENGTH l1 = LENGTH l2 ?- t[(CONS h l1)/l1,(CONS h' l2)/l2]             *)
(* ------------------------------------------------------------------------- *)

val EQ_LENGTH_INDUCT_TAC =
 LIST_INDUCT_TAC THENL[
 LIST_INDUCT_TAC THENL[
   REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_THEN (K ALL_TAC),
   REWRITE_TAC[LENGTH,SUC_NOT]],
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH,NOT_SUC,INV_SUC_EQ]
   THEN GEN_TAC THEN REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_TAC];


(* ------------------------------------------------------------------------- *)
(* EQ_LENGTH_SNOC_INDUCT_TAC : tactic                                        *)
(* A ?- !l1 l2.(LENGTH l1 = LENGTH l2) ==> t[l1,l2]                          *)
(* =============================================== EQ_LENGTH_SNOC_INDUCT_TAC *)
(*  A                       ?- t[ []/l1, []/l2 ]                             *)
(*  A,LENGTH l1 = LENGTH l2 ?- t[(SNOC h l1)/l1,(SNOC h' l2)/l2]             *)
(* ------------------------------------------------------------------------- *)

val EQ_LENGTH_SNOC_INDUCT_TAC =
    SNOC_INDUCT_TAC THENL[
     SNOC_INDUCT_TAC THENL[
      REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_THEN (K ALL_TAC),
      REWRITE_TAC[LENGTH,LENGTH_SNOC,SUC_NOT]],
     GEN_TAC THEN SNOC_INDUCT_TAC
     THEN REWRITE_TAC[LENGTH,LENGTH_SNOC,NOT_SUC,INV_SUC_EQ]
     THEN GEN_TAC THEN REPEAT (CONV_TAC FORALL_IMP_CONV) THEN DISCH_TAC];

end (* local *)

val _ = Rewrite.add_implicit_rewrites pairTheory.pair_rws;

fun export_doc_theorems() = let
  open Theory Parse
  val thydir0 = Path.concat(Path.parentArc, Path.concat("help", "thms"))
  val _ = if FileSys.access(thydir0, []) then () else FileSys.mkDir thydir0
  val thydir = Path.concat(thydir0, current_theory())
  val _ = if FileSys.access(thydir, []) then () else FileSys.mkDir thydir
  val thms = theorems() @ axioms() @ definitions()
  fun write_thm (thname, thm) = let
    open TextIO
    val outstream = openOut (Path.concat(thydir, thname^".doc"))
  in
    output(outstream, "\\THEOREM "^thname^" "^current_theory()^"\n");
    output(outstream, thm_to_string thm);
    output(outstream, "\n\\ENDTHEOREM\n");
    closeOut outstream
  end
in
  app write_thm thms
end



end;
