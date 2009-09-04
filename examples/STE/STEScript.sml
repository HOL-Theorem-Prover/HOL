(* ===================================================================== *)
(* FILE          : STEScript.sml                                         *)
(* DESCRIPTION   : STE Embedding in HOL                                  *)
(* AUTHOR        : Ashish Darbari                                        *)
(* ===================================================================== *)
(*
(* For interactive running uncomment this part *)
   val _ = load "stringLib";
   val _ = load "mesonLib";
 *)

local
open boolLib Parse bossLib HolKernel;
open arithmeticTheory stringLib;
open listTheory mesonLib pairTheory;

in

(* Creating a new theory that will be called STE *)

val _ = new_theory "STE";

infix THEN THENL;

(* Creating abbreviations for FULL_SIMP_TAC and RW_TAC *)

val fs = FULL_SIMP_TAC std_ss;
val fl = FULL_SIMP_TAC list_ss;
val ARW_TAC = RW_TAC std_ss;

(* Dual Rail Encoding of Lattice Values *)

val Top_def  = Define `Top  = (F, F)`;
val One_def  = Define `One  = (T, F)`;
val Zero_def = Define `Zero = (F, T)`;
val X_def    = Define `X    = (T, T)`;

(* Definition of least upper bound *)
val _ = set_fixity "lub" (Infixl 510);
val lub_def = Define `(a, b) lub (c, d) = (a /\ c, b /\ d)`;


(* Definition of lub on states *)

val lub_state_def = Define `lub_state state1 state2 node =
			     (state1 node) lub (state2 node)`;

(* Defintion of ordering *)
 (*              ---
                |
                 ---
                 ---  *)

val _ = set_fixity "leq" (Infixl 510);
val leq_def = Define `(a leq b  = (b = a lub b))`;

(* Ordering lifted over states *)

val _ = set_fixity "leq_state" (Infixl 510);
val leq_state_def = Define `state1 leq_state state2
    = !node:string. (state1 node) leq (state2 node)`;

(* Ordering lifted over sequences *)

val _ = set_fixity "leq_seq" (Infixl 510);
val leq_seq_def = Define `sigma1 leq_seq sigma2
    = !node:string t:num. (sigma1 t node) leq (sigma2 t node)`;

(* Definition of suffix *)

val Suffix_def = Define
    `Suffix i (sigma: num->string->(bool # bool))
    = \t node.(sigma (t+i) node)`;


(* Dropping from Boolean to Lattice Values *)

val drop_def = Define `(drop T = One) /\ (drop F = Zero)`;

(* Drop operation lifted over states *)

val extended_drop_state_def = Define
    `extended_drop_state (s_b:string->bool) = \node. drop (s_b node)`;


(* Drop operation lifted over sequences *)

val extended_drop_seq_def = Define
    `extended_drop_seq (sigma_b:num->string->bool) = \t.
    (extended_drop_state (sigma_b t))`;

(* Next state function is monotonic *)

val Monotonic_def = Define `Monotonic Y_ckt =
    !s s'.
    s leq_state s' ==>
	(Y_ckt s) leq_state (Y_ckt s')`;


(* Sequence is in the STE language of a circuit  *)

val in_STE_lang_def = Define `
    in_STE_lang sigma Y_ckt =
    !t. (Y_ckt (sigma t)) leq_state (sigma (t+1))`;


(* Defining the abstract type of Trajectory formulas *)

val _ = Hol_datatype
    `TF = Is_0 of string
  | Is_1 of string
  | AND of TF => TF
  | WHEN of TF => bool
  | NEXT of TF`;

(* Defining the operators WHEN and AND to be left infix *)

val _ = set_fixity "WHEN" (Infixl 500);
val _ = set_fixity "AND" (Infixl 510);

(* Semantics of trajectory formula - defined wrt a sequence *)

val SAT_STE_def = Define `(SAT_STE (Is_0 n) = \sigma.
			   Zero leq (sigma 0 n))

    /\ (SAT_STE (Is_1 n) = \sigma.
	One leq (sigma 0 n))

    /\ (SAT_STE (tf1 AND tf2) = \sigma.
	((SAT_STE tf1 sigma) /\ (SAT_STE tf2 sigma)))

    /\ (SAT_STE (tf WHEN (P:bool)) = \sigma.
	(P ==> (SAT_STE tf sigma)))

    /\ (SAT_STE (NEXT tf) = \sigma.
	(SAT_STE tf (Suffix 1 sigma)))`;

(* Datatype of Assertions - leadsto operator *)

val _ = Hol_datatype `Assertion = ==>> of TF => TF`;

(* leadsto is infix *)

val _ = set_fixity "==>>" (Infixl 470);


(* Defining Sequence of a trajectory formula *)

val DefSeq_def = Define `(DefSeq (Is_0 m) = \t n.
			  (if ((n = m) /\ (t = 0)) then Zero else X))

    /\ (DefSeq (Is_1 m) = \t n.
	(if ((n = m) /\ (t = 0)) then One else X))

    /\ (DefSeq (tf1 AND tf2) = \t n.
	((DefSeq tf1 t n) lub (DefSeq tf2 t n)))

    /\ (DefSeq (tf WHEN (P:bool)) = \t n.
	(P ==> FST(DefSeq tf t n),  P ==> SND(DefSeq tf t n)))

    /\ (DefSeq (NEXT tf) = \t n.
	(if ~(t = 0) then (DefSeq tf (t-1) n) else X))`;


(* Collecting the nodes in the trajectory formula *)

val Nodes_def = Define `(Nodes (Is_0 n) Acc =
			    if MEM n Acc then Acc else (n::Acc))
    /\ (Nodes (Is_1 n) Acc = if MEM n Acc then Acc else (n::Acc))
    /\ (Nodes (tf1 AND tf2) Acc =  Nodes tf2 (Nodes tf1 Acc))
    /\ (Nodes (tf WHEN P) Acc = Nodes tf Acc)
    /\ (Nodes (NEXT tf) Acc = Nodes tf Acc)`;


(* Useful properties about node membership *)

val MEM_NODES1 = store_thm("MEM_NODES1",``!tf acc node.
         MEM node (Nodes tf []) \/ MEM node acc =
         MEM node (Nodes tf acc)``,
			      Induct THEN
			      fl [Nodes_def]
			      THEN REPEAT STRIP_TAC
			      THEN REPEAT COND_CASES_TAC
			      THEN fl [] THEN PROVE_TAC []);



val MEM_NODES2 = store_thm("MEM_NODES2", ``!tf tf'.
			      ~MEM node (Nodes tf' (Nodes tf [])) =
			      ~MEM node (Nodes tf [])
			      /\ ~MEM node (Nodes tf' [])``,
			      PROVE_TAC [MEM_NODES1]);


val MAX_def = Define `MAX t1 t2 = (if t1 >= t2 then t1 else t2)`;;

(* Depth of a trajectory formula *)

val Depth_def = Define `(Depth (Is_0 n) = 0)
    /\ (Depth (Is_1 n) = 0)
    /\ (Depth (tf1 AND tf2) = MAX (Depth tf1)(Depth tf2))
    /\ (Depth (tf WHEN P) = Depth tf)
    /\ (Depth (NEXT tf) = SUC (Depth tf))`;


(* Defining Trajectory *)

val DefTraj_def = Define `(DefTraj tf Model 0 node = DefSeq tf 0 node)
    /\ (DefTraj tf Model (SUC t) node
	= (DefSeq tf (SUC t) node) lub (Model (DefTraj tf Model t) node))`;

(* The STE implementation *)

val STE_Impl_def = Define `STE_Impl (Ant ==>> Cons) Y_ckt =
    !t. (t <= Depth Cons ==>
	 !n. MEM n
	 (APPEND(Nodes Ant [])(Nodes Cons [])) ==>
	     (DefSeq Cons t n) leq (DefTraj Ant Y_ckt t n))`;

(* Satisfiability of a Trajectory Assertion *)

val SAT_CKT_def = Define `SAT_CKT (Ant ==>> Cons) Y_ckt
    = !sigma. (in_STE_lang sigma Y_ckt )
    ==>  (SAT_STE Ant sigma)
    ==> (SAT_STE Cons sigma)`;

(* Boolean valued world starts here *)

(* Definition of suffix of a Boolean valued sequence *)

val Suffix_b_def = Define
    `Suffix_b i (sigma_b:num->string->bool)
    = \t node.(sigma_b (t+i) node)`;

(* Boolean Valued Sequence is in the relational model of a circuit  *)

val in_BOOL_lang_def = Define `
    in_BOOL_lang (sigma_b:num->string->bool) Yb_ckt
    = !t. Yb_ckt (sigma_b t) (sigma_b (t+1))`;

(* Boolean sequence satisfies a trajectory formula *)

val SAT_BOOL_def = Define `(SAT_BOOL (Is_0 n) = \sigma_b.
			    ((sigma_b 0 n) = F))

    /\ (SAT_BOOL (Is_1 n)  = \sigma_b.
	((sigma_b 0 n) = T))

    /\ (SAT_BOOL (tf1 AND tf2)  = \sigma_b.
	(SAT_BOOL tf1 sigma_b) /\ (SAT_BOOL tf2 sigma_b))

    /\ (SAT_BOOL (tf WHEN (P:bool))  = \sigma_b.
	(P ==> (SAT_BOOL tf  sigma_b)))

    /\ (SAT_BOOL (NEXT(tf))  =  \sigma_b.
	(SAT_BOOL tf (Suffix_b 1 sigma_b)))`;



(* Linking the lattice and the Boolean Models *)

val Okay_def = Define `Okay (Y_ckt, Yb_ckt) =
    !s_b:string->bool s_b':string->bool.
    (Yb_ckt s_b s_b') ==> ((Y_ckt (extended_drop_state s_b)) leq_state
			 (extended_drop_state s_b'))`;

 (* Lemmas and Theorems *)


(* Here is the Big Picture *)
(*
-----------Top Level Picture : BridgeTheorem ---------------------------------

	A ==>> C Y  Yb
	   |     |   |
	   |     |   |
	  \|/   \|/ \|/
	   |     |   |
	   |     |   |
   --STE---------------------------
  |				   |
  | - its Okay to relate Y and Yb  |	    --- BOOLEAN ----
  | - Y is Monotonic		   |  ---> |                |
  |	                           |       | Theorem in HOL |
  | - run STE simulator to see if  |       |                |
  |	                           |        ----------------
  | - Y satisfies A ==>> C	   |
  |				   |
    -------------------------------

BridgeTheorem:
|- !Ant Cons Y_ckt Yb_ckt.
	       Okay (Y_ckt, Yb_ckt) ==>
		   Monotonic Y_ckt
		   ==>
		   (

		    (!t.
		     t <= Depth Cons ==>
			 !n.
			 MEM n (Nodes Ant APPEND Nodes Cons) ==>
			     leq (DefSeq Cons t n) (DefTraj Ant Y_ckt t n))

		    ==>
		    (
		     !sigma_b.
		     in_BOOL_lang sigma_b Yb_ckt ==>
			 !t.
			 SAT_BOOL Ant (Suffix_b t sigma_b) ==>
			     SAT_BOOL Cons (Suffix_b t sigma_b))
		    ) : thm

Proof of BridgeTheorem:

			Relies on proving SAT_CKT_IFF_STE_IMPL and Theorem2
------------------------------------------------------------------------------


---------------SAT_CKT_IFF_STE_IMPL--------------------------------------------


	A ==>> C Y
	   |     |
	   |     |
	  \|/   \|/
	   |     |
	   |     |
  -----------------------------------
 |				     |
 | If Y is monotonic then	     |
 | the jth suffix of the lattice     |
 | valued sequence satisfies the     |
 | STE assertion if and only if	     |
 | the STE implementation (STE_Impl) |
 | does.			     |
  -----------------------------------

STE_Impl is defined as:

|- !Ant Cons Y_ckt.
         STE_Impl (Ant ==>> Cons) Y_ckt =
         !t.
           t <= Depth Cons ==>
           !n.
             MEM n (Nodes Ant APPEND Nodes Cons) ==>
             leq (DefSeq Cons t n) (DefTraj Ant Y_ckt t n) : thm

SAT_CKT_IFF_STE_IMPL:

 |- !Ant Cons Y_ckt.
         Monotonic Y_ckt ==>
         ((!sigma.
             in_STE_lang sigma Y_ckt ==>
             !j.
               SAT_STE Ant (Suffix j sigma) ==>
               SAT_STE Cons (Suffix j sigma)) =
          !t.
            t <= Depth Cons ==>
            !n.
              MEM n (Nodes Ant APPEND Nodes Cons) ==>
              leq (DefSeq Cons t n) (DefTraj Ant Y_ckt t n)) : thm


Proof of SAT_CKT_IFF_STE_IMPL:
			Relies on SAT_CKT_IFF_TIME_SHIFT theorem and
			AuxTheorem1 (relies on Y being monotonic)

------------------------------------------------------------------------------

-------------------Theorem2---------------------------------------------------


	 ----------------------------------
	| If its Okay to relate Y and Yb,  |
        | and Y is monotonic               |
	| then if the lattice sequence	   |
	| which is in the langauge of Y    |
	| satisfies the STE assertion,     |
	| the Boolean sequence which is	   |
	| in the language of Yb also	   |
	| satisfies the same STE assertion |
         ---------------------------------


Theorem2:

|- !Ant Cons Y_ckt Yb_ckt.
         Okay (Y_ckt,Yb_ckt)
	 ==>
         (!sigma.
            in_STE_lang sigma Y_ckt ==>
            !t.
              SAT_STE Ant (Suffix t sigma) ==>
              SAT_STE Cons (Suffix t sigma)) ==>
         !sigma_b.
           in_BOOL_lang sigma_b Yb_ckt ==>
           !t.
             SAT_BOOL Ant (Suffix_b t sigma_b) ==>
             SAT_BOOL Cons (Suffix_b t sigma_b) : thm

Proof of Theorem2:
		  Relies on Lemma1, Lemma2 and Suffix_Lemma

------------------------------------------------------------------------------

*)


(* If its Okay to relate Y and Yb then for all Boolean valued
   sequences which are in the language of the Boolean Model Yb,
   the drop of the Boolean valued sequence is in the language
   of the lattice model Y.

  Lemma1 is used in the proof of Theorem2

*)

val Lemma1 =
    store_thm ("Lemma1",
	       ``!Y_ckt Yb_ckt. Okay (Y_ckt, Yb_ckt)
	       ==> !sigma_b.
	       in_BOOL_lang sigma_b Yb_ckt
	       ==>  in_STE_lang (extended_drop_seq sigma_b) Y_ckt``,
	       STRIP_TAC THEN fs [Okay_def, in_BOOL_lang_def,
				  in_STE_lang_def,
				  extended_drop_seq_def]);

(* Calculating the Suffix after calculating the
   drop of the Boolean valued sequence, results
   in the sequence that one obtains by first calculating
   the Suffix of the Boolean valued sequence and then
   dropping it

   Suffix_Lemma is used in the proof of Theorem2

*)
val Suffix_Lemma = TAC_PROOF(([], ``!t sigma_b.
   (Suffix t (extended_drop_seq sigma_b)) =
   (extended_drop_seq (Suffix_b t sigma_b))``),

			      (REPEAT STRIP_TAC
			       THEN Induct_on `t`
			       THEN fs [Suffix_def, Suffix_b_def,
					extended_drop_seq_def,
					extended_drop_state_def, drop_def])
			      );


(* Lemma2_1 is used in the proof of Lemma 2 *)

val Lemma2_1 = prove (``!tf sigma_b. SAT_BOOL tf sigma_b
		      ==> SAT_STE tf (extended_drop_seq sigma_b)``,

		      STRIP_TAC
		      THEN Induct_on `tf`
		      THEN fs [SAT_BOOL_def, SAT_STE_def]
		      THEN fs [extended_drop_seq_def,
			       extended_drop_state_def,
			       drop_def, leq_def, Zero_def,
			       lub_def]
		      THEN fs [extended_drop_seq_def,
			       extended_drop_state_def,
			       drop_def, leq_def, One_def, lub_def]
		      THEN fs [Suffix_def, Suffix_b_def,
			       extended_drop_seq_def,
			       extended_drop_state_def]

		      );


(* Lemma2_2 is used in the proof of Lemma 2 *)

val Lemma2_2 = prove (``!tf sigma_b. SAT_STE tf (extended_drop_seq sigma_b)
		      ==> SAT_BOOL tf sigma_b``,

		      STRIP_TAC THEN Induct_on `tf`
		      THEN fs [SAT_STE_def, SAT_BOOL_def,
			       extended_drop_seq_def,
			       extended_drop_state_def, drop_def]
		      THEN REPEAT STRIP_TAC
		      THEN fs [Zero_def, One_def, drop_def, leq_def, lub_def]


		      THEN fs [SAT_STE_def, SAT_BOOL_def,
			       extended_drop_seq_def,
			       extended_drop_state_def, drop_def]
		      THEN REPEAT STRIP_TAC
		      THEN fs [Zero_def, One_def, drop_def,
			       leq_def, lub_def]
		      THEN Induct_on `sigma_b 0 s = T`
		      THEN fs [drop_def, lub_def, Zero_def, One_def]
		      THEN fs [SAT_STE_def, SAT_BOOL_def,
			       extended_drop_seq_def, extended_drop_state_def,
			       Suffix_def, Suffix_b_def]
		      );

(* Trajectory formula is satisfiable by a Boolean valued sequence
   if and only if the trajectory formula is satisfiable by the
   drop of the Boolean valued sequence

*)

val Lemma2 = prove (``!tf sigma_b. SAT_BOOL tf sigma_b =
		    SAT_STE tf (extended_drop_seq sigma_b)``,

		    REPEAT STRIP_TAC THEN EQ_TAC
		    THEN fs [Lemma2_1, Lemma2_2]);


(* Properties of drop operation
   An interesting property though these lemmas are not used anywhere
*)


val Lemma3_1 = prove(``!sigma_b:num->string->bool.
		      (sigma_b 0 node = F)
		      = (Zero leq ((extended_drop_seq sigma_b) 0 node))``,

		      STRIP_TAC THEN EQ_TAC
		      THEN fs [extended_drop_seq_def, extended_drop_state_def,
			       drop_def, leq_def, lub_def]
		      THEN fs [lub_def, Zero_def]
		      THEN fs [extended_drop_seq_def, extended_drop_state_def,
			       drop_def, leq_def, lub_def]
		      THEN STRIP_TAC
		      THEN Induct_on `sigma_b 0 node = T`
		      THEN fs [drop_def, lub_def, Zero_def, One_def]
		      THEN fs [drop_def, lub_def, Zero_def, One_def]);


val Lemma3_2 = prove(``!sigma_b:num->string->bool. (sigma_b 0 node = T)
		     = (One leq ((extended_drop_seq sigma_b) 0 node))``,

		     STRIP_TAC THEN EQ_TAC
		     THEN fs [extended_drop_seq_def, extended_drop_state_def,
			      drop_def, leq_def, lub_def]
		     THEN fs [lub_def, Zero_def]
		     THEN fs [extended_drop_seq_def, extended_drop_state_def,
			      drop_def, leq_def, lub_def]
		     THEN STRIP_TAC
		     THEN Induct_on `sigma_b 0 node = T`
		     THEN fs [drop_def, lub_def, Zero_def, One_def]
		     THEN fs [drop_def, lub_def, Zero_def, One_def]);

(* lattice_X1_lemma and lattice_X2_lemma state the same thing -
   that the lub of any lattice value and X is that lattice value.
   We have two versions they get used as and when they are needed
   in the proofs of other lemmas

   Used in the proof of DEFSEQ_LE_THAN_SAT_STE1 and AuxTheorem1

*)

val lattice_X1_lemma = store_thm ("lattice_X1_lemma",
				  ``!elem. elem = X lub elem``,
				  STRIP_TAC THEN Cases_on `elem`
				  THEN fs [lub_def, X_def]);

val lattice_X2_lemma = TAC_PROOF(([], ``!elem. elem = (T, T) lub elem``),
				STRIP_TAC THEN Cases_on `elem`
				 THEN fs [lub_def]);

(* If a number is not zero, it must be either equal to 1 or greater than 1

   Used in the proof of DEFSEQ_LE_THAN_SAT_STE1
*)


val NUM_LEMMA = TAC_PROOF(([], ``!t. ~(t = 0) ==> 1 <= t``),
			  Induct THEN DECIDE_TAC
			  );

(* Transitivity Lemma
  Used in the proof of SEQ_LESS_THAN_SAT_STE and
  DEFTRAJ_LESSTHAN_SEQ_IMP_SAT_STE_2

*)
val TRANS_LEMMA =
    TAC_PROOF(([],  ``!a c. (?b. a leq b /\ b leq c) ==> a leq c``),
        REPEAT Cases THEN STRIP_TAC THEN Cases_on `b` THEN
        fs [leq_def, lub_def] THEN PROVE_TAC[]);;



(* A rather obvious but useful lemma that the 0th suffix of the sequence
   gives the sequence itself *)

val SUFFIX_0 = store_thm("SUFFIX_0", ``!sigma. Suffix 0 sigma = sigma``,
			  GEN_TAC THEN fs [Suffix_def]
			  THEN CONV_TAC(FUN_EQ_CONV)
			  THEN GEN_TAC
			  THEN Induct_on `n` THEN fs []
			  THEN (CONV_TAC(FUN_EQ_CONV))
			  THEN fs [] THEN (FULL_SIMP_TAC arith_ss [])
			  THEN (CONV_TAC(FUN_EQ_CONV)) THEN fs []);

(* Suffix Closure Axiom: If a sequence is in the language of a lattice
   circuit model then every suffix of that sequence is in the language
   of the circuit model

   Used in the proof of SEQ_LESS_THAN_SAT_STE
*)

(* Suffix closed -- Proposition *)
val Proposition =
    store_thm("Proposition",
	      ``!Y_ckt sigma. in_STE_lang sigma Y_ckt
	      ==> !t. in_STE_lang (Suffix t sigma) Y_ckt``,
	      STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC
	      THEN Induct THENL [PROVE_TAC [SUFFIX_0],
				 fs [in_STE_lang_def, Suffix_def]
				 THEN fl [leq_state_def,
					  leq_def]
				 THEN REPEAT STRIP_TAC
				 THEN FIRST_ASSUM
				 (STRIP_ASSUME_TAC
				  o SPECL [``t'+1``,
					   ``node:string``])
				 THEN
				 FULL_SIMP_TAC bool_ss
				 [ONE, ADD_CLAUSES]
				 THEN RW_TAC std_ss [ADD_COMM]
				 THEN PROVE_TAC []]);




(* Following up from Proposition above, clearly the first suffix is
   in the language of the circuit model - useful to have this in the proofs

   Used in the proof of DEFSEQ_LE_THAN_SAT_STE1, DEFSEQ_LE_THAN_SAT_STE2
   and DEFSEQ_LE_THAN_SAT_STE

 *)


val Proposition1 =  store_thm("Proposition1",
			      ``!Y_ckt sigma. in_STE_lang sigma Y_ckt
			      ==> !t. in_STE_lang (Suffix 1 sigma) Y_ckt``,
			      PROVE_TAC [Proposition]);


(* If a sequence sigma is less than or equal to another sequence sigma'
   then the ith suffix of sigma is less than or equal to the ith suffix
   of sigma' *)

val SUFFIX_SEQ_LESSTHAN = TAC_PROOF(([], ``!sigma sigma' i.
			(!t n. (sigma t n) leq (sigma' t n))
			==> !t n. ((Suffix i sigma) t n )
			leq ((Suffix i sigma') t n)``),
		       REPEAT STRIP_TAC
		       THEN (Induct_on `t`)
		       THEN (Induct_on `i`)
		       THEN fs [Suffix_def, leq_def]
		       THEN PROVE_TAC []
		       THEN fs [Suffix_def, leq_def]
		       THEN PROVE_TAC []
		       );

(* Lemmas about lub operation. Useful in other proofs *)

val LUB_LEMMA1 = TAC_PROOF(([], ``!a. a = a lub a``),
			   REPEAT STRIP_TAC
			   THEN Cases_on `a`
			   THEN fs [lub_def]);

val LUB_LEMMA2 = TAC_PROOF(([], ``!a b. a leq (a lub b)``),
			   (REPEAT Cases
			    THEN fs [leq_def, lub_def] THEN PROVE_TAC [])
			   );

val LUB_LEMMA3 = TAC_PROOF(([], ``!a b. a leq (b lub a)``),
			   (REPEAT Cases
			    THEN fs [leq_def, lub_def] THEN PROVE_TAC [])
			   );

val LUB_LEMMA4 = TAC_PROOF(([], ``!a b c.
		   a leq c ==> b leq c ==> (a lub b) leq c``),
		  (REPEAT Cases
		   THEN fs [leq_def, lub_def]
		   THEN PROVE_TAC []));

val LUB_LEMMA4a = TAC_PROOF(([], ``!a b c.
		   (a leq c /\ b leq c) ==> (a lub b) leq c``),
		  (REPEAT Cases
		   THEN fs [leq_def, lub_def]
		   THEN PROVE_TAC []));

val LUB_LEMMA5 = TAC_PROOF(([], ``!a b c. b leq c ==>
			    (a lub b) leq (a lub c)``),
			   REPEAT Cases THEN fs [leq_def, lub_def]
			   THEN PROVE_TAC []
			   );

val LUB_LEMMA6 = TAC_PROOF (([], ``!a b c. (c = a lub b)
			     = (c = (FST a,SND a) lub b)``),
			    (REPEAT Cases THEN fs [FST, SND,
						   lub_def]));

val LUB_LEMMA7a = TAC_PROOF(([],
			   ``!a b c. (a lub b) leq c ==> a leq c``),
			  REPEAT Cases THEN fs [leq_def, lub_def]
			  THEN PROVE_TAC []
			  );

val LUB_LEMMA7b = TAC_PROOF(([],
			   ``!a b c. (a lub b) leq c ==> b leq c``),
			  REPEAT Cases THEN fs [leq_def, lub_def]
			  THEN PROVE_TAC []
			  );

val LUB_LEMMA8 = TAC_PROOF(([], ``!a b. a lub b = b lub a``),
			   REPEAT Cases THEN fs [lub_def] THEN PROVE_TAC []);




(* Defining Sequence for a given trajectory formula is less than or equal to
   the defining trajectory for the formula at time point 0 - used in the proof
   for any time t later *)

val LEQ_DEFSEQ_DEFTRAJ_BASE = TAC_PROOF(([], ``!tf Y_ckt.
					 (DefSeq tf 0) leq_state
					 (DefTraj tf Y_ckt 0)``),
					(REPEAT STRIP_TAC
					 THEN fs [leq_state_def, DefTraj_def]
					 THEN STRIP_TAC
					 THEN PROVE_TAC [leq_def,
							 LUB_LEMMA1])
					);

(* Defining Sequence for a given trajectory formula is less than or equal
  to the defining trajectory for the same formula for a given circuit model

  Used in the proof of SAT_CKT_IFF_STE1
*)

val LEQ_DEFSEQ_DEFTRAJ = TAC_PROOF(([], ``!tf Y_ckt t.
                                           (DefSeq tf t) leq_state
					   (DefTraj tf Y_ckt t)``),
				   REPEAT STRIP_TAC THEN Induct_on `t`
				   THEN fs [LEQ_DEFSEQ_DEFTRAJ_BASE]
				   THEN fs [leq_state_def] THEN STRIP_TAC
				   THEN fs [DefTraj_def] THEN fs [LUB_LEMMA2]
				   );



(* If the circuit is monotonic then the defining trajectory for a given
   trajectory formula wrt a given circuit model is in the langage of that
   circuit model

   Used in the proof of DEFTRAJ_LESSTHAN_SEQ_IMP_SAT_STE_1,
   SAT_CKT_IFF_STE1, SAT_CKT_IFF_STE2 *)

(* val DEFTRAJ_IN_STE_LANG = TAC_PROOF(([], ``!tf Y_ckt. Monotonic Y_ckt ==> *)
(* 				     in_STE_lang (DefTraj tf Y_ckt) Y_ckt``),  *)

(* 				    (REPEAT STRIP_TAC THEN fs  *)
(* 				     [in_STE_lang_def]) *)
(* 				    THEN (GEN_TAC THEN Induct_on `t`) *)
(* 				    THENL[ *)
(* 					  ((fs [DefTraj_def, leq_state_def]) *)
(* 					   THEN (GEN_TAC THEN fs [DefTraj_def]) *)
(* 					   THEN (fs [DefTraj_def, ONE]) *)
(* 					   THEN (fs [LUB_LEMMA3])), *)
(* 					  ((fs [leq_state_def]) *)
(* 					   THEN (GEN_TAC) *)
(* 					   THEN (fs [ONE, ADD, DefTraj_def]) *)
(* 					   THEN (fs [ADD_SYM, ADD]) *)
(* 					   THEN (fs [LUB_LEMMA3]))] *)
(* 				    ); *)

val DEFTRAJ_IN_STE_LANG = TAC_PROOF(([], ``!tf Y_ckt. Monotonic Y_ckt
				     ==>
				     in_STE_lang (DefTraj tf Y_ckt)
				     Y_ckt``),
				    (REPEAT STRIP_TAC THEN fs
				     [in_STE_lang_def])
				    THEN REWRITE_TAC [GSYM ADD1]
				    THEN Induct
				    THENL[
					  ((fs [DefTraj_def,
						leq_state_def])
					   THEN (GEN_TAC THEN fs
						 [DefTraj_def])
					   THEN (fs [DefTraj_def])
					   THEN (fs [LUB_LEMMA3])),
					  ((fs [leq_state_def])
					   THEN (GEN_TAC)
					   THEN (fs [ADD, DefTraj_def])
					   THEN (fs [ADD_SYM, ADD])
					   THEN (fs [LUB_LEMMA3]))]
				    );


(* If the circuit is monotonic and if two given sequences sigma and sigma'
   are in the language of the circuit and if sigma is less than or equal
   to sigma' then if sigma satisfies a trajectory formula then so does sigma'
   *)

val SEQ_LESS_THAN_SAT_STE = TAC_PROOF (([], ``!Y_ckt tf. !sigma sigma'.
					Monotonic Y_ckt ==>
					(in_STE_lang sigma Y_ckt) ==>
					    (in_STE_lang sigma' Y_ckt)
					    ==> (!t n.
						 (sigma t n) leq (sigma' t n))
					    ==>  (SAT_STE tf sigma ==>
						  SAT_STE tf sigma')``),
				       (GEN_TAC THEN Induct_on `tf`
					THEN fs [SAT_STE_def]
					THEN REPEAT STRIP_TAC THENL
					[PROVE_TAC [TRANS_LEMMA],
					 PROVE_TAC [TRANS_LEMMA],
					 PROVE_TAC [TRANS_LEMMA],
					 PROVE_TAC [TRANS_LEMMA],
					 PROVE_TAC [TRANS_LEMMA],
					 ALL_TAC]
					THEN
					(STRIP_ASSUME_TAC Proposition
					 THEN RES_TAC) THEN
					fs [SUFFIX_SEQ_LESSTHAN]
					THEN
					IMP_RES_TAC
					(SPECL[``sigma:num->string->bool#bool``
					       , ``sigma':num->string->
					       bool#bool``, ``1``]
					 SUFFIX_SEQ_LESSTHAN)
					THEN
					FIRST_ASSUM (STRIP_ASSUME_TAC o
						     SPECL[``(Suffix 1

							      (sigma:num->
							       string->
							       bool#bool))``,
							   ``Suffix 1
							   (sigma':num->
							    string->
							    bool#bool)``])
					THEN fs []));


(* Specialized versions of LUB_LEMMA - useful in different proofs  *)

val SPEC_LUB_LEMMA1 = TAC_PROOF(([], ``!tf tf'.
				(!t n.
				 ((DefSeq tf t n) lub (DefSeq tf' t n))
				 leq  (sigma t n)) ==>
				!t n. (DefSeq tf t n) leq (sigma t n)``),

			       REPEAT STRIP_TAC THEN
			       Induct_on `t`
			       THENL[((FIRST_ASSUM(STRIP_ASSUME_TAC o
						  SPECL [``0:num``,
							 ``n:string``]))
				     THEN
				     (IMP_RES_TAC LUB_LEMMA7a)),
				    ((FIRST_ASSUM(STRIP_ASSUME_TAC o
						  SPECL [``SUC(t:num)``,
							 ``n:string``]))
				     THEN (IMP_RES_TAC LUB_LEMMA7a))]
				);

val SPEC_LUB_LEMMA2 = TAC_PROOF(([], ``!tf tf'.
				 (!t n. ((DefSeq tf t n) lub
					 (DefSeq tf' t n)) leq (sigma t n)) ==>
				!t n. (DefSeq tf' t n) leq (sigma t n)``),

			       REPEAT STRIP_TAC THEN
			       Induct_on `t`
			       THENL[((FIRST_ASSUM(STRIP_ASSUME_TAC o
						  SPECL [``0:num``,
							 ``n:string``]))
				     THEN
				     (IMP_RES_TAC LUB_LEMMA7b)),
				    ((FIRST_ASSUM(STRIP_ASSUME_TAC o
						  SPECL [``SUC(t:num)``,
							 ``n:string``]))
				     THEN (IMP_RES_TAC LUB_LEMMA7b))]
				);


(* For all time points greater than zero, if DefSeq tf (t - 1) n returns a
 value less than or equal to the lattice value returned by sigma, then the
 DefSeq tf t n returns a value less than the first suffix of the sequence
 sigma
 *)

val SPEC_NEXT_LEMMA = TAC_PROOF(([], ``!tf.(!t n. (if ~(t=0)
						      then
							  DefSeq tf (t -1) n
						   else X) leq (sigma t n))
				 ==> (!t n. (DefSeq tf t n) leq
				      (Suffix 1 sigma t n))``),
				Induct THEN
				REPEAT STRIP_TAC
				THEN fl [DefSeq_def, Suffix_def] THEN
				FIRST_ASSUM(STRIP_ASSUME_TAC o
					    SPECL [``SUC t``, ``n:string``])
				THEN fl []
				THEN RW_TAC std_ss [SYM(SPEC_ALL ADD1)]
				THEN fl [leq_def, lattice_X1_lemma]
				THEN fl [lattice_X1_lemma]
				THEN fl [ADD_CLAUSES, SUC_ONE_ADD]
				THEN fl []
				);


(* If a lattice sequence sigma is in the language of a circuit model then
   if sigma satisfies a given trajectory formula then the
   Defining Sequence of the trajectory formula is less than or equal
   to sigma *)

val DEFSEQ_LE_THAN_SAT_STE1 =
    TAC_PROOF(([],  ``!tf. !sigma. in_STE_lang sigma Y_ckt ==>
	       (SAT_STE tf sigma ==>
		   !t. !n. (DefSeq tf t n) leq
		   (sigma t n)) ``),

	      GEN_TAC THEN Induct_on `tf`
	      THEN fs [SAT_STE_def, DefSeq_def]
	      THEN REPEAT STRIP_TAC
	      THENL
	      [(COND_CASES_TAC THEN fs [leq_def,
					lub_def,
					Zero_def]
		THEN PROVE_TAC
		[lattice_X1_lemma]),
	       (COND_CASES_TAC THEN fs [leq_def,
					lub_def,
					One_def]
		THEN PROVE_TAC
		[lattice_X1_lemma]),
	       (fs [LUB_LEMMA4]),
	       ((Cases_on `b`) THEN
		(PROVE_TAC [lattice_X2_lemma,
			    leq_def, LUB_LEMMA6])
		THEN (PROVE_TAC [lattice_X2_lemma,
				 leq_def,
				 LUB_LEMMA6])),
	       ((COND_CASES_TAC) THEN (IMP_RES_TAC
				       Proposition1)
		THEN (RES_TAC) THEN (fs [Suffix_def])
		THEN (FIRST_ASSUM(STRIP_ASSUME_TAC o
				  (SPECL [
					  ``
					  (t:num)-1``
					  ,
					  ``n:string
					  ``])))
		THEN (IMP_RES_TAC NUM_LEMMA)
		THEN (fs [SUB_ADD])
		THEN (PROVE_TAC [leq_def,
				 lattice_X1_lemma])
		)
	       ]
	      );



(* If a lattice sequence sigma is in the language of a circuit model then
   if the Defining Sequence of a given trajectory formula is is less than
   or equal to sigma then sigma satisfies the trajectory formula

   We have stated this theorem in two ways. One is defined on states using
   leq_state and the later one is defined on lattice values using leq
*)

val DEFSEQ_LE_THAN_SAT_STE =
    TAC_PROOF (([], ``!tf. !sigma.
		in_STE_lang sigma Y_ckt ==>
		    ((!t. (DefSeq tf t) leq_state (sigma t))
		     ==> SAT_STE tf sigma)``),
      Induct
	       THEN fs [leq_state_def, SAT_STE_def, DefSeq_def]
	       THEN REPEAT STRIP_TAC
	      THENL [FIRST_ASSUM(STRIP_ASSUME_TAC o
				SPECL [``0``,  ``s:string``])
		    THEN fs [],
		     FIRST_ASSUM(STRIP_ASSUME_TAC o
				 SPECL [``0``,  ``s:string``])
		     THEN fs [],
		     IMP_RES_TAC LUB_LEMMA7a
		     THEN  RES_TAC
		     THEN  (IMP_RES_TAC
			    (SPEC_ALL
			     (SPEC_LUB_LEMMA1)))
		     THEN RES_TAC, ((IMP_RES_TAC LUB_LEMMA7b)
		     THEN  RES_TAC
		     THEN  (IMP_RES_TAC
			    (SPEC_ALL
			     (SPEC_LUB_LEMMA2)))
		     THEN RES_TAC),
		     (IMP_RES_TAC Proposition1
		      THEN RES_TAC
		      THEN (FIRST_ASSUM
			    (STRIP_ASSUME_TAC o
			     SPECL[``(SUC(t:num))``,
				   ``n:string``]))
		      THEN fs [NOT_EQ_SYM
			       (SPEC_ALL SUC_NOT)]
		      THEN  fs [SUC_SUB1]
		      THEN  (IMP_RES_TAC
			     SPEC_NEXT_LEMMA)
		      THEN (FIRST_ASSUM
			    (STRIP_ASSUME_TAC o
			     SPEC ``(Suffix 1
				     (sigma:num->
				      string->
				      bool#bool))``))
		      THEN RES_TAC)]
	       );


(* If a lattice sequence sigma is in the language of a circuit model then
   if the Defining Sequence of a given trajectory formula is is less than
   or equal to sigma then sigma satisfies the trajectory formula

   This is the one defined on lattice values using leq
  *)


val DEFSEQ_LE_THAN_SAT_STE2 =
    TAC_PROOF(([], ``!tf. !sigma.
	       in_STE_lang sigma Y_ckt ==>
		   ((!t. !n. (DefSeq tf t n) leq
		     (sigma t n))
		    ==> SAT_STE tf sigma)``),
	      Induct
	       THEN fs [SAT_STE_def, DefSeq_def]
	       THEN REPEAT STRIP_TAC
	      THENL [FIRST_ASSUM(STRIP_ASSUME_TAC o
				SPECL [``0``,  ``s:string``])
		    THEN fs [],
		     FIRST_ASSUM(STRIP_ASSUME_TAC o
				 SPECL [``0``,  ``s:string``])
		     THEN fs [],
		     IMP_RES_TAC LUB_LEMMA7a
		     THEN  RES_TAC
		     THEN  (IMP_RES_TAC
			    (SPEC_ALL
			     (SPEC_LUB_LEMMA1)))
		     THEN RES_TAC, ((IMP_RES_TAC LUB_LEMMA7b)
		     THEN  RES_TAC
		     THEN  (IMP_RES_TAC
			    (SPEC_ALL
			     (SPEC_LUB_LEMMA2)))
		     THEN RES_TAC),
		     (IMP_RES_TAC Proposition1
		      THEN RES_TAC
		      THEN (FIRST_ASSUM
			    (STRIP_ASSUME_TAC o
			     SPECL[``(SUC(t:num))``,
				   ``n:string``]))
		      THEN fs [NOT_EQ_SYM
			       (SPEC_ALL SUC_NOT)]
		      THEN  fs [SUC_SUB1]
		      THEN  (IMP_RES_TAC
			     SPEC_NEXT_LEMMA)
		      THEN (FIRST_ASSUM
			    (STRIP_ASSUME_TAC o
			     SPEC ``(Suffix 1
				     (sigma:num->
				      string->
				      bool#bool))``))
		      THEN RES_TAC)]
	      );


(* DEFSEQ_LESSTHAN_SEQ_IFF_SAT_STE

 Now proving the if and only if version of the above theorem

*)

val DEFSEQ_LESSTHAN_SEQ_IFF_SAT_STE = TAC_PROOF(([], ``!tf. !sigma.
						 in_STE_lang sigma Y_ckt ==>
						     (SAT_STE tf sigma
						      = !t.
						      (DefSeq tf t) leq_state
						      (sigma t))``),
						REPEAT STRIP_TAC THEN EQ_TAC
						THEN fs [leq_state_def]
						THEN (POP_ASSUM MP_TAC
						      THEN SPEC_TAC
						      (``sigma:num->
						       string->bool#bool``,
						       ``sigma:num->string->
						       bool#bool``)
						      THEN SPEC_TAC
						      (``tf:TF``, ``tf:TF``))
						THENL
						[PROVE_TAC
						 [DEFSEQ_LE_THAN_SAT_STE1],
						 PROVE_TAC
						 [DEFSEQ_LE_THAN_SAT_STE2]
						 ]
						);

(* DefTraj satisfies the trajectory formula *)

val DEFTRAJ_SAT_STE= TAC_PROOF(([], ``!tf Y_ckt.
				Monotonic Y_ckt
				==> SAT_STE tf (DefTraj tf Y_ckt)``),
			       REPEAT STRIP_TAC THEN
			       (IMP_RES_TAC (SPEC_ALL(DEFTRAJ_IN_STE_LANG)))
			       THEN FIRST_ASSUM(STRIP_ASSUME_TAC o
						(SPEC ``tf:TF``))
			       THEN (IMP_RES_TAC
				     (SPEC_ALL
				      (DEFSEQ_LESSTHAN_SEQ_IFF_SAT_STE)))
			       THEN (PROVE_TAC
				     [SPEC_ALL(LEQ_DEFSEQ_DEFTRAJ)]));

(* For a circuit model that is monotonic, if a sequence sigma is in the
  language of that circuit model then if sigma satisfies a trajectory formula
  then the defining trajectory of that formula wrt the given circuit model
  returns a lattice value that is less than or equal to the value returned
  by sigma *)


val SAT_STE_IMP_DEFTRAJ_LESSTHAN_SEQ =
    TAC_PROOF(([], ``!tf sigma Y_ckt.
	       Monotonic Y_ckt ==>
		   in_STE_lang sigma Y_ckt ==>
		       SAT_STE tf sigma ==>
			   (!t n. (DefTraj tf Y_ckt t n) leq (sigma t n))``),

	      REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC
	      THEN STRIP_TAC THEN Induct
	      THENL[IMP_RES_TAC DEFSEQ_LESSTHAN_SEQ_IFF_SAT_STE
		    THEN fs [DefTraj_def, leq_state_def],
		    IMP_RES_TAC DEFSEQ_LESSTHAN_SEQ_IFF_SAT_STE
		    THEN REPEAT STRIP_TAC
		    THEN fl [leq_state_def] THEN RW_TAC std_ss [DefTraj_def]
		    THEN fl [Monotonic_def, in_STE_lang_def, leq_state_def]
		    THEN (FIRST_ASSUM(STRIP_ASSUME_TAC o
				      SPECL [``DefTraj (tf:TF)
					     (Y_ckt:(string->bool#bool)->
					      string->bool#bool)(t:num)``,
					     ``(sigma:num->string->bool#bool)
					     (t:num)``]))
		    THEN RES_TAC
		    THEN POP_ASSUM MP_TAC
		    THEN POP_ASSUM MP_TAC
		    THEN POP_ASSUM MP_TAC
		    THEN POP_ASSUM MP_TAC
		    THEN POP_ASSUM MP_TAC
		    THEN
		    FIRST_ASSUM(STRIP_ASSUME_TAC o
				SPECL[``t:num``, ``n:string``])
		    THEN REPEAT STRIP_TAC
		    THEN FIRST_ASSUM(STRIP_ASSUME_TAC o
				     SPEC ``n:string``)
		    THEN FIRST_ASSUM(STRIP_ASSUME_TAC o
				     SPECL [``SUC t:num``,``n:string``])
		    THEN POP_ASSUM MP_TAC THEN RW_TAC std_ss [SUC_ONE_ADD]
		    THEN PROVE_TAC [TRANS_LEMMA, LUB_LEMMA4, ADD_COMM]]);



(* SAT_CKT_IFF_TIME_SHIFT1 and SAT_CKT_IFF_TIME_SHIFT2 are used in the
   proof of SAT_CKT_IFF_TIME_SHIFT - Time shifting theorem *)

val SAT_CKT_IFF_TIME_SHIFT1 =
    TAC_PROOF(([], ``!Ant Cons Y_ckt.
	       (!sigma. (in_STE_lang sigma Y_ckt )
		==> ((SAT_STE Ant sigma)
		     ==> (SAT_STE Cons sigma)))
	       ==>
	       (!sigma. (in_STE_lang sigma Y_ckt )
		==> !t. ((SAT_STE Ant (Suffix t sigma))
			 ==> (SAT_STE Cons (Suffix t sigma))))``),
	      REPEAT STRIP_TAC
	      THEN (IMP_RES_TAC Proposition)
	      THEN RES_TAC
	      THEN (FIRST_ASSUM(STRIP_ASSUME_TAC
				o SPEC ``t:num``))
	      THEN (FIRST_ASSUM(STRIP_ASSUME_TAC o
				SPEC ``Suffix (t:num)
				(sigma:num->string->
				 bool#bool)``))
	      THEN fs []);


val SAT_CKT_IFF_TIME_SHIFT2 =
    TAC_PROOF(([],
	       ``!Ant Cons Y_ckt.
	       (!sigma. (in_STE_lang sigma Y_ckt )
		==> !t. ((SAT_STE Ant (Suffix t sigma))
			 ==> (SAT_STE Cons (Suffix t sigma))))
	       ==> (!sigma. (in_STE_lang sigma Y_ckt )
		    ==> ((SAT_STE Ant sigma)
			 ==> (SAT_STE Cons sigma)))``),
	      REPEAT STRIP_TAC
	      THEN (FIRST_ASSUM(STRIP_ASSUME_TAC
				o SPEC ``(sigma:num->
					  string->
					  bool#bool)``))
	      THEN RES_TAC
	      THEN (FIRST_ASSUM(STRIP_ASSUME_TAC
				o SPEC ``0:num``))
	      THEN fs [SUFFIX_0]
	      );


(* Time shifting theorem

   A given circuit model satisfies an STE assertion if and only if
   for all lattice sequences that are in the language of that circuit
   if the ith suffix of the sequence satisfies the antecedent of the
   STE assertion then the ith suffix of the sequence also satisfies the
   consequent of the STE assertion
*)

val SAT_CKT_IFF_TIME_SHIFT =
    store_thm ("SAT_CKT_IFF_TIME_SHIFT",
	       ``!Ant Cons Y_ckt.
	       SAT_CKT (Ant ==>> Cons) Y_ckt
		   =
		   (!sigma. (in_STE_lang sigma Y_ckt )
		    ==> !t. SAT_STE Ant (Suffix t sigma)
		    ==> SAT_STE Cons (Suffix t sigma))``,

		   REPEAT STRIP_TAC THEN fs [SAT_CKT_def]
		   THEN PROVE_TAC [SAT_CKT_IFF_TIME_SHIFT1,
				   SAT_CKT_IFF_TIME_SHIFT2]);


(* SAT_CKT_IFF_STE1 and SAT_CKT_IFF_STE2 are used in
   the proof of SAT_CKT_IFF_STE *)


val SAT_CKT_IFF_STE1 =
    store_thm ("SAT_CKT_IFF_STE1",
	       ``!Ant Cons Y_ckt.
	       Monotonic Y_ckt ==>
		   (SAT_CKT (Ant ==>> Cons) Y_ckt
		       ==> !t. (DefSeq Cons t) leq_state
		       (DefTraj Ant Y_ckt t))``,
		       let
			   val temp1 = SPECL [``Cons:TF``, ``DefTraj (Ant:TF)
					      (Y_ckt:(string->bool#bool)->
					       string->bool#bool)``]
			       DEFSEQ_LESSTHAN_SEQ_IFF_SAT_STE;
			   val temp2 = SPECL [``Ant:TF``, ``Y_ckt:
					      (string->bool#bool)->
					      string->bool#bool``]
			       DEFTRAJ_SAT_STE;
			   val temp3 = SPECL [``Ant:TF``, ``Y_ckt:
					      (string->bool#bool)->
					      string->bool#bool``]
			       DEFTRAJ_IN_STE_LANG;
			   val temp4 = SPECL [``Ant:TF``, ``Y_ckt:
					      (string->bool#bool)->
					      string->bool#bool``]
			       LEQ_DEFSEQ_DEFTRAJ;;
		       in
			   REPEAT STRIP_TAC THEN fs [SAT_CKT_def] THEN
			   (FIRST_ASSUM(STRIP_ASSUME_TAC o
					SPEC ``DefTraj (Ant:TF)
					(Y_ckt:(string->bool#bool)->
					 string->bool#bool)``))
			   THEN fs [temp1, temp2, temp3, temp4]
		       end);

val SAT_CKT_IFF_STE2 =
    store_thm ("SAT_CKT_IFF_STE2",
	       ``!Ant Cons Y_ckt.
	       Monotonic Y_ckt ==>
		   ((!t. (DefSeq Cons t) leq_state
		     (DefTraj Ant Y_ckt t))
		    ==>
		    SAT_CKT (Ant ==>> Cons) Y_ckt)``,

		   let
		       val temp = SPECL [``Ant:TF``,
					  ``Y_ckt:(string->bool#bool)->
					  string->bool#bool``]
			   DEFTRAJ_IN_STE_LANG;
		   in
		       REPEAT STRIP_TAC
		       THEN fs [SAT_CKT_def, leq_state_def]
		       THEN REPEAT STRIP_TAC
		       THEN STRIP_ASSUME_TAC SEQ_LESS_THAN_SAT_STE
		       THEN (FIRST_ASSUM(STRIP_ASSUME_TAC o
					 SPECL [``Y_ckt:(string->bool#bool)->
						string->bool#bool``,
						``Cons:TF``,
						``DefTraj (Ant:TF)
						(Y_ckt:(string->bool#bool)->
						 string->bool#bool)``,
						``sigma:num->string->
						bool#bool``]))
		       THEN (IMP_RES_TAC temp)
		       THEN (FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``Ant:TF``))
		       THEN
		       (FIRST_ASSUM(STRIP_ASSUME_TAC o
				    SPECL [``Y_ckt:(string->bool#bool)->
						string->bool#bool``,
						``Cons:TF``,
						``DefSeq (Cons:TF)``,
						``DefTraj (Ant:TF)
						(Y_ckt:(string->bool#bool)->
						 string->bool#bool)``
						]))

		       THEN (STRIP_ASSUME_TAC
			     SAT_STE_IMP_DEFTRAJ_LESSTHAN_SEQ)
		       THEN (FIRST_ASSUM(STRIP_ASSUME_TAC o
					 SPECL [``Ant:TF``,
						``sigma:num->string->
						bool#bool``,
						``Y_ckt:(string->bool#bool)->
						string->bool#bool``]))
		       THEN (STRIP_ASSUME_TAC DEFSEQ_LE_THAN_SAT_STE)
		       THEN fs [leq_state_def]
		   end);


(* If the circuit model is monotonic then the circuit model
   satsifies the STE assertion if and only if the Defining Sequence
   of the consequent returns a state value less than or equal to
   the state value returned by the defining trajectory for the
   antecedent wrt the given circuit model *)

val SAT_CKT_IFF_STE =
    store_thm("SAT_CKT_IFF_STE",
	       ``!Ant Cons Y_ckt.
	       Monotonic Y_ckt ==>
		   (SAT_CKT (Ant ==>> Cons) Y_ckt
		       = !t. (DefSeq Cons t) leq_state
		       (DefTraj Ant Y_ckt t))``,
		       PROVE_TAC [SAT_CKT_IFF_STE1, SAT_CKT_IFF_STE2]
		       );;


(* Defining Sequence beyond the depth of a trajectory formula is X *)

val DEFSEQ_X =
    store_thm("DEFSEQ_X",
	      ``!tf i. i > Depth tf ==> !n. DefSeq tf i n = X``,

	      Induct THEN fs [DefSeq_def, Depth_def]
	      THENL[
		    (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN FULL_SIMP_TAC
		     arith_ss []),

		    (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN FULL_SIMP_TAC
		     arith_ss []),

		    (GEN_TAC THEN fs [MAX_def] THEN COND_CASES_TAC THEN
		     REPEAT STRIP_TAC THEN RES_TAC THEN
		     (FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``n:string``))
		     THEN (FULL_SIMP_TAC arith_ss [lub_def, X_def])),

		    (REPEAT STRIP_TAC THEN RES_TAC THEN
		     (FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``n:string``))
		     THEN (FULL_SIMP_TAC arith_ss [lub_def, X_def]) THEN
		     Cases_on `b` THEN fs [FST, SND, X_def]),

		    (REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
		     (FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC ``((i:num)-1)``))
		     THEN (FULL_SIMP_TAC arith_ss []))
		    ]
	      );;

(* If a node doesn't occur in antecedent and it doesn't appear in NEXT Cons
   then it doesn't appear in Ant and it doesn't appear in Cons *)
val NODE_LEMMA0 =
    store_thm ("NODE_LEMMA0", ``!node Ant Cons.
	       ~MEM node (APPEND(Nodes Ant [])
			     (Nodes (NEXT Cons) [])) ==>
	       ~MEM node (APPEND(Nodes Ant [])
			     (Nodes Cons []))
	       ``,
	       REPEAT STRIP_TAC THEN fs [Nodes_def]);



val NODE_LEMMA1 = store_thm ("NODE_LEMMA1",
			     ``!elem tf. ~MEM elem (Nodes (NEXT tf) [])
			     = ~MEM elem (Nodes tf [])``,
			     REPEAT STRIP_TAC THEN Induct_on `tf`
			     THEN REPEAT STRIP_TAC THEN fs [Nodes_def]);




(* If a node doesn't appear in a trajectory formula, it takes on a value X *)
val NODE_LEMMA2 = store_thm("NODE_LEMMA2",
			    ``!tf (node:string).
			       ~MEM node (Nodes tf []) ==>
			    !t. DefSeq tf t node = X``,
			       Induct THENL
			       [fl [Nodes_def, DefSeq_def],
				fl [Nodes_def, DefSeq_def],
				fl [DefSeq_def, Nodes_def]
				THEN REPEAT STRIP_TAC THEN
				fl [MEM_NODES2, lub_def, X_def],
				REPEAT STRIP_TAC
				THEN fl [Nodes_def, DefSeq_def]
				THEN Cases_on `b` THEN fl [X_def],
				fl [DefSeq_def, Nodes_def]]);

(* All nodes that don't appear in the antecedent or the consequent take on
 a value X *)
val NODES_X =
    store_thm ("NODES_X",
	       ``!Ant Cons. !(node:string).
	       ~(MEM node (APPEND(Nodes Ant [])
			   (Nodes Cons [])))
	       ==> !t. (DefSeq Cons t node = X)``,
	       Induct THENL
	       [STRIP_TAC THEN Induct THEN fl [Nodes_def, DefSeq_def]
		THENL [REPEAT STRIP_TAC THEN IMP_RES_TAC MEM_NODES2
		       THEN RES_TAC
		       THEN fl [lub_def, X_def],
		       REPEAT STRIP_TAC THEN fl [X_def]],
		STRIP_TAC THEN Induct THEN fl [Nodes_def, DefSeq_def]
		THENL [REPEAT STRIP_TAC THEN IMP_RES_TAC MEM_NODES2
		       THEN RES_TAC
		       THEN fl [lub_def, X_def],
		       REPEAT STRIP_TAC THEN fl [X_def]],
		fl [Nodes_def] THEN REPEAT STRIP_TAC THEN
		IMP_RES_TAC MEM_NODES2 THEN RES_TAC
		THEN fl [lub_def, X_def],
		REPEAT STRIP_TAC THEN fl [Nodes_def],
		REPEAT STRIP_TAC THEN fl [Nodes_def]]);


(* AuxTheorem1 and Theorem1 are basically identical
   except that in AuxTheorem1 we have rephrased the goal
   with the definition of STE_Impl unfolded. We use AuxTheorem1
   in the proof of Theorem1. Theorem1 has purely academic value
   - succint representation of AuxTheorem1. AuxTheorem1
   is used in the proof of SAT_CKT_IFF_STE_IMPL *)

(* If the given circuit model Y is monotonic then it
   satisfies an STE assertion Ant ==>> Cons if and only if
   the STE Implementation STE_Impl guarantees that *)


(* How the proof of AuxTheorem1 and in turn Theorem1 depends on other
   important lemmas and theorems, specially the fact that Y has got to
   be Monotonic

    AuxTheorem1
       |
       |
       |
      \|/
       |
SAT_CKT_IFF_STE
    |          \
    |           \
    |            \
   \|/            \
    |              \
SAT_CKT_IFF_STE1    \
                     \
                      \
                  SAT_CKT_IFF_STE2
		        |
		        |
		        |
                       \|/
                        |
                 SAT_STE_IMP_DEFTRAJ_LESSTHAN_SEQ
	                |
	                |
                        |
                       \|/
                        |
		 Monotonicity of Y


		 *)




val AuxTheorem1 =
    store_thm ("AuxTheorem1", ``!Ant Cons Y_ckt.
	       Monotonic Y_ckt ==>
		   (SAT_CKT (Ant ==>> Cons) Y_ckt
		       =
		       (!t.
			t <= Depth Cons ==>
			    !n.
			    MEM n (APPEND(Nodes Ant [])(Nodes Cons []))
			    ==>
				(DefSeq Cons t n) leq
				(DefTraj Ant Y_ckt t n)))``,

		       REPEAT STRIP_TAC THEN fl [SAT_CKT_IFF_STE]
		       THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
		       [fl [leq_state_def],
			fl [leq_state_def],
			fl [leq_state_def] THEN REPEAT STRIP_TAC
			THEN STRIP_ASSUME_TAC DEFSEQ_X
			THEN Induct_on `t <= Depth Cons`
			THENL [REPEAT STRIP_TAC THEN
			       Induct_on
			       `MEM node (APPEND(Nodes Ant [])
					  (Nodes Cons []))`
			       THENL [REPEAT STRIP_TAC THEN fl [MEM_APPEND],
				      REPEAT STRIP_TAC THEN
				      STRIP_ASSUME_TAC NODES_X
				      THEN fl [leq_def] THEN
				      PROVE_TAC [lattice_X1_lemma]],
			       fl [leq_def]
			       THEN PROVE_TAC [lattice_X1_lemma]]]);

(* Theorem1 *)

(* If the given circuit model Y is monotonic then it
   satisfies an STE assertion Ant ==>> Cons if and only if
    the STE Implementation STE_Impl guarantees that *)

val Theorem1 = store_thm ("Theorem1",
			  ``!Ant Cons Y_ckt.
			  Monotonic Y_ckt ==>
			      (SAT_CKT (Ant ==>> Cons) Y_ckt
				  = STE_Impl (Ant ==>> Cons) Y_ckt)``,
				  fs [STE_Impl_def] THEN
				  PROVE_TAC [AuxTheorem1]
				  );

(* Refer to explanation in the Big Picture section *)

val SAT_CKT_IFF_STE_IMPL =
    store_thm ("SAT_CKT_IFF_STE_IMPL",
	       ``!Ant Cons Y_ckt.
	       Monotonic Y_ckt ==>
		   (
		    (!sigma.
		     in_STE_lang sigma Y_ckt ==>
			 !t.
			 SAT_STE Ant (Suffix t sigma) ==>
			     SAT_STE Cons (Suffix t sigma)) =
		    (!t.
		     t <= Depth Cons ==>
			 !n.
			 MEM n (APPEND(Nodes Ant [])(Nodes Cons [])) ==>
			     (DefSeq Cons t n) leq (DefTraj Ant Y_ckt t n))
		    )``,
		   REPEAT GEN_TAC
		   THEN fs [SYM(SPEC_ALL SAT_CKT_IFF_TIME_SHIFT)]
		   THEN fs [AuxTheorem1]);



(* Refer for explanation to the Big Picture section *)
val Theorem2 =
    store_thm ("Theorem2", ``!Ant Cons.
	       !Y_ckt Yb_ckt. Okay (Y_ckt, Yb_ckt)
	       ==>
	       (
		!sigma. in_STE_lang sigma Y_ckt
		==> !t. ((SAT_STE Ant (Suffix t sigma))
			 ==> (SAT_STE Cons (Suffix t sigma)))
		)
	       ==>
	       (
		!sigma_b. in_BOOL_lang sigma_b Yb_ckt
		==> !t. ((SAT_BOOL Ant (Suffix_b t sigma_b))
			 ==> (SAT_BOOL Cons (Suffix_b t sigma_b)))
		)``,
	       REPEAT GEN_TAC THEN
	       (STRIP_ASSUME_TAC (SPECL
				  [``Y_ckt:(string->(bool#bool))
				   ->(string->(bool#bool))``,
				   ``Yb_ckt:(string->bool)
				   ->(string->bool)->bool``]
				  Lemma1))
	       THEN (REPEAT STRIP_TAC)
	       THEN (fs [Lemma2])

	       THEN (FIRST_ASSUM (STRIP_ASSUME_TAC o
				  SPEC ``extended_drop_seq
				  (sigma_b:num->string->bool)``))
	       THEN (fs [Suffix_Lemma])
	       THEN (FIRST_ASSUM (STRIP_ASSUME_TAC o
				  SPEC
				  ``sigma_b:num->string->bool``))
	       THEN (fs []));


(* Same as Theorem2 except that the definition of SAT_CKT is
   uunfolded in Theorem2. This theorem has pure academic value.
   - succint representation. This is known as Theorem 2 in the Tech Report
   and also in the TPHOLS paper *)
val AuxTheorem2 =
    store_thm ("AuxTheorem2", ``!Ant Cons.
	       !Y_ckt Yb_ckt. Okay (Y_ckt, Yb_ckt)
	       ==>
	       (SAT_CKT (Ant ==>> Cons) Y_ckt)
		   ==>
		   (
		    !sigma_b. in_BOOL_lang sigma_b Yb_ckt
		    ==> !t. ((SAT_BOOL Ant (Suffix_b t sigma_b))
			     ==> (SAT_BOOL Cons (Suffix_b t sigma_b)))
		    )``, PROVE_TAC [SAT_CKT_IFF_TIME_SHIFT, Theorem2]);

(* Refer to explanation in the Big Picture section *)

val BridgeTheorem =
    store_thm ("BridgeTheorem",
	       ``!Ant Cons Y_ckt Yb_ckt.
	       Okay (Y_ckt, Yb_ckt) ==>
		   Monotonic Y_ckt
		   ==>
		   (

		    (!t.
		     t <= Depth Cons ==>
			 !n.
			 MEM n (APPEND(Nodes Ant [])(Nodes Cons [])) ==>
			     (DefSeq Cons t n) leq (DefTraj Ant Y_ckt t n))

		    ==>
		    (
		     !sigma_b.
		     in_BOOL_lang sigma_b Yb_ckt ==>
			 !t.
			 SAT_BOOL Ant (Suffix_b t sigma_b) ==>
			     SAT_BOOL Cons (Suffix_b t sigma_b))
		    )``,

		   REPEAT STRIP_TAC
		   THEN IMP_RES_TAC (SPEC_ALL SAT_CKT_IFF_STE_IMPL)
		   THEN IMP_RES_TAC (SPEC_ALL Theorem2)
		   );


val BRIDGETHEOREM2 = store_thm ("BRIDGETHEOREM2",
				``!Ant Cons Y_ckt Yb_ckt.
				Okay (Y_ckt,Yb_ckt) ==>
				    Monotonic Y_ckt ==>
					STE_Impl (Ant ==>> Cons) Y_ckt ==>
					    !sigma_b.
					    in_BOOL_lang sigma_b Yb_ckt ==>
						!t.
						SAT_BOOL Ant
						(Suffix_b t sigma_b) ==>
						    SAT_BOOL Cons
						    (Suffix_b t sigma_b)``,
						    MATCH_ACCEPT_TAC (CONV_RULE
						    (SIMP_CONV std_ss
						     [(SYM o SPEC_ALL)
						      STE_Impl_def])
						    BridgeTheorem));


val _ = export_theory();
end;


