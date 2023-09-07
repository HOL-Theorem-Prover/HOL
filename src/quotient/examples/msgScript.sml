open HolKernel Parse boolLib;

(* ------------------------------------------------------------------------ *)
(* Representing cryptographic messages as a new datatype in the HOL logic.  *)
(*                                                                          *)
(* This is a representation in HOL using Homeier's quotient package of the  *)
(* symmetric-key cryptographic system modeled in Lawrence C. Paulson's      *)
(* paper, "Defining Functions on Equivalence Classes," Computer Laboratory, *)
(* University of Cambridge, England, 20 April 2004.                         *)
(* ------------------------------------------------------------------------ *)


val _ = new_theory "msg";
val _ = ParseExtras.temp_loose_equality()


(* In interactive sessions, do:

app load ["pred_setTheory",
          "ind_rel",
          "bossLib",
          "quotientLib"];

*)

open pred_setTheory;
open ind_rel;
open bossLib;

open quotientLib;


val REWRITE_THM = fn th => REWRITE_TAC[th];


(* --------------------------------------------------------------------- *)
(* Section 5.1, The Concrete Datatype and the Equivalence Relation.      *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* Create datatypes for the free algebra of cryptographic messages.      *)
(* --------------------------------------------------------------------- *)


val _ = Hol_datatype

        ` msg1 = Nonce1 of num
               | Mpair1 of msg1 => msg1
               | Crypt1 of num => msg1
               | Decrypt1 of num => msg1 ` ;

(* Notice: no nesting or mutual recursion; a simply recursive type. *)


val msg1_distinct = theorem "msg1_distinct";
val msg1_one_one = theorem "msg1_11";
val msg1_cases = theorem "msg1_nchotomy";
val msg1_case_cong = theorem "msg1_case_cong";

val msg1_induction = theorem "msg1_induction";
val msg1_Axiom = theorem "msg1_Axiom";

val msg1_distinct2 = save_thm("msg1_distinct2",
                         CONJ msg1_distinct (GSYM msg1_distinct));
val _ = save_thm("msg1_one_one", msg1_one_one);
val _ = save_thm("msg1_cases", msg1_cases);



(* --------------------------------------------------------------------- *)
(* Definition of equivalence between cryptographic messges.              *)
(* This uses Myra VanInwegen's mutually recursive rule induction pkg.    *)
(* --------------------------------------------------------------------- *)

val msgrel =
“msgrel : msg1 -> msg1 -> bool”;

val msgrel_patterns = [“^msgrel X Y”];

val msgrel_rules_tm =
“

       (* -------------------------------------------- *)
             (^msgrel (Crypt1 k (Decrypt1 k X)) X)                /\


       (* -------------------------------------------- *)
             (^msgrel (Decrypt1 k (Crypt1 k X)) X)                /\


       (* -------------------------------------------- *)
               (^msgrel (Nonce1 N) (Nonce1 N))                   /\


               ((^msgrel X X') /\ (^msgrel Y Y')
       (* -------------------------------------------- *) ==>
             (^msgrel (Mpair1 X Y) (Mpair1 X' Y')))              /\


                         ((^msgrel X X')
       (* -------------------------------------------- *) ==>
               (^msgrel (Crypt1 k X) (Crypt1 k X')))               /\


                         ((^msgrel X X')
       (* -------------------------------------------- *) ==>
             (^msgrel (Decrypt1 k X) (Decrypt1 k X')))             /\


                         ((^msgrel X Y)
       (* -------------------------------------------- *) ==>
                          (^msgrel Y X))                         /\


                  ((^msgrel X Y) /\ (^msgrel Y Z)
       (* -------------------------------------------- *) ==>
                          (^msgrel X Z))

”;

val (msgrel_rules_sat,msgrel_ind_thm) =
    define_inductive_relations msgrel_patterns msgrel_rules_tm;

val msgrel_inv_thms = prove_inversion_theorems
    msgrel_rules_sat msgrel_ind_thm;

val msgrel_strong_ind = prove_strong_induction
    msgrel_rules_sat msgrel_ind_thm;

val _ = save_thm ("msgrel_rules_sat", msgrel_rules_sat);
val _ = save_thm ("msgrel_ind_thm", msgrel_ind_thm);
val _ = save_thm ("msgrel_inv_thms", LIST_CONJ msgrel_inv_thms);
val _ = save_thm ("msgrel_strong_ind", msgrel_strong_ind);


val [CD, DC, NONCE, MPAIR, CRYPT, DECRYPT, msgSYM, msgTRANS]
    = CONJUNCTS msgrel_rules_sat;


(* The cryptographic message equivalence relation is reflexive,    *)
(* symmetric and transitive.                                       *)

val msgrel_REFL = store_thm
   ("msgrel_REFL",
    “!X. msgrel X X”,
    Induct
    THEN RW_TAC std_ss [msgrel_rules_sat]
   );

val msgrel_SYM = store_thm
   ("msgrel_SYM",
    “!X Y. msgrel X Y ==> msgrel Y X”,
    REWRITE_TAC [msgSYM]
   );

val msgrel_TRANS = store_thm
   ("msgrel_TRANS",
    “!X Y Z. msgrel X Y /\ msgrel Y Z ==> msgrel X Z”,
    PROVE_TAC [msgTRANS]
   );



(* --------------------------------------------------------------------- *)
(* Section 5.2, Two Functions on the Free Algebra (well, actually 4).    *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* Definition of function to return all nonces from an expression.       *)
(* --------------------------------------------------------------------- *)

val freenonces1_def = Define
   `(freenonces1 (Nonce1 n)      = {n})                                 /\
    (freenonces1 (Mpair1 x y)    = freenonces1 x UNION freenonces1 y)   /\
    (freenonces1 (Crypt1 k x)    = freenonces1 x)                       /\
    (freenonces1 (Decrypt1 k x)  = freenonces1 x)`;

(* Respectfulness theorem for the freenonces1 function. *)

val freenonces_RSP = store_thm
   ("freenonces_RSP",
    “!V W. msgrel V W ==> (freenonces1 V = freenonces1 W)”,
    rule_induct msgrel_ind_thm
    THEN REPEAT STRIP_TAC
    THEN RW_TAC std_ss [freenonces1_def]
   );


(* --------------------------------------------------------------------- *)
(* Definition of left part of the uppermost Mpair1 constructor.          *)
(* --------------------------------------------------------------------- *)

val freeleft1_def = Define
   `(freeleft1 (Nonce1 n)      = Nonce1 n)        /\
    (freeleft1 (Mpair1 x y)    = x)               /\
    (freeleft1 (Crypt1 k x)    = freeleft1 x)     /\
    (freeleft1 (Decrypt1 k x)  = freeleft1 x)`;

(* Respectfulness theorem for the freeleft1 function. *)

val freeleft_RSP = store_thm
   ("freeleft_RSP",
    “!V W. msgrel V W ==> msgrel (freeleft1 V) (freeleft1 W)”,
    rule_induct msgrel_strong_ind
    THEN REPEAT STRIP_TAC
    THEN RW_TAC std_ss[freeleft1_def,msgrel_REFL,msgrel_SYM]
    THEN IMP_RES_TAC msgrel_TRANS
   );


(* --------------------------------------------------------------------- *)
(* Definition of right part of the uppermost Mpair1 constructor.         *)
(* --------------------------------------------------------------------- *)

val freeright1_def = Define
   `(freeright1 (Nonce1 n)      = Nonce1 n)        /\
    (freeright1 (Mpair1 x y)    = y)               /\
    (freeright1 (Crypt1 k x)    = freeright1 x)    /\
    (freeright1 (Decrypt1 k x)  = freeright1 x)`;

(* Respectfulness theorem for the freeright1 function. *)

val freeright_RSP = store_thm
   ("freeright_RSP",
    “!V W. msgrel V W ==> msgrel (freeright1 V) (freeright1 W)”,
    rule_induct msgrel_strong_ind
    THEN REPEAT STRIP_TAC
    THEN RW_TAC std_ss[freeright1_def,msgrel_REFL,msgrel_SYM]
    THEN IMP_RES_TAC msgrel_TRANS
   );


(* --------------------------------------------------------------------- *)
(* Definition of is_nonce, true if the uppermost constructor is Nonce,   *)
(* not Mpair.                                                            *)
(* --------------------------------------------------------------------- *)

val is_nonce1_def = Define
   `(is_nonce1 (Nonce1 n)      = T)    /\
    (is_nonce1 (Mpair1 x y)    = F)    /\
    (is_nonce1 (Crypt1 k x)    = is_nonce1 x)    /\
    (is_nonce1 (Decrypt1 k x)  = is_nonce1 x)`;

(* Respectfulness theorem for the is_nonce1 function. *)

val is_nonce_RSP = store_thm
   ("is_nonce_RSP",
    “!V W. msgrel V W ==> (is_nonce1 V = is_nonce1 W)”,
    rule_induct msgrel_strong_ind
    THEN REPEAT STRIP_TAC
    THEN RW_TAC std_ss[is_nonce1_def]
   );



(* --------------------------------------------------------------------- *)
(* Section 5.3, The Abstract Message Type and its Constructors.          *)
(* --------------------------------------------------------------------- *)


val msgrel_EQUIV = save_thm("msgrel_EQUIV",
    refl_sym_trans_equiv msgrel_REFL msgrel_SYM msgrel_TRANS);

val equivs = [msgrel_EQUIV];

val old_thms =
     [msg1_cases,
      CD,
      DC,
      freenonces1_def,
      freeleft1_def,
      freeright1_def,
      is_nonce1_def,
      msg1_induction
     ];


(* ==================================================== *)
(*   LIFT TYPES, CONSTANTS, AND THEOREMS BY QUOTIENTS   *)
(* ==================================================== *)

val _ = quotient.chatting := true;
fun mk_fn (nm,t) = {def_name=nm^"_def", fname = nm, func = t, fixity = NONE}

val [msg_cases,
      msgCD,
      msgDC,
      nonces_def,
      left_def,
      right_def,
      is_nonce_def,
      msg_induction
     ] =
    define_quotient_types
    {types = [{name = "msg", equiv = msgrel_EQUIV}],
     defs = map mk_fn [("Nonce", ``Nonce1``),
                       ("Mpair", ``Mpair1``),
                       ("Crypt", ``Crypt1``),
                       ("Decrypt", ``Decrypt1``),
                       ("nonces", ``freenonces1``),
                       ("left", ``freeleft1``),
                       ("right", ``freeright1``),
                       ("is_nonce", ``is_nonce1``)],
     tyop_equivs = [],
     tyop_quotients = [FUN_QUOTIENT],
     tyop_simps = [FUN_REL_EQ, FUN_MAP_I],
     respects = [NONCE, MPAIR, CRYPT, DECRYPT,
                 freenonces_RSP, freeleft_RSP, freeright_RSP, is_nonce_RSP],
     poly_preserves = [FORALL_PRS, EXISTS_PRS],
     poly_respects = [RES_FORALL_RSP, RES_EXISTS_RSP],
     old_thms = old_thms};



(* ---------------------------------------------------------------- *)
(* Save the theorems lifted by the quotient operations.             *)
(* ---------------------------------------------------------------- *)

val _ = map save_thm
    [("msg_cases",msg_cases),
     ("msgCD",msgCD),
     ("msgDC",msgDC),
     ("msg_induction",msg_induction)
    ];

(* Notice the important induction theorem for the lifted msg type:

msg_induction
    |- !P.
         (!n. P (Nonce n)) /\
         (!m m0. P m /\ P m0 ==> P (Mpair m m0)) /\
         (!m. P m ==> !n. P (Crypt n m)) /\
         (!m. P m ==> !n. P (Decrypt n m)) ==>
         !m. P m

This was not lifted by Paulson.  It requires higher order quotients
to lift automatically.
*)


(* ---------------------------------------------------------------- *)
(*      End of saving important theorems from lifting.              *)
(* ---------------------------------------------------------------- *)


(* ---------------------------------------------------------------- *)
(* The rest of these proofs, accomplishing results from Paulson's   *)
(* article, are achieved purely through reasoning at the higher,    *)
(* quotient level (regarding the type "msg", not "msg1").           *)
(* There is never again any need to deal with concepts at the       *)
(* lower level.  That layer may now be completely forgotten.        *)
(* ---------------------------------------------------------------- *)

val Mpair_EQUALS = store_thm
   ("Mpair_EQUALS",
    “!X X' Y Y'. (Mpair X Y = Mpair X' Y') = (X = X') /\ (Y = Y')”,
    PROVE_TAC[left_def,right_def]
    );

val Nonce_EQUALS = store_thm
   ("Nonce_EQUALS",
    “!n n'. (Nonce n = Nonce n') = (n = n')”,
    REPEAT GEN_TAC
    THEN EQ_TAC
    THENL
      [ DISCH_THEN (MP_TAC o AP_TERM ``nonces``)
        THEN RW_TAC std_ss [nonces_def,EXTENSION,NOT_IN_EMPTY,IN_INSERT]
        THEN POP_ASSUM (REWRITE_THM o GSYM),

        DISCH_THEN REWRITE_THM
      ]
    );

val Crypt_EQUALS = store_thm
   ("Crypt_EQUALS",
    “!k X X'. (Crypt k X = Crypt k X') = (X = X')”,
    PROVE_TAC[msgDC]
    );

val Decrypt_EQUALS = store_thm
   ("Decrypt_EQUALS",
    “!k X X'. (Decrypt k X = Decrypt k X') = (X = X')”,
    PROVE_TAC[msgCD]
    );

val Nonce_NOT_EQ_Mpair = store_thm
   ("Decrypt_NOT_EQ_Mpair",
    “!N X Y. ~(Nonce N = Mpair X Y)”,
    PROVE_TAC[is_nonce_def]
    );

(* Here is a proof using the lifted induction theorem for messages: *)

val FINITE_nonces = store_thm
   ("FINITE_nonces",
    “!M. FINITE (nonces M)”,
    HO_MATCH_MP_TAC msg_induction
    THEN REWRITE_TAC[nonces_def]
    THEN REWRITE_TAC[FINITE_INSERT,FINITE_EMPTY,FINITE_UNION]
   );




(* ===================================================================== *)
(* End of the lifting of cryptographic expression types and definitions  *)
(* to the higher, more abstract level where equivalent expressions are   *)
(* actually equal in HOL.                                                *)
(* ===================================================================== *)




val _ = export_theory();

val _ = print_theory_to_file "-" "msg.lst";

val _ = html_theory "msg";

fun print_theory_size () =
   (print "The theory ";
    print (current_theory ());
    print " has ";
    print (Int.toString (length (types (current_theory ()))));
    print " types, ";
    print (Int.toString (length (axioms "-")));
    print " axioms, ";
    print (Int.toString (length (definitions "-")));
    print " definitions, and ";
    print (Int.toString (length (theorems "-")));
    print " theorems.";
    print "\n" );

val _ = print_theory_size();
