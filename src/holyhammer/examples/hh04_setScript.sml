(* ========================================================================= *)
(* FILE          : hh04_setScript.sml                                        *)
(* DESCRIPTION   : HolyHammer examples: sets and functions                   *)
(*                                                                           *)
(* Every proof below was found by calling the hammer at the point marked     *)
(* (* hh *); the tactic that follows is the verified, minimised proof that   *)
(* HolyHammer printed.  See README.md for how to replay the calls.           *)
(* ========================================================================= *)
Theory hh04_set
Ancestors
  pred_set list

(* -------------------------------------------------------------------------
   pred_setTheory represents a set as its characteristic predicate, so
   "x IN s" is literally "s x".  That is a higher-order encoding, and
   some proofs the provers find about sets are hard for Metis to replay;
   hh10_troubleshootingScript.sml shows such a case (surj_iff_image) and
   how to work around it.  Goals stated with the set operations
   (UNION, IMAGE, CARD, ...) rather than with raw predicates are the
   hammer's sweet spot, as the examples below show.
   ------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------
   Set algebra
   ------------------------------------------------------------------------- *)

Theorem inter_distrib_union:
  s INTER (t UNION u) = (s INTER t) UNION (s INTER u)
Proof
  (* hh *)
  metis_tac [UNION_OVER_INTER]
QED

(* De Morgan for relative complement: not a single library lemma.  The
   prover used four facts, including INTER_IDEMPOT to merge the two
   copies of s. *)
Theorem diff_union_de_morgan:
  s DIFF (t UNION u) = (s DIFF t) INTER (s DIFF u)
Proof
  (* hh *)
  metis_tac [DIFF_INTER, INTER_COMM, INTER_IDEMPOT, DIFF_UNION]
QED

Theorem compl_union_de_morgan:
  COMPL (s UNION t) = COMPL s INTER COMPL t
Proof
  (* hh *)
  metis_tac [COMPL_UNION]
QED

Theorem subset_union_absorb:
  s SUBSET t ==> s UNION t = t
Proof
  (* hh *)
  metis_tac [SUBSET_UNION_ABSORPTION]
QED

Theorem subset_chain:
  s SUBSET t /\ t SUBSET u /\ u SUBSET v ==> s SUBSET v
Proof
  (* hh *)
  metis_tac [SUBSET_TRANS]
QED

Theorem insert_absorb:
  x IN s ==> x INSERT s = s
Proof
  (* hh *)
  metis_tac [ABSORPTION_RWT]
QED

Theorem bigunion_of_union:
  BIGUNION (s UNION t) = BIGUNION s UNION BIGUNION t
Proof
  (* hh *)
  metis_tac [BIGUNION_UNION]
QED

Theorem pow_monotone:
  s SUBSET t ==> POW s SUBSET POW t
Proof
  (* hh *)
  metis_tac [SUBSET_POW]
QED

(* -------------------------------------------------------------------------
   Images and functions between sets
   ------------------------------------------------------------------------- *)

Theorem image_of_union:
  IMAGE f (s UNION t) = IMAGE f s UNION IMAGE f t
Proof
  (* hh *)
  metis_tac [IMAGE_UNION]
QED

Theorem image_monotone:
  s SUBSET t ==> IMAGE f s SUBSET IMAGE f t
Proof
  (* hh *)
  metis_tac [IMAGE_SUBSET]
QED

Theorem image_of_image:
  IMAGE f (IMAGE g s) = IMAGE (f o g) s
Proof
  (* hh *)
  metis_tac [IMAGE_IMAGE]
QED

(* Images commute with intersection only for injective functions. *)
Theorem image_inter_inj:
  INJ f UNIV UNIV ==> IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t
Proof
  (* hh *)
  metis_tac [INJ_IMAGE_INTER, SUBSET_UNIV]
QED

Theorem inj_restrict:
  INJ f s t /\ u SUBSET s ==> INJ f u t
Proof
  (* hh *)
  metis_tac [SUBSET_DEF, INJ_SUBSET]
QED

Theorem inj_compose:
  INJ f s t /\ INJ g t u ==> INJ (g o f) s u
Proof
  (* hh *)
  metis_tac [INJ_COMPOSE]
QED

Theorem bij_inverse:
  BIJ f s t ==> BIJ (LINV f s) t s
Proof
  (* hh *)
  metis_tac [BIJ_LINV_BIJ]
QED

(* -------------------------------------------------------------------------
   Finiteness and cardinality
   ------------------------------------------------------------------------- *)

Theorem finite_image:
  FINITE s ==> FINITE (IMAGE f s)
Proof
  (* hh *)
  metis_tac [IMAGE_FINITE]
QED

Theorem finite_inter_left:
  FINITE s ==> FINITE (s INTER t)
Proof
  (* hh *)
  metis_tac [FINITE_INTER]
QED

Theorem card_subset_le:
  FINITE t /\ s SUBSET t ==> CARD s <= CARD t
Proof
  (* hh *)
  metis_tac [CARD_SUBSET]
QED

Theorem card_union_le_sum:
  FINITE s /\ FINITE t ==> CARD (s UNION t) <= CARD s + CARD t
Proof
  (* hh *)
  metis_tac [CARD_UNION_LE]
QED

Theorem card_union_disjoint:
  FINITE s /\ FINITE t /\ DISJOINT s t ==>
  CARD (s UNION t) = CARD s + CARD t
Proof
  (* hh *)
  metis_tac [CARD_UNION_DISJOINT]
QED

(* The library states this with SUC (CARD s); the hammer bridges the
   gap with SUC_ONE_ADD and commutativity. *)
Theorem card_insert_new:
  FINITE s /\ ~(x IN s) ==> CARD (x INSERT s) = CARD s + 1
Proof
  (* hh *)
  metis_tac [CARD_INSERT, arithmeticTheory.ADD_SYM,
             arithmeticTheory.SUC_ONE_ADD]
QED

Theorem card_diff_subset:
  FINITE s /\ t SUBSET s ==> CARD (s DIFF t) = CARD s - CARD t
Proof
  (* hh *)
  metis_tac [CARD_DIFF_EQN, SUBSET_INTER2]
QED

(* Pigeonhole, in its injective form. *)
Theorem inj_card_le:
  FINITE t /\ INJ f s t ==> CARD s <= CARD t
Proof
  (* hh *)
  metis_tac [INJ_CARD]
QED

Theorem card_image_le:
  FINITE s ==> CARD (IMAGE f s) <= CARD s
Proof
  (* hh *)
  metis_tac [CARD_IMAGE]
QED

Theorem bij_card_eq:
  BIJ f s t /\ FINITE s ==> CARD s = CARD t
Proof
  (* hh *)
  metis_tac [FINITE_BIJ]
QED

Theorem card_zero_empty:
  FINITE s /\ CARD s = 0 ==> s = {}
Proof
  (* hh *)
  metis_tac [CARD_EQ_0]
QED

(* -------------------------------------------------------------------------
   Lists as sets

   set l (LIST_TO_SET) connects the two libraries.  The hammer does not
   care which theory a fact lives in: the next two came from
   listTheory.
   ------------------------------------------------------------------------- *)

Theorem set_reverse:
  set (REVERSE l) = set l
Proof
  (* hh *)
  metis_tac [LIST_TO_SET_REVERSE]
QED

Theorem card_set_le_length:
  CARD (set l) <= LENGTH l
Proof
  (* hh *)
  metis_tac [CARD_LIST_TO_SET]
QED
