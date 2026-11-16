(* ========================================================================= *)
(* FILE          : hh01_tutorialScript.sml                                   *)
(* DESCRIPTION   : HolyHammer examples: first steps                          *)
(*                                                                           *)
(* Every proof below calls the hammer: each hh runs HolyHammer when the      *)
(* theory is built, so building needs a prover (see README.md).  The         *)
(* comment after each hh is the verified, minimised proof that               *)
(* HolyHammer printed when the example was written.                          *)
(* ========================================================================= *)
Theory hh01_tutorial
Ancestors
  list rich_list pred_set
Libs
  holyHammer

(* -------------------------------------------------------------------------
   Lesson 1: calling the hammer on a statement

   Start an interactive session and type

     load "holyHammer"; open holyHammer;
     holyhammer ``MEM x l /\ EVERY P l ==> P x``;

   The hammer prints a progress line for every prover slice it starts
   ("starting vampire slice (96 facts)", ...), a line for every slice
   that finishes ("vampire slice: Theorem (0.25 s)").  Its last message
   is the verified proof:

     Prove the statement in a script with:
       metis_tac [EVERY_MEM]

   and it returns the theorem.  The whole call takes a few seconds, even
   when a prover answers in a fraction of a second: preparing and
   ranking all the loaded theorems takes time too.  The provers found
   that the goal follows from one library fact, EVERY_MEM:

     EVERY P l <=> !e. MEM e l ==> P e

   In your own scripts, paste the verified proof in place of the hammer
   call, so that building the theory does not need the provers.  Theory
   names can be dropped when the theory is opened (listed under
   Ancestors).  These examples keep the hammer call instead, so that
   building them runs the hammer, and give the printed proof in a
   comment:
   ------------------------------------------------------------------------- *)

Theorem mem_every:
  MEM x l /\ EVERY P l ==> P x
Proof
  hh
  (* metis_tac [EVERY_MEM] *)
QED

(* The same thing happens for goals that look harder only because you do
   not know the name of the lemma.  In listTheory this is
   ALL_DISTINCT_CARD_LIST_TO_SET; nobody remembers that. *)
Theorem card_of_distinct_list:
  ALL_DISTINCT l ==> CARD (set l) = LENGTH l
Proof
  hh
  (* metis_tac [ALL_DISTINCT_CARD_LIST_TO_SET] *)
QED

(* -------------------------------------------------------------------------
   Lesson 2: the hh tactic, in the middle of a proof

   hh is a tactic, so it can be used anywhere a tactic can.  It sees the
   assumptions of the goal:

     g `!l1 l2. ALL_DISTINCT (l1 ++ l2) ==> DISJOINT (set l1) (set l2)`;
     e (rpt strip_tac);

         0.  ALL_DISTINCT (l1 ++ l2)
        ------------------------------------
             DISJOINT (set l1) (set l2)

     e hh;

   The last message is again a verified metis_tac call:

     Replace `hh` with:
       metis_tac [ALL_DISTINCT_APPEND']

   In your own script it would replace the hh; the tactics before it
   stay.  Here the library had a
   variant of the right lemma, ALL_DISTINCT_APPEND', stated with
   DISJOINT, and metis_tac uses the assumption on its own.
   ------------------------------------------------------------------------- *)

Theorem distinct_append_disjoint:
  !l1 l2. ALL_DISTINCT (l1 ++ l2) ==> DISJOINT (set l1) (set l2)
Proof
  rpt strip_tac >>
  hh
  (* metis_tac [ALL_DISTINCT_APPEND'] *)
QED

(* -------------------------------------------------------------------------
   Lesson 3: combining several lemmas

   The point of a hammer is not finding one lemma (DB.match and DB.find
   do that) but finding a *combination*.  Mapping an injective function
   over a list without duplicates gives a list without duplicates.  The
   library does not state this with INJ.  The hammer went through nub
   (remove duplicates): a distinct list equals its nub, and the nub of a
   map with an injective function is distinct. *)
Theorem map_inj_distinct:
  INJ f (set l) UNIV /\ ALL_DISTINCT l ==> ALL_DISTINCT (MAP f l)
Proof
  hh
  (* metis_tac [nub_MAP_INJ, all_distinct_nub_id, all_distinct_nub] *)
QED

(* -------------------------------------------------------------------------
   Lesson 4: your own definitions and lemmas

   Definitions and theorems in the current theory are premises like any
   library theorem.  The hammer prints them as fetch "thy" "name"; in the
   script you can write the name directly.
   ------------------------------------------------------------------------- *)

Definition palindrome_def:
  palindrome l <=> REVERSE l = l
End

Theorem palindrome_sing:
  palindrome [x]
Proof
  hh
  (* metis_tac [palindrome_def, REVERSE_SING] *)
QED

Theorem palindrome_map:
  palindrome l ==> palindrome (MAP f l)
Proof
  hh
  (* metis_tac [palindrome_def, MAP_REVERSE] *)
QED

(* Unfolding the definition, then REVERSE (l ++ l') = REVERSE l' ++
   REVERSE l and REVERSE (REVERSE l) = l. *)
Theorem palindrome_append_reverse:
  palindrome (l ++ REVERSE l)
Proof
  hh
  (* metis_tac [palindrome_def, REVERSE_REVERSE, REVERSE_APPEND] *)
QED

(* The hammer went through SNOC (x :: l ++ [x] is x :: SNOC x l). *)
Theorem palindrome_wrap:
  palindrome l ==> palindrome (x :: l ++ [x])
Proof
  hh
  (* metis_tac [palindrome_def, SNOC, SNOC_APPEND, REVERSE_SNOC,
                REVERSE_SNOC_DEF] *)
QED

(* Here the palindrome assumption is irrelevant: every list of length one
   is [HD l].  The hammer noticed, and its proof does not mention
   palindrome_def at all.  The lemma it used lives in
   quantHeuristicsTheory, a theory few users would think of searching. *)
Theorem palindrome_length_one:
  palindrome l /\ LENGTH l = 1 ==> l = [HD l]
Proof
  hh
  (* metis_tac [quantHeuristicsTheory.HD_TL_EQ_NIL_1_bothways] *)
QED

(* -------------------------------------------------------------------------
   Lesson 5: earlier results help later calls

   Every theorem proved so far is a candidate premise for the next call.
   In an interactive session this includes theorems bound with val:

     val th1 = holyhammer ``MEM x l /\ EVERY P l ==> P x``;
     holyhammer ``EVERY P l /\ EVERY Q l /\ MEM x l ==> P x /\ Q x``;

   printed "metis_tac [th1]".  In this theory the same lemma is stored as
   mem_every, so the second goal is proved from it.  Small, named,
   reusable lemmas make the hammer stronger as a development grows.
   ------------------------------------------------------------------------- *)

Theorem mem_every_two:
  EVERY P l /\ EVERY Q l /\ MEM x l ==> P x /\ Q x
Proof
  hh
  (* metis_tac [mem_every] *)
QED

(* -------------------------------------------------------------------------
   Lesson 6: when it fails

   The hammer fails in two ways:

     ATPs could not find a proof

   on a goal that needs induction, an unknown intermediate fact, or that
   is false (try LENGTH (l1 ++ l2) = LENGTH l1); and

     ATPs found proofs, but reconstruction failed for: ...

   when a prover found a proof that metis_tac could not replay in time.
   hh07_inductionScript.sml and hh10_troubleshootingScript.sml show
   what to do in each case.
   ------------------------------------------------------------------------- *)
