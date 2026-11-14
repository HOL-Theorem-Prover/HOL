(* ========================================================================= *)
(* FILE          : hh03_listScript.sml                                       *)
(* DESCRIPTION   : HolyHammer examples: lists                                *)
(*                                                                           *)
(* Every proof below was found by calling the hammer at the point marked     *)
(* (* hh *); the tactic that follows is the verified, minimised proof that   *)
(* HolyHammer printed.  See README.md for how to replay the calls.           *)
(* ========================================================================= *)
Theory hh03_list
Ancestors
  list rich_list sorting

(* -------------------------------------------------------------------------
   Lists are the bread and butter of functional verification, and the list
   libraries (listTheory, rich_listTheory, sortingTheory) contain well over
   two thousand theorems.  Most goals below need one or two of them; the
   point of the hammer is that you do not need to know their names.

   A few examples are adapted from the CoqHammer tutorial and test suite
   (marked [CoqHammer]) and from the Sledgehammer user's guide (marked
   [Sledgehammer]), so that the three systems can be compared on the same
   problems.
   ------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------
   Append, reverse and length
   ------------------------------------------------------------------------- *)

(* [Sledgehammer] The first example of the Sledgehammer guide. *)
Theorem singleton_inj:
  [a] = [b] ==> a = b
Proof
  (* hh *)
  metis_tac [LIST_SING_EQ]
QED

(* The prover's proof used six facts, including the numeral encoding
   facts NUMERAL_DEF and ALT_ZERO; minimisation keeps the three that
   matter.  (simp [] proves this one too: the hammer is not always the
   only option, and the README says when to prefer simp.) *)
Theorem length_rev_append_self:
  LENGTH (REVERSE l ++ l) = 2 * LENGTH l
Proof
  (* hh *)
  metis_tac [arithmeticTheory.TIMES2, LENGTH_REVERSE, LENGTH_APPEND]
QED

Theorem length_two_maps:
  LENGTH (MAP f l ++ MAP g l) = 2 * LENGTH l
Proof
  (* hh *)
  metis_tac [arithmeticTheory.TIMES2, LENGTH_MAP, LENGTH_APPEND]
QED

(* Equational reasoning in both directions: REVERSE_APPEND is used
   left-to-right, the defining equations of ++ right-to-left. *)
Theorem reverse_middle:
  REVERSE (l1 ++ [x] ++ l2) = REVERSE l2 ++ x :: REVERSE l1
Proof
  (* hh *)
  metis_tac [REVERSE_DEF, REVERSE_APPEND, APPEND]
QED

Theorem append_eq_nil:
  l1 ++ l2 = [] <=> l1 = [] /\ l2 = []
Proof
  (* hh *)
  metis_tac [APPEND_eq_NIL]
QED

Theorem length_tl_lt:
  l <> [] ==> LENGTH (TL l) < LENGTH l
Proof
  (* hh *)
  metis_tac [LENGTH_TL_LT]
QED

Theorem hd_of_append:
  l1 <> [] ==> HD (l1 ++ l2) = HD l1
Proof
  (* hh *)
  metis_tac [HD_APPEND_NOT_NIL]
QED

Theorem last_of_snoc:
  LAST (l ++ [x]) = x
Proof
  (* hh *)
  metis_tac [LAST_compute, LAST_APPEND_CONS]
QED

Theorem null_iff_length:
  NULL l <=> LENGTH l = 0
Proof
  (* hh *)
  metis_tac [NULL_LENGTH]
QED

(* A length assumption implies the list is not empty, so it splits into
   its FRONT and LAST.  The hammer goes from n + 1 to SUC n through the
   numeral encoding, then uses LENGTH_EQ_NUM to get a non-empty list. *)
Theorem front_last_split:
  LENGTH l = n + 1 ==> l = FRONT l ++ [LAST l]
Proof
  (* hh *)
  metis_tac [APPEND_FRONT_LAST, listTheory.NOT_CONS_NIL, LENGTH_EQ_NUM,
             numeralTheory.numeral_suc, arithmeticTheory.NUMERAL_DEF,
             arithmeticTheory.ADD_CLAUSES]
QED

(* -------------------------------------------------------------------------
   Membership and quantifiers over lists
   ------------------------------------------------------------------------- *)

(* [CoqHammer] lem_lst: membership in an append. *)
Theorem mem_append_every:
  MEM x (l1 ++ l2) /\ EVERY P l1 /\ EVERY P l2 ==> P x
Proof
  (* hh *)
  metis_tac [EVERY_APPEND, EVERY_MEM]
QED

(* [CoqHammer] lem_lst2. *)
Theorem mem_cons_append:
  MEM z l \/ MEM z l' ==> MEM z (y1::y2::l ++ y3::l')
Proof
  (* hh *)
  metis_tac [MEM_APPEND, MEM]
QED

Theorem every_append_comm:
  EVERY P (l1 ++ l2) <=> EVERY P l2 /\ EVERY P l1
Proof
  (* hh *)
  metis_tac [EVERY_APPEND]
QED

(* rich_listTheory exports this fact twice: as EXISTS_REVERSE and under
   its pre-2000 name SOME_EL_REVERSE.  The hammer happened to pick the
   legacy alias; either works. *)
Theorem exists_reverse:
  EXISTS P (REVERSE l) <=> EXISTS P l
Proof
  (* hh *)
  metis_tac [SOME_EL_REVERSE]
QED

Theorem el_is_mem:
  n < LENGTH l ==> MEM (EL n l) l
Proof
  (* hh *)
  metis_tac [EL_MEM]
QED

Theorem mem_flat_exists:
  MEM x (FLAT ls) <=> ?l. MEM l ls /\ MEM x l
Proof
  (* hh *)
  metis_tac [MEM_FLAT]
QED

Theorem all_distinct_append_left:
  ALL_DISTINCT (l1 ++ l2) ==> ALL_DISTINCT l1
Proof
  (* hh *)
  metis_tac [ALL_DISTINCT_APPEND]
QED

(* -------------------------------------------------------------------------
   Higher-order functions: MAP and FILTER
   ------------------------------------------------------------------------- *)

Theorem map_reverse_comm:
  MAP f (REVERSE l) = REVERSE (MAP f l)
Proof
  (* hh *)
  metis_tac [MAP_REVERSE]
QED

Theorem reverse_map_reverse:
  REVERSE (MAP f (REVERSE l)) = MAP f l
Proof
  (* hh *)
  metis_tac [MAP_REVERSE, REVERSE_REVERSE]
QED

Theorem map_map_compose:
  MAP f (MAP g l) = MAP (f o g) l
Proof
  (* hh *)
  metis_tac [MAP_MAP_o]
QED

(* The lambda-abstraction in the statement does not get in the way:
   the higher-order slices pass it to the provers unchanged. *)
Theorem filter_filter_conj:
  FILTER P (FILTER Q l) = FILTER (\x. Q x /\ P x) l
Proof
  (* hh *)
  metis_tac [FILTER_FILTER, FILTER_COMM]
QED

Theorem length_filter_le:
  LENGTH (FILTER P l) <= LENGTH l
Proof
  (* hh *)
  metis_tac [LENGTH_FILTER_LEQ]
QED

Theorem mem_filter_imp:
  MEM x (FILTER P l) ==> P x /\ MEM x l
Proof
  (* hh *)
  metis_tac [MEM_FILTER]
QED

Theorem all_distinct_filter:
  ALL_DISTINCT l ==> ALL_DISTINCT (FILTER P l)
Proof
  (* hh *)
  metis_tac [FILTER_ALL_DISTINCT]
QED

(* -------------------------------------------------------------------------
   TAKE, DROP and ZIP
   ------------------------------------------------------------------------- *)

Theorem take_append_drop:
  TAKE n l ++ DROP n l = l
Proof
  (* hh *)
  metis_tac [TAKE_DROP]
QED

Theorem length_take_le:
  n <= LENGTH l ==> LENGTH (TAKE n l) = n
Proof
  (* hh *)
  metis_tac [LENGTH_TAKE]
QED

Theorem length_zip_same:
  LENGTH l1 = LENGTH l2 ==> LENGTH (ZIP (l1, l2)) = LENGTH l1
Proof
  (* hh *)
  metis_tac [LENGTH_ZIP]
QED

Theorem map_fst_zip_same:
  LENGTH l1 = LENGTH l2 ==> MAP FST (ZIP (l1, l2)) = l1
Proof
  (* hh *)
  metis_tac [MAP_ZIP]
QED

Theorem sum_append_comm:
  SUM (l1 ++ l2) = SUM l2 + SUM l1
Proof
  (* hh *)
  metis_tac [SUM_APPEND, arithmeticTheory.ADD_SYM]
QED

(* -------------------------------------------------------------------------
   Permutations and sortedness (sortingTheory)
   ------------------------------------------------------------------------- *)

Theorem perm_same_length:
  PERM l1 l2 ==> LENGTH l1 = LENGTH l2
Proof
  (* hh *)
  metis_tac [PERM_LENGTH]
QED

Theorem perm_same_members:
  PERM l1 l2 ==> (MEM x l1 <=> MEM x l2)
Proof
  (* hh *)
  metis_tac [PERM_MEM_EQ]
QED

(* [CoqHammer] lem_perm_0 from the hammer tutorial. *)
Theorem perm_cons_append:
  PERM l1 (y::l2) ==> PERM (x::l1 ++ l3) (x::y::l2 ++ l3)
Proof
  (* hh *)
  metis_tac [PERM_CONS_IFF, PERM_APPEND_IFF]
QED

(* [CoqHammer] lem_perm_1: the same with the two heads swapped.  This
   needs five lemmas, chained through transitivity; it took Vampire about
   ten seconds.  Neither simp [] nor metis_tac [] on its own proves it. *)
Theorem perm_cons_append_swap:
  PERM l1 (y::l2) ==> PERM (x::l1 ++ l3) (y::x::l2 ++ l3)
Proof
  (* hh *)
  metis_tac [PERM_CONS_IFF, PERM_APPEND_IFF, PERM_TRANS, PERM_SWAP_AT_FRONT,
             PERM_SYM]
QED

(* SORTED_APPEND needs a transitive order; the hammer also found the
   fact that <= on numbers is transitive. *)
Theorem sorted_append_left:
  SORTED $<= (l1 ++ l2) ==> SORTED $<= l1
Proof
  (* hh *)
  metis_tac [SORTED_APPEND, arithmeticTheory.transitive_LE]
QED
