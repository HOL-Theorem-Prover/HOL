(* ------------------------------------------------------------------------- *)
(* Permutation Group.                                                        *)
(* ------------------------------------------------------------------------- *)

(*===========================================================================*)

(* add all dependent libraries for script *)
open HolKernel boolLib bossLib Parse;

(* declare new theory at start *)
val _ = new_theory "permutation";

(* ------------------------------------------------------------------------- *)


(* val _ = load "jcLib"; *)
open jcLib; (* for stripDup *)

(* open dependent theories *)
(* val _ = load "symmetryTheory"; *)
open pred_setTheory arithmeticTheory;
open helperCountTheory;
open helperSetTheory;

open listTheory rich_listTheory;
open helperListTheory;

open mapCountTheory;
open combinatoricsTheory;

(* Get dependent theories local *)
open monoidTheory groupTheory;
open submonoidTheory subgroupTheory;
open monoidMapTheory groupMapTheory;
open quotientGroupTheory; (* for homo_image_def *)

open symmetryTheory;


(* ------------------------------------------------------------------------- *)
(* Permutation Group Documentation                                           *)
(* ------------------------------------------------------------------------- *)
(* Overloading (# is temporary):
   (l1 oo l2) n   = list_op n l1 l2
*)
(* Definitions and Theorems (# are exported):

   Permutation Group:
   list_to_bij_def     |- !ls. list_to_bij ls = (\j. if j < LENGTH ls then EL j ls else ARB)
   bij_to_list_def     |- !n f. bij_to_list n f = MAP f [0 ..< n]
   bij_count_map_bij_alt
                       |- !n. BIJ (bij_to_list n) (bij_count n) (perm_count n)
   list_op_def         |- !n l1 l2. (l1 oo l2) n =
                                    bij_to_list n (list_to_bij l1 o list_to_bij l2)

   permutation_group_def       |- !n. permutation_group n =
                                      <|carrier := perm_count n;
                                             op := list_op n;
                                             id := [0 ..< n]
                                       |>
   permutation_group_property  |- !n. (permutation_group n).carrier = perm_count n /\
                                      (permutation_group n).id = [0 ..< n] /\
                                      !l1 l2. (permutation_group n).op l1 l2 = (l1 oo l2) n
   permutation_group_carrier   |- !n. (permutation_group n).carrier = perm_count n
   permutation_group_id        |- !n. (permutation_group n).id = [0 ..< n]
   permutation_group_op        |- !n l1 l2. (permutation_group n).op l1 l2 = (l1 oo l2) n
   list_to_bij_thm     |- !ls j. j < LENGTH ls ==> list_to_bij ls j = EL j ls
   map_list_to_bij_id  |- !ls. MAP (list_to_bij ls) [0 ..< LENGTH ls] = ls
   list_to_bij_element |- !ls n j. ls IN perm_count n /\ j < n ==> list_to_bij ls j < n
   list_to_bij_count_inj   |- !ls n. ls IN perm_count n ==> INJ (list_to_bij ls) (count n) (count n)
   list_to_bij_count_surj  |- !ls n. ls IN perm_count n ==> SURJ (list_to_bij ls) (count n) (count n)
   list_to_bij_count_bij   |- !ls n. ls IN perm_count n ==> list_to_bij ls PERMUTES count n
   bij_to_list_image_subset
                       |- !n. IMAGE (bij_to_list n) (bij_count n) SUBSET perm_count n
   bij_to_list_image_superset
                       |- !n. perm_count n SUBSET IMAGE (bij_to_list n) (bij_count n)
   bij_to_list_image_thm
                       |- !n. perm_count n = IMAGE (bij_to_list n) (bij_count n)
   permutation_group_homo_image
                       |- !n. permutation_group n =
                              homo_image (bij_to_list n) (symmetric_group (count n))
                                                         (permutation_group n)
   bij_to_list_on_count    |- !f n. bij_to_list n f = bij_to_list n (f on count n)
   list_to_bij_to_list_eq  |- !f n. list_to_bij (bij_to_list n (f on count n)) = f on count n
   list_to_bij_to_list_thm |- !f n. f IN fun_count n n ==> list_to_bij (bij_to_list n f) = f
   bij_to_list_compose     |- !f g n. f IN fun_count n n /\ g IN fun_count n n ==>
                                      bij_to_list n (f o g) = (bij_to_list n f oo bij_to_list n g) n
   bij_to_list_map_homo    |- !n. MonoidHomo (bij_to_list n)
                                             (symmetric_group (count n))
                                             (permutation_group n)
   permutation_group_group |- !n. Group (permutation_group n)
   symmetric_group_iso_permutation_group
                           |- !n. GroupIso (bij_to_list n) (symmetric_group (count n))
                                                           (permutation_group n)

   list_to_bij_alt     |- !ls. list_to_bij ls = (\j. EL j ls) on count (LENGTH ls)
   list_to_bij_on_count|- !ls. list_to_bij ls = list_to_bij ls on count (LENGTH ls)
   list_to_bij_image_subset
                       |- !n. IMAGE list_to_bij (perm_count n) SUBSET bij_count n
   list_op_thm         |- !l1 l2 n. LENGTH l1 = n /\ LENGTH l2 = n /\ set l2 = count n ==>
                                    (l1 oo l2) n = MAP (\j. EL j l1) l2
   list_op_el          |- !l1 l2 n j. LENGTH l1 = n /\ LENGTH l2 = n /\ set l2 = count n /\
                                      j < n ==> EL j ((l1 oo l2) n) = EL (EL j l2) l1
   list_op_length      |- !l1 l2 n. LENGTH l1 = n /\ LENGTH l2 = n /\ set l2 = count n ==>
                                    LENGTH ((l1 oo l2) n) = n
   list_op_all_distinct|- !l1 l2 n. LENGTH l1 = n /\ LENGTH l2 = n /\ set l2 = count n /\
                                    ALL_DISTINCT l1 /\ ALL_DISTINCT l2 ==>
                                    ALL_DISTINCT ((l1 oo l2) n)
   list_op_set         |- !l1 l2 n. LENGTH l1 = n /\ LENGTH l2 = n /\ set l2 = count n ==>
                                    set ((l1 oo l2) n) = set l1
   perm_count_list_op  |- !l1 l2 n. l1 IN perm_count n /\ l2 IN perm_count n ==>
                                    (l1 oo l2) n IN perm_count n /\
                                    (l1 oo l2) n = MAP (\j. EL j l1) l2
   perm_count_list_op_closure
                       |- !l1 l2 n. l1 IN perm_count n /\ l2 IN perm_count n ==>
                                    (l1 oo l2) n IN perm_count n
   perm_count_list_op_thm
                       |- !l1 l2 n. l1 IN perm_count n /\ l2 IN perm_count n ==>
                                    (l1 oo l2) n = MAP (\j. EL j l1) l2
   perm_count_list_op_el
                       |- !l1 l2 n j. l1 IN perm_count n /\ l2 IN perm_count n /\ j < n ==>
                                      EL j ((l1 oo l2) n) = EL (EL j l2) l1
   perm_count_list_op_all_distinct
                       |- !l1 l2 n. l1 IN perm_count n /\ l2 IN perm_count n ==>
                                    ALL_DISTINCT ((l1 oo l2) n)
   perm_count_list_op_set
                       |- !l1 l2 n. l1 IN perm_count n /\ l2 IN perm_count n ==>
                                    set ((l1 oo l2) n) = count n
   perm_count_list_op_length
                       |- !l1 l2 n. l1 IN perm_count n /\ l2 IN perm_count n ==>
                                    LENGTH ((l1 oo l2) n) = n
   perm_count_list_el_inj
                       |- !ls n. ls IN perm_count n ==> INJ (\j. EL j ls) (count n) (count n)
   list_to_bij_map_thm |- !f ls. list_to_bij (MAP f ls) = (\j. f (EL j ls)) on count (LENGTH ls)
   list_to_bij_compose |- !l1 l2 n. l1 IN perm_count n /\ l2 IN perm_count n ==>
                                    list_to_bij ((l1 oo l2) n) =
                                    list_to_bij l1 o list_to_bij l2 on count n
   list_to_bij_id_thm  |- !n. list_to_bij [0 ..< n] = I on count n
   list_to_bij_map_homo|- !n. MonoidHomo list_to_bij (permutation_group n)
                                                     (symmetric_group (count n))
   list_to_bij_perm_count_inj
                       |- !n. INJ list_to_bij (perm_count n) (bij_count n)
   bij_to_list_inj_all_distinct
                       |- !f n. INJ f (count n) (count n) ==> ALL_DISTINCT (bij_to_list n f)
   bij_to_list_surj_set|- !f n. SURJ f (count n) (count n) ==> set (bij_to_list n f) = count n
   list_to_bij_image_superset
                       |- !n. bij_count n SUBSET IMAGE list_to_bij (perm_count n)
   list_to_bij_image_thm
                       |- !n. bij_count n = IMAGE list_to_bij (perm_count n)
   list_to_bij_perm_count_surj
                       |- !n. SURJ list_to_bij (perm_count n) (bij_count n)
   list_to_bij_perm_count_bij
                       |- !n. BIJ list_to_bij (perm_count n) (bij_count n)
   list_to_bij_map_iso |- !n. MonoidIso list_to_bij (permutation_group n)
                                              (symmetric_group (count n))
   permutation_group_iso_symmetric_group
                        |- !n. GroupIso list_to_bij (permutation_group n)
                                              (symmetric_group (count n))

   perm_count_has_id    |- !n. [0 ..< n] IN perm_count n
   perm_count_list_op_lid
                        |- !ls n. ls IN perm_count n ==> ([0 ..< n] oo ls) n = ls
   perm_count_list_op_rid
                        |- !ls n. ls IN perm_count n ==> (ls oo [0 ..< n]) n = ls
   perm_count_list_op_assoc
                        |- !l1 l2 l3 n. l1 IN perm_count n /\ l2 IN perm_count n /\
                                        l3 IN perm_count n ==>
                                        ((l1 oo l2) n oo l3) n = (l1 oo (l2 oo l3) n) n
   list_op_inv_def       |- !ls. list_op_inv ls = MAP (\j. findi j ls) [0 ..< LENGTH ls]
   perm_count_has_list_op_inv
                         |- !ls n. ls IN perm_count n ==> list_op_inv ls IN perm_count n
   perm_count_list_op_inv|- !ls n. ls IN perm_count n ==> (list_op_inv ls oo ls) n = [0 ..< n]
   permutation_group_inv |- !ls n. (permutation_group n).inv ls =
                                      if ls IN perm_count n then list_op_inv ls
                                      else FAIL ((permutation_group n).inv ls) bad_element
*)

(* ------------------------------------------------------------------------- *)
(* Helper Theorems                                                           *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Permutation Group                                                         *)
(* ------------------------------------------------------------------------- *)

(* Idea:

(bij_count n) is a set of functions (bijections).
bij_maps_bij_count  |- !n. bij_maps (count n) = bij_count n

(perm_count n) is a set of lists (necklaces).
perm_set_perm_count |- !n. perm_set (count n) = perm_count n

We know symmetric_group_group, with carrier (bij_maps s):
|- !s. Group (symmetric_group s)

There is a corresponding group, permutation_group, with carrier (perm_set s).

Apply:
group_homo_homo_image_group
|- !g h f. Group g /\ MonoidHomo f g h ==> Group (homo_image f g h)
homo_image_def
|- !f g h. homo_image f g h =
             <|carrier := IMAGE f G; op := h.op; id := h.id|>,

However, only (perm_count n) can easily identify [0 ..< n] as identity.
For (perm_set s), when s is not (count n), what should be the identity?
Only when s = count n can we formulate a suitable binary operation.

*)

(* Define a necklace to bijection conversion. *)
(*
Definition list_to_bij_def:
   list_to_bij (ls:num list) = \j. EL j ls
End
*)
(* Note that list_to_bij ls gives a function of type :num -> :num. *)
Definition list_to_bij_def:
   list_to_bij (ls:num list) = \j. if j < LENGTH ls then EL j ls else ARB
End
(* or: if j < LENGTH ls then EL j ls else ??? *)

(* Define a bijection to necklace conversion. *)
Definition bij_to_list_def:
   bij_to_list n (f:num -> num) = MAP f [0 ..< n]
End

(* val bij_count_map_bij =
|- !n. BIJ (\f. MAP f [0 ..< n]) (bij_count n) (perm_count n): thm *)

(* Theorem: BIJ (bij_to_list n) (bij_count n) (perm_count n) *)
(* Proof: by bij_count_map_bij, bij_to_list_def, FUN_EQ_THM. *)
Theorem bij_count_map_bij_alt:
  !n. BIJ (bij_to_list n) (bij_count n) (perm_count n)
Proof
  rpt strip_tac >>
  assume_tac bij_count_map_bij >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  qabbrev_tac `f = \f:num -> num. MAP f [0 ..< n]` >>
  `f = bij_to_list n` by rw[bij_to_list_def, FUN_EQ_THM] >>
  fs[BIJ_CONG]
QED


(* Define necklace composition. *)
Definition list_op_def:
   list_op n l1 l2 = bij_to_list n ((list_to_bij l1) o (list_to_bij l2))
End
(* overload list_op with infix symbol. *)
val _ = overload_on("oo", ``\l1 l2 n. list_op n l1 l2``);
val _ = set_fixity "oo" (Infix(NONASSOC, 450)); (* same as relation *)
(* val _ = clear_overloads_on "oo"; *)
(* list_op_def:
val it =
   |- !n l1 l2. (l1 oo l2) n = bij_to_list n (list_to_bij l1 o list_to_bij l2): thm
*)

(*
> EVAL ``list_op 3 [2;0;1] [1;0;2]``;
val it = |- ([2; 0; 1] oo [1; 0; 2]) 3 = [0; 2; 1]: thm
> EVAL ``([2;0;1] oo [1;0;2]) 3``;
val it = |- ([2; 0; 1] oo [1; 0; 2]) 3 = [0; 2; 1]: thm
*)

(* Define the permutation group for lists in (perm_count n). *)
Definition permutation_group_def:
   permutation_group n =
      <|carrier := perm_count n;
             op := list_op n;
             id := [0 ..< n]
       |>
End
(* JC: if carrier is perm_set s,
   what is the binary operation? Also, what is the identity?
*)

(* Theorem: properties of (permutation_group n). *)
(* Proof: by permutation_group_def. *)
Theorem permutation_group_property:
  !n. (permutation_group n).carrier = perm_count n /\
      (permutation_group n).id = [0 ..< n] /\
      !l1 l2. (permutation_group n).op l1 l2 = (l1 oo l2) n
Proof
  simp[permutation_group_def]
QED

(* Derive theorems. *)
Theorem permutation_group_carrier =
   permutation_group_property |> SPEC_ALL |> CONJUNCT1 |> GEN_ALL;
(* val permutation_group_carrier =
   |- !n. (permutation_group n).carrier = perm_count n: thm *)

Theorem permutation_group_id =
   permutation_group_property |> SPEC_ALL |> CONJUNCT2 |> CONJUNCT1 |> GEN_ALL;
(* val permutation_group_id = |- !n. (permutation_group n).id = [0 ..< n]: thm *)

Theorem permutation_group_op =
   permutation_group_property |> SPEC_ALL |> CONJUNCT2 |> CONJUNCT2 |> GEN_ALL;
(* val permutation_group_op =
   |- !n l1 l2. (permutation_group n).op l1 l2 = (l1 oo l2) n: thm *)

(* Theorem: j < LENGTH ls ==> list_to_bij ls j = EL j ls *)
(* Proof: by list_to_bij_def. *)
Theorem list_to_bij_thm:
  !ls j. j < LENGTH ls ==> list_to_bij ls j = EL j ls
Proof
  simp[list_to_bij_def]
QED

(* Theorem: MAP (list_to_bij ls) [0 ..< (LENGTH ls)] = ls *)
(* Proof:
   Let f = (\j. list_to_bij ls j),
       n = LENGTH ls.
   First, note that
     LENGTH (MAP f [0 ..< n])
   = LENGTH [0 ..< n]              by LENGTH_MAP
   = n                             by listRangeLHI_LEN
   To apply LIST_EQ, it remains to compute, for j < n,
     EL j (MAP f [0 ..< n])
   = f (EL j [0 ..< n])            by EL_MAP
   = f j                           by listRangeLHI_EL
   = list_to_bij ls j              by notation
   = EL j ls                       by list_to_bij_def
   Therefore, MAP f [0 ..< n] = ls by LIST_EQ
*)
Theorem map_list_to_bij_id:
  !ls. MAP (list_to_bij ls) [0 ..< (LENGTH ls)] = ls
Proof
  rpt strip_tac >>
  irule LIST_EQ >>
  rw[list_to_bij_def, EL_MAP, listRangeLHI_EL]
QED

(* Theorem: ls IN perm_count n /\ j < n ==> list_to_bij ls j < n *)
(* Proof:
   Note LENGTH ls = n                    by perm_count_element_length
    and set ls = count n                 by perm_count_element
    Now list_to_bij ls j = EL j ls       by list_to_bij_def
    and MEM (EL j ls) ls                 by MEM_EL
   Thus list_to_bij ls j < n             by IN_COUNT, set ls = count n
*)
Theorem list_to_bij_element:
  !ls n j. ls IN perm_count n /\ j < n ==> list_to_bij ls j < n
Proof
  rpt strip_tac >>
  imp_res_tac perm_count_element_length >>
  fs[perm_count_def, list_to_bij_def] >>
  `MEM (EL j ls) ls` by metis_tac[MEM_EL] >>
  rfs[]
QED

(* Theorem: ls IN perm_count n ==> INJ (list_to_bij ls) (count n) (count n) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) x < n ==> list_to_bij ls x < n, true    by list_to_bij_element
   (2) x < n /\ y < n /\ list_to_bij ls x = list_to_bij ls y ==> x = y
       Note list_to_bij ls x = EL x ls         by bij_to_list_def
        and list_to_bij ls y = EL y ls         by bij_to_list_def
        Now ALL_DISTINCT ls                    by perm_count_element
        and LENGTH ls = n                      by perm_count_element_length
         so EL x ls = EL y ls ==> x = y        by ALL_DISTINCT_EL_IMP
*)
Theorem list_to_bij_count_inj:
  !ls n. ls IN perm_count n ==> INJ (list_to_bij ls) (count n) (count n)
Proof
  rw[INJ_DEF] >-
  simp[list_to_bij_element] >>
  imp_res_tac perm_count_element_length >>
  `EL x ls = EL y ls` by metis_tac[list_to_bij_thm] >>
  rfs[perm_count_element, ALL_DISTINCT_EL_IMP]
QED

(* Theorem: ls IN perm_count n ==> SURJ (list_to_bij ls) (count n) (count n) *)
(* Proof:
   By SURJ_DEF, this is to show:
   (1) x < n ==> list_to_bij ls x < n, true    by list_to_bij_element
   (2) x < n ==> ?y. y < n /\ list_to_bij ls y = x
       Note LENGTH ls = n                      by perm_count_element_length
        and set ls = count n                   by perm_count_element
        and ?y. y < n /\ x = EL y ls           by MEM_EL
       Take this y, then
         list_to_bij ls y = EL y ls = x        by list_to_bij_def, IN_COUNT
*)
Theorem list_to_bij_count_surj:
  !ls n. ls IN perm_count n ==> SURJ (list_to_bij ls) (count n) (count n)
Proof
  rw[SURJ_DEF] >-
  simp[list_to_bij_element] >>
  imp_res_tac perm_count_element_length >>
  fs[perm_count_def] >>
  metis_tac[MEM_EL, list_to_bij_thm, IN_COUNT]
QED

(* Theorem: ls IN perm_count n ==> list_to_bij ls PERMUTES count n *)
(* Proof:
   Note INJ (list_to_bij ls) (count n) (count n)   by list_to_bij_count_inj
    and FINITE (count n)                           by FINITE_COUNT
     so BIJ (list_to_bij ls) (count n) (count n)   by FINITE_INJ_IS_BIJ
*)
Theorem list_to_bij_count_bij:
  !ls n. ls IN perm_count n ==> list_to_bij ls PERMUTES count n
Proof
  simp[FINITE_INJ_IS_BIJ, list_to_bij_count_inj]
QED

(* Theorem: IMAGE (bij_to_list n) (bij_count n) SUBSET (perm_count n) *)
(* Proof:
   By bij_to_list_def, bij_count_element, SUBSET_DEF, this is to show:
      !f. f PERMUTES count n ==> MAP (f on count n) [0 ..< n] IN perm_count n
   Note MAP (f on count n) [0 ..< n]
      = MAP f [0 ..< n]                    by map_on_count
    Now INJ f (count n) (count n)          by BIJ_DEF
    and ALL_DISTINCT [0 ..< n]             by listRangeLHI_ALL_DISTINCT
     so ALL_DISTINCT (MAP f [0 ..< n])     by ALL_DISTINCT_MAP_INJ
   Also SURJ f (count n) (count n)         by BIJ_DEF
          set (MAP f [0 ..< n])
        = IMAGE f (set [0 ..< n])          by LIST_TO_SET_MAP
        = IMAGE f (count n)                by listRangeLHI_SET
        = count n                          by IMAGE_SURJ
   Thus MAP f [0 ..< n] IN perm_count n    by perm_count_def
*)
Theorem bij_to_list_image_subset:
  !n. IMAGE (bij_to_list n) (bij_count n) SUBSET (perm_count n)
Proof
  rw[bij_to_list_def, bij_count_element, SUBSET_DEF] >>
  simp[GSYM map_on_count, perm_count_element] >>
  fs[BIJ_DEF, INJ_DEF, ALL_DISTINCT_MAP_INJ] >>
  fs[LIST_TO_SET_MAP, listRangeLHI_SET] >>
  fs[IMAGE_SURJ]
QED

(* Theorem: (perm_count n) SUBSET IMAGE (bij_to_list n) (bij_count n) *)
(* Proof:
   By bij_to_list_def, bij_count_element, SUBSET_DEF, this is to show:
      !x. x IN perm_count n ==>
      ?g. x = MAP g [0 ..< n] /\ ?f. g = f on count n /\ f PERMUTES count n
   Note LENGTH x = n           by perm_count_element_length
   Let f = list_to_bij x, and g = f on count n.
   Then MAP g [0 ..< n]
      = MAP f [0 ..< n]        by map_on_count
      = x                      by map_list_to_bij_id
    and f PERMUTES count n     by list_to_bij_count_bij
*)
Theorem bij_to_list_image_superset:
  !n. (perm_count n) SUBSET IMAGE (bij_to_list n) (bij_count n)
Proof
  rw[bij_to_list_def, bij_count_element, SUBSET_DEF] >>
  imp_res_tac perm_count_element_length >>
  qexists_tac `(list_to_bij x) on count n` >>
  rw[GSYM map_on_count, map_list_to_bij_id] >>
  qabbrev_tac `n = LENGTH x` >>
  qexists_tac `list_to_bij x` >>
  simp[list_to_bij_count_bij]
QED

(* Theorem: perm_count n = IMAGE (bij_to_list n) (bij_count n) *)
(* Proof:
   Let s = perm_count n,
       t = IMAGE (bij_to_list n) (bij_count n).
   Note s SUBSET t         by bij_to_list_image_superset
    and t SUBSET s         by bij_to_list_image_subset
   Thus s = t              by SUBSET_ANTISYM
*)
Theorem bij_to_list_image_thm:
  !n. perm_count n = IMAGE (bij_to_list n) (bij_count n)
Proof
  rpt strip_tac >>
  irule SUBSET_ANTISYM >>
  simp[bij_to_list_image_superset, bij_to_list_image_subset]
QED

(* Theorem: permutation_group n =
            homo_image (bij_to_list n) (symmetric_group (count n)) (permutation_group n) *)
(* Proof:
   Let f = bij_to_list n,
       g = symmetric_group (count n),
       h = permutation_group n.
   By homo_image_def, this is to show:
      (homo_image f g h).carrier = (permutation_group n).carrier
      (homo_image f g h).carrier
    = IMAGE f G                          by homo_image_def
    = IMAGE f (bij_maps (count n))       by symmetric_group_def
    = IMAGE f (bij_count n)              by bij_maps_bij_count
    = perm_count n                       by bij_to_list_image_thm
    = (permutation_group n).carrier      by permutation_group_def
*)
Theorem permutation_group_homo_image:
  !n. permutation_group n =
          homo_image (bij_to_list n) (symmetric_group (count n)) (permutation_group n)
Proof
  rw[permutation_group_def, homo_image_def, symmetric_group_def, bij_maps_bij_count] >>
  simp[bij_to_list_image_thm]
QED

(* Theorem: bij_to_list n f = bij_to_list n (f on (count n)) *)
(* Proof:
     bij_to_list n (f on (count n))
   = MAP (f on count n) [0 ..< n]  by bij_to_list_def
   = MAP f [0 ..< n]               by map_on_count
   = bij_to_list n f               by bij_to_list_def
*)
Theorem bij_to_list_on_count:
  !f n. bij_to_list n f = bij_to_list n (f on (count n))
Proof
  simp[bij_to_list_def, GSYM map_on_count]
QED

(* Theorem: list_to_bij (bij_to_list n (f on count n)) = (f on count n) *)
(* Proof:
   If j < n,
     (list_to_bij (bij_to_list n (f on count n))) j
   = (list_to_bij (bij_to_list n f)) j       by bij_to_list_on_count
   = (list_to_bij (MAP f [0 ..< n])) j       by bij_to_list_def
   = (\j. EL j (MAP f [0 ..< n])) j          by list_to_bij_def, j < n [*]
   = EL j (MAP f [0 ..< n])                  by function application
   = f (EL j [0 ..< n])                      by EL_MAP, j < n
   = f j                                     by listRangeLHI_EL, j < n
   If ~(j < n),
   Hence by FUN_EQ_THM, step [*] gives ARB, and (f on (count n)) gives ARB.
   list_to_bij (bij_to_list n (f on count n)) = f on (count n)
*)
Theorem list_to_bij_to_list_eq:
  !f n. list_to_bij (bij_to_list n (f on count n)) = (f on count n)
Proof
  rw[list_to_bij_def, bij_to_list_def, on_def, FUN_EQ_THM] >>
  rw[EL_MAP, listRangeLHI_EL]
QED

(* Theorem: f IN fun_count n n ==> list_to_bij (bij_to_list n f) = f *)
(* Proof:
   Note ?g. f = g on (count n)                 by fun_count_element
   Thus list_to_bij (bij_to_list n f) = f      by list_to_bij_to_list_eq
*)
Theorem list_to_bij_to_list_thm:
  !f n. f IN fun_count n n ==> list_to_bij (bij_to_list n f) = f
Proof
  rw[fun_count_element] >>
  simp[list_to_bij_to_list_eq]
QED

(* Theorem: f IN fun_count n n /\ g IN fun_count n n ==>
            bij_to_list n (f o g) = (bij_to_list n f oo bij_to_list n g) n *)
(* Proof:
   Let l1 = MAP f [0 ..< n],
       l2 = MAP g [0 ..< n].
     (bij_to_list n f oo bij_to_list n g) n
   = (l1 oo l2) n                                      by bij_to_list_def
   = bij_to_list n (list_to_bij l1 o list_to_bij l2)   by list_op_def
   = MAP (list_to_bij l1) o list_to_bij l2) [0 ..< n]  by bij_to_list_def
   = MAP (f o g) [0 ..< n]                             by list_to_bij_to_list_thm
   = bij_to_list n (f o g)                             by bij_to_list_def
*)
Theorem bij_to_list_compose:
  !f g n. f IN fun_count n n /\ g IN fun_count n n ==>
          bij_to_list n (f o g) = (bij_to_list n f oo bij_to_list n g) n
Proof
  simp[bij_to_list_def, list_op_def, list_to_bij_to_list_thm]
QED

(* Theorem: MonoidHomo (bij_to_list n) (symmetric_group (count n)) (permutation_group n) *)
(* Proof:
   By MonoidHomo_def, symmetric_group_def, permutation_group_def, this is to show:
   (1) x IN bij_maps (count n) ==> bij_to_list n x IN perm_count n
       Note IMAGE (bij_to_list n) (bij_count n) SUBSET perm_count n
                                                   by bij_to_list_image_subset
        and bij_maps (count n) = bij_count n       by bij_maps_bij_count
       Hence true                                  by SUBSET_DEF, IN_IMAGE
   (2) x IN bij_maps (count n) /\ y IN bij_maps (count n) ==>
       bij_to_list n (x o y on count n) = (bij_to_list n x oo bij_to_list n y) n
       Note x IN fun_count n n                     by bij_maps_element_alt
        and y IN fun_count n n                     by bij_maps_element_alt
         bij_to_list n (x o y on count n)
       = bij_to_list n (x o y)                     by bij_to_list_on_count
       = (bij_to_list n x oo bij_to_list n y) n    by bij_to_list_compose
   (3) bij_to_list n (I on count n) = [0 ..< n]
         bij_to_list n (I on count n)
       = bij_to_list n I                           by bij_to_list_on_count
       = MAP I [0 ..< n]                           by bij_to_list_def
       = [0 ..< n]                                 by MAP_ID
*)
Theorem bij_to_list_map_homo:
  !n. MonoidHomo (bij_to_list n) (symmetric_group (count n)) (permutation_group n)
Proof
  rw[MonoidHomo_def, symmetric_group_def, permutation_group_def] >-
  metis_tac[bij_to_list_image_subset, bij_maps_bij_count, SUBSET_DEF, IN_IMAGE] >-
 (fs[bij_maps_element_alt] >>
  simp[GSYM bij_to_list_on_count] >>
  simp[bij_to_list_compose]) >>
  simp[GSYM bij_to_list_on_count, bij_to_list_def]
QED

(* Theorem: MonoidIso (bij_to_list n) (symmetric_group (count n)) (permutation_group n) *)
(* Proof:
   Let f = bij_to_list n,
       g = symmetric_group (count n),
       h = permutation_group n.
   Note MonoidHomo f g h                 by bij_to_list_map_homo
    Now g.carrier = bij_count n          by symmetric_group_carrier, bij_maps_bij_count
    and h.carrier = perm_count n         by permutation_group_carrier
    and BIJ f g.carrier h.carrier        by bij_count_map_bij_alt
     so MonoidIso f g h                  by MonoidIso_def
*)
Theorem bij_to_list_map_iso:
  !n. MonoidIso (bij_to_list n) (symmetric_group (count n)) (permutation_group n)
Proof
  rpt strip_tac >>
  assume_tac bij_to_list_map_homo >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  qabbrev_tac `f = bij_to_list n` >>
  qabbrev_tac `g = symmetric_group (count n)` >>
  qabbrev_tac `h = permutation_group n` >>
  `BIJ f g.carrier h.carrier` by rw[bij_count_map_bij_alt, symmetric_group_carrier, bij_maps_bij_count, permutation_group_carrier, Abbr`f`, Abbr`g`, Abbr`h`] >>
  simp[MonoidIso_def]
QED

(* Theorem: Group (permutation_group n) *)
(* Proof:
   Let f = bij_to_list n,
       g = symmetric_group (count n),
       h = permutation_group n.
   Note h = homo_image f g h       by permutation_group_homo_image
    and MonoidHomo f g h           by bij_to_list_map_homo
    and Group g                    by symmetric_group_group
     so Group h                    by group_homo_homo_image_group
*)
Theorem permutation_group_group:
  !n. Group (permutation_group n)
Proof
  metis_tac[permutation_group_homo_image, bij_to_list_map_homo,
            symmetric_group_group, group_homo_homo_image_group]
QED

(* Theorem: GroupIso (bij_to_list n) (symmetric_group (count n)) (permutation_group n) *)
(* Proof:
   Let f = bij_to_list n,
       g = symmetric_group (count n),
       h = permutation_group n.
   Note MonoidIso f g h            by bij_to_list_map_iso
     so GroupIso f g h             by group_iso_monoid_iso
*)
Theorem symmetric_group_iso_permutation_group:
  !n. GroupIso (bij_to_list n) (symmetric_group (count n)) (permutation_group n)
Proof
  metis_tac[bij_to_list_map_iso, group_iso_monoid_iso]
QED

(* Theorem: GroupIso (LINV (bij_to_list n) (bij_count n))
            (permutation_group n) (symmetric_group (count n)) *)
(* Proof:
   Let f = bij_to_list n,
       g = symmetric_group (count n),
       h = permutation_group n.
   Note GroupIso f g h                   by symmetric_group_iso_permutation_group
    Now Group g                          by symmetric_group_group
    and g.carrier = bij_count n          by symmetric_group_carrier, bij_maps_bij_count
     so GroupIso (LINV f g.carrier) h g  by group_iso_sym
*)
Theorem permutation_group_iso_symmetric_group:
  !n. GroupIso (LINV (bij_to_list n) (bij_count n))
               (permutation_group n) (symmetric_group (count n))
Proof
  metis_tac[symmetric_group_iso_permutation_group, group_iso_sym, symmetric_group_group, symmetric_group_carrier, bij_maps_bij_count]
QED

(* Note: this is not very useful, as (LINV f s) is not unique, as defined by:
LINV_DEF;
|- !f s t. INJ f s t ==> !x. x IN s ==> LINV f s (f x) = x: thm

This theorem is replaced later, thus not documented.
*)

(* Theorem: list_to_bij ls = (\j. EL j ls) on (count (LENGTH ls)) *)
(* Proof:
   Let f = (\j. EL j ls), n = LENGTH ls.
     f on (count n)
   = \j. if j IN (count n) then f j else ARB   by on_def
   = \j. if j < n then f j else ARB            by IN_COUNT
   = list_to_bij ls                            by list_to_bij_def
*)
Theorem list_to_bij_alt:
  !ls. list_to_bij ls = (\j. EL j ls) on (count (LENGTH ls))
Proof
  simp[list_to_bij_def, on_def]
QED

(* Theorem: list_to_bij ls = (list_to_bij ls) on (count (LENGTH ls)) *)
(* Proof:
   Let f = (\j. EL j ls), n = LENGTH ls.
     list_to_bij ls
   = f on (count n)                by list_to_bij_alt
   = f on (count n) on (count n)   by on_on
   = (list_to_bij ls) on (count n) by list_to_bij_alt
*)
Theorem list_to_bij_on_count:
  !ls. list_to_bij ls = (list_to_bij ls) on (count (LENGTH ls))
Proof
  simp[list_to_bij_alt, on_on]
QED

(* Theorem: IMAGE list_to_bij (perm_count n) SUBSET (bij_count n) *)
(* Proof:
   By bij_count_element, SUBSET_DEF, this is to show:
      !ls. ls IN perm_count n ==>
       ?f. list_to_bij ls = f on count n /\ f PERMUTES count n
   Note LENGTH ls = n                    by perm_count_element_length
   Let f = list_to_bij ls.
   Then f on count n = list_to_bij ls    by list_to_bij_on_count
    and f PERMUTES count n               by list_to_bij_count_bij
*)
Theorem list_to_bij_image_subset:
  !n. IMAGE list_to_bij (perm_count n) SUBSET (bij_count n)
Proof
  rw[bij_count_element, SUBSET_DEF] >>
  imp_res_tac perm_count_element_length >>
  qexists_tac `list_to_bij x'` >>
  rw[list_to_bij_on_count] >>
  simp[list_to_bij_count_bij]
QED

(* Theorem: LENGTH l1 = n /\ LENGTH l2 = n /\ set l2 = count n ==>
            (l1 oo l2) n = MAP (\j. EL j l1) l2 *)
(* Proof:
     (l1 oo l2) n
   = bij_to_list n (list_to_bij l1 o list_to_bij l2)         by list_op_def
   = MAP (list_to_bij l1 o list_to_bij l2) [0 ..< n]         by bij_to_list_def
   = MAP (list_to_bij l1) (MAP (list_to_bij l2) [0 ..< n])   by MAP_COMPOSE
   = MAP (list_to_bij l1) l2                                 by map_list_to_bij_id
   = MAP ((\j. EL j l1) on (count n)) l2                     by list_to_bij_alt
   = MAP (\j. EL j l1) l2                                    by map_on_count_length
*)
Theorem list_op_thm:
  !l1 l2 n. LENGTH l1 = n /\ LENGTH l2 = n /\ set l2 = count n ==>
       (l1 oo l2) n = MAP (\j. EL j l1) l2
Proof
  rpt strip_tac >>
  qabbrev_tac `f = \j. EL j l1` >>
  `(l1 oo l2) n = bij_to_list n (list_to_bij l1 o list_to_bij l2)` by rw[list_op_def] >>
  `_ = MAP (list_to_bij l1 o list_to_bij l2) [0 ..< n]` by rw[bij_to_list_def] >>
  `_ = MAP (list_to_bij l1) (MAP (list_to_bij l2) [0 ..< n])` by rw[MAP_COMPOSE] >>
  `_ = MAP (list_to_bij l1) l2` by rw[map_list_to_bij_id] >>
  `_ = MAP (f on (count n)) l2` by rw[list_to_bij_alt, Abbr`f`] >>
  `_ = MAP f l2` by rw[GSYM map_on_count_length] >>
  simp[]
QED

(* Theorem: LENGTH l1 = n /\ LENGTH l2 = n /\ set l2 = count n /\
            j < n ==> EL j ((l1 oo l2) n) = EL (EL j l2) l1 *)
(* Proof:
     EL j ((l1 oo l2) n)
   = EL j (MAP (\j. EL j l1) l2)   by list_op_thm
   = (\j. EL j l1) (EL j l2)       by EL_MAP, j < n
   = EL (EL j l2) l1               by function application
*)
Theorem list_op_el:
  !l1 l2 n j. LENGTH l1 = n /\ LENGTH l2 = n /\ set l2 = count n /\
              j < n ==> EL j ((l1 oo l2) n) = EL (EL j l2) l1
Proof
  simp[list_op_thm, EL_MAP]
QED

(* Theorem: LENGTH l1 = n /\ LENGTH l2 = n /\
            set l2 = count n ==> LENGTH ((l1 oo l2) n) = n *)
(* Proof:
     LENGTH ((l1 oo l2) n)
   = LENGTH (MAP (\j. EL j l1) l2) by list_op_thm
   = LENGTH l2                     by LENGTH_MAP
   = n                             by given
*)
Theorem list_op_length:
  !l1 l2 n. LENGTH l1 = n /\ LENGTH l2 = n /\
            set l2 = count n ==> LENGTH ((l1 oo l2) n) = n
Proof
  simp[list_op_thm]
QED

(* Theorem: LENGTH l1 = n /\ LENGTH l2 = n /\ set l2 = count n /\
            ALL_DISTINCT l1 /\ ALL_DISTINCT l2 ==> ALL_DISTINCT ((l1 oo l2) n) *)
(* Proof:
   Let f = \j. EL j l1.
   Note INJ f (count n) univ(:num)             by all_distinct_list_el_inj
     or INJ f (set l2) univ(:num)              by set l2 = count n
    and !x. MEM x l2 <=> x < n                 by set l2 = count n
   Thus !x y. MEM x l2 /\ MEM y l2 /\
              f x = f y ==> x = y              by INJ_DEF [1]
       ALL_DISTINCT l2
   ==> ALL_DISTINCT (MAP (\j. EL j l1) l2)     by ALL_DISTINCT_MAP_INJ, [1]
   <=> ALL_DISTINCT ((l1 oo l2) n)             by list_op_thm
*)
Theorem list_op_all_distinct:
  !l1 l2 n. LENGTH l1 = n /\ LENGTH l2 = n /\ set l2 = count n /\
             ALL_DISTINCT l1 /\ ALL_DISTINCT l2 ==> ALL_DISTINCT ((l1 oo l2) n)
Proof
  rpt strip_tac >>
  pop_assum mp_tac >>
  imp_res_tac all_distinct_list_el_inj >>
  qabbrev_tac `f = \j. EL j l1` >>
  fs[INJ_DEF] >>
  rfs[list_op_thm, ALL_DISTINCT_MAP_INJ]
QED

(* Theorem: LENGTH l1 = n /\ LENGTH l2 = n /\
            set l2 = count n ==> set ((l1 oo l2) n) = set l1 *)
(* Proof:
   Let f = \j. EL j l1.
     set ((l1 oo l2) n)
   = set (MAP f l2)            by list_op_thm
   = IMAGE f (set l2)          by LIST_TO_SET_MAP
   = IMAGE f (count n)         by set l2 = count n
   = set l1                    by list_to_set_eq_el_image
*)
Theorem list_op_set:
  !l1 l2 n. LENGTH l1 = n /\ LENGTH l2 = n /\
            set l2 = count n ==> set ((l1 oo l2) n) = set l1
Proof
  metis_tac[list_op_thm, LIST_TO_SET_MAP, list_to_set_eq_el_image]
QED

(* Note:
perm_count_element
|- !ls n. ls IN perm_count n <=> ALL_DISTINCT ls /\ set ls = count n
perm_count_element_length
|- !ls n. ls IN perm_count n ==> LENGTH ls = n
*)

(* Theorem: l1 IN (perm_count n) /\ l2 IN (perm_count n) ==>
            ((l1 oo l2) n) IN (perm_count n) /\
            (l1 oo l2) n = MAP (\j. EL j l1) l2 *)
(* Proof:
   Note LENGTH l1 = n /\ LENGTH l2 = n         by perm_count_element_length
    and ALL_DISTINCT l1 /\ ALL_DISTINCT l2     by perm_count_element
    and set l1 = count n /\ set l2 = count n   by perm_count_element
   Thus ALL_DISTINCT ((l1 oo l2) n)            by list_op_all_distinct
    and set ((l1 oo l2) n) = count n           by list_op_set
    ==> ((l1 oo l2) n) IN (perm_count n)       by perm_count_element
    and (l1 oo l2) n = MAP (\j. EL j l1) l2    by list_op_thm
*)
Theorem perm_count_list_op:
  !l1 l2 n. l1 IN (perm_count n) /\ l2 IN (perm_count n) ==>
            ((l1 oo l2) n) IN (perm_count n) /\ (* closure *)
            (l1 oo l2) n = MAP (\j. EL j l1) l2
Proof
  ntac 4 strip_tac >>
  imp_res_tac perm_count_element_length >>
  imp_res_tac perm_count_element >>
  `ALL_DISTINCT ((l1 oo l2) n)` by fs[list_op_all_distinct] >>
  `set ((l1 oo l2) n) = count n` by fs[list_op_set] >>
  simp[perm_count_element, list_op_thm]
QED

(* Obtain individual theorems. *)

(* Theorem: l1 IN (perm_count n) /\ l2 IN (perm_count n) ==>
            ((l1 oo l2) n) IN (perm_count n) *)
(* Proof: by perm_count_list_op. *)
Theorem perm_count_list_op_closure:
  !l1 l2 n. l1 IN (perm_count n) /\ l2 IN (perm_count n) ==>
            ((l1 oo l2) n) IN (perm_count n)
Proof
  simp[perm_count_list_op]
QED

(* Theorem: l1 IN (perm_count n) /\ l2 IN (perm_count n) ==>
            (l1 oo l2) n = MAP (\j. EL j l1) l2 *)
(* Proof: by perm_count_list_op. *)
Theorem perm_count_list_op_thm:
  !l1 l2 n. l1 IN (perm_count n) /\ l2 IN (perm_count n) ==>
            (l1 oo l2) n = MAP (\j. EL j l1) l2
Proof
  simp[perm_count_list_op]
QED

(* Theorem: l1 IN (perm_count n) /\ l2 IN (perm_count n) /\ j < n ==>
            EL j ((l1 oo l2) n) = EL (EL j l2) l1 *)
(* Proof:
   Note LENGTH l2 = n              by perm_count_element_length
     EL j ((l1 oo l2) n)
   = EL j (MAP (\j. EL j l1) l2)   by perm_count_list_op
   = (\j. EL j l1) (EL j l2)       by EL_MAP, j < n
   = EL (EL j l2) l1               by function application
*)
Theorem perm_count_list_op_el:
  !l1 l2 n j. l1 IN (perm_count n) /\ l2 IN (perm_count n) /\ j < n ==>
              EL j ((l1 oo l2) n) = EL (EL j l2) l1
Proof
  rpt strip_tac >>
  imp_res_tac perm_count_element_length >>
  simp[perm_count_list_op, EL_MAP]
QED

(* Theorem: l1 IN (perm_count n) /\ l2 IN (perm_count n) ==>
            (l1 oo l2) n = MAP (\j. EL j l1) l2 *)
(* Proof: by perm_count_list_op, perm_count_element. *)
Theorem perm_count_list_op_all_distinct:
  !l1 l2 n. l1 IN (perm_count n) /\ l2 IN (perm_count n) ==>
            ALL_DISTINCT ((l1 oo l2) n)
Proof
  metis_tac[perm_count_list_op, perm_count_element]
QED

(* Theorem: l1 IN (perm_count n) /\ l2 IN (perm_count n) ==>
            set ((l1 oo l2) n) = count n *)
(* Proof: by perm_count_list_op, perm_count_element. *)
Theorem perm_count_list_op_set:
  !l1 l2 n. l1 IN (perm_count n) /\ l2 IN (perm_count n) ==>
            set ((l1 oo l2) n) = count n
Proof
  metis_tac[perm_count_list_op, perm_count_element]
QED

(* Theorem: l1 IN (perm_count n) /\ l2 IN (perm_count n) ==>
            LENGTH ((l1 oo l2) n) = n *)
(* Proof: by perm_count_list_op, perm_count_element_length. *)
Theorem perm_count_list_op_length:
  !l1 l2 n. l1 IN (perm_count n) /\ l2 IN (perm_count n) ==>
            LENGTH ((l1 oo l2) n) = n
Proof
  metis_tac[perm_count_list_op, perm_count_element_length]
QED

(* Theorem: ls IN (perm_count n) ==> INJ (\j. EL j ls) (count n) (count n) *)
(* Proof:
   Note LENGTH ls = n              by perm_count_element_length
    and ALL_DISTINCT ls /\
        set ls = count n           by perm_count_element
   By INJ_DEF, this is to show:
   (1) j < LENGTH ls ==> EL j ls < LENGTH ls
       Note MEM (EL j ls) ls       by EL_MEM
         so EL j ls IN (count n)   by set ls = count n
         or EL j ls < n            by IN_COUNT
   (2) j < LENGTH ls /\ k < LENGTH ls /\ EL j ls = EL k ls ==> j = k
       This is true                by ALL_DISTINCT_EL_IMP
*)
Theorem perm_count_list_el_inj:
  !ls n. ls IN (perm_count n) ==> INJ (\j. EL j ls) (count n) (count n)
Proof
  rpt strip_tac >>
  imp_res_tac perm_count_element_length >>
  fs[perm_count_def] >>
  rw[INJ_DEF] >| [
    `MEM (EL j ls) ls` by rw[EL_MEM] >>
    rfs[],
    rfs[ALL_DISTINCT_EL_IMP]
  ]
QED

(* Theorem: list_to_bij (MAP f ls) = (\j. f (EL j ls)) on (count (LENGTH ls)) *)
(* Proof:
    Let n = LENGTH ls
      list_to_bij (MAP f ls)
    = (\j. EL j (MAP f ls)) on (count n)  by list_to_bij_alt
    = (\j. f (EL j ls)) on (count n)      by EL_MAP, on_def
*)
Theorem list_to_bij_map_thm:
  !f ls. list_to_bij (MAP f ls) = (\j. f (EL j ls)) on (count (LENGTH ls))
Proof
  rw[list_to_bij_alt, on_def, FUN_EQ_THM] >>
  metis_tac[EL_MAP]
QED

(* Theorem: l1 IN perm_count n /\ l2 IN perm_count n ==>
            list_to_bij ((l1 oo l2) n) = (list_to_bij l1 o list_to_bij l2) on count n *)
(* Proof:
   Note LENGTH l1 = n /\ LENGTH l2 = n         by perm_count_element_length
   Let f = \j. EL j l1, g = \j. EL j l2, s = count n.
   Then INJ g s s                              by perm_count_list_el_inj
     or over g s s                             by over_inj
     list_to_bij ((l1 oo l2) n)
   = list_to_bij (MAP f l2)                    by perm_count_list_op
   = (\k. f (EL k l2)) on s                    by list_to_bij_map_thm
   = (f o g) on s                              by o_THM, FUN_EQ_THM
   = ((f on s) o (g on s)) on s                by on_on_compose, over g s s
   = (list_to_bij l1 o list_to_bij l2) on s    by list_to_bij_alt
*)
Theorem list_to_bij_compose:
  !l1 l2 n. l1 IN perm_count n /\ l2 IN perm_count n ==>
            list_to_bij ((l1 oo l2) n) = (list_to_bij l1 o list_to_bij l2) on count n
Proof
  rpt strip_tac >>
  imp_res_tac perm_count_element_length >>
  qabbrev_tac `f = \j. EL j l1` >>
  qabbrev_tac `g = \k. EL k l2` >>
  qabbrev_tac `s = count n` >>
  `f o g = \k. f (EL k l2)` by rw[FUN_EQ_THM, Abbr`g`] >>
  `INJ g s s` by rw[perm_count_list_el_inj, FUN_EQ_THM, Abbr`g`, Abbr`s`] >>
  `over g s s` by metis_tac[over_inj] >>
  `list_to_bij ((l1 oo l2) n) = list_to_bij (MAP f l2)` by rw[perm_count_list_op, Abbr`f`] >>
  `_ = (f o g) on s` by rw[list_to_bij_map_thm, Abbr`s`] >>
  `_ = ((f on s) o (g on s)) on s` by rw[on_on_compose] >>
  simp[list_to_bij_alt, Abbr`f`, Abbr`g`]
QED

(* Theorem: list_to_bij [0 ..< n] = I on count n *)
(* Proof:
   Let ls = [0 ..< n],
   Then LENGTH ls = n              by listRangeLHI_LEN
     list_to_bij ls
   = (\j. EL j ls) on count n      by list_to_bij_alt
   = (\j. j) on count n            by listRangeLHI_EL, IN_COUNT, FUN_EQ_THM
   = I on count n                  by I_THM
*)
Theorem list_to_bij_id_thm:
  !n. list_to_bij [0 ..< n] = I on count n
Proof
  rpt strip_tac >>
  qabbrev_tac `ls = [0 ..< n]` >>
  `LENGTH ls = n` by rw[listRangeLHI_LEN, Abbr`ls`] >>
  `(\j. EL j ls) on count n = I on count n` by rw[on_def, listRangeLHI_EL, FUN_EQ_THM, Abbr`ls`] >>
  simp[list_to_bij_alt]
QED

(* Theorem: MonoidHomo list_to_bij (permutation_group n) (symmetric_group (count n)) *)
(* Proof:
   By MonoidHomo_def, permutation_group_def, symmetric_group_def, this is to show:
   (1) x IN perm_count n ==> list_to_bij x IN bij_maps (count n)
       Note IMAGE list_to_bij (perm_count n) SUBSET bij_count n
                                               by list_to_bij_image_subset
        and bij_maps (count n) = bij_count n   by bij_maps_bij_count
       Hence true                              by SUBSET_DEF, IN_IMAGE
   (2) x IN perm_count n /\ y IN perm_count n ==>
       list_to_bij ((x oo y) n) = list_to_bij x o list_to_bij y on count n
       This is true                            by list_to_bij_compose
   (3) list_to_bij [0 ..< n] = I on count n
       This is true                            by list_to_bij_id_thm
*)
Theorem list_to_bij_map_homo:
  !n. MonoidHomo list_to_bij (permutation_group n) (symmetric_group (count n))
Proof
  rw[MonoidHomo_def, permutation_group_def, symmetric_group_def] >-
  metis_tac[bij_maps_bij_count, list_to_bij_image_subset, SUBSET_DEF, IN_IMAGE] >-
  simp[list_to_bij_compose] >>
  simp[list_to_bij_id_thm]
QED

(* Theorem: INJ list_to_bij (perm_count n) (bij_count n) *)
(* Proof:
   By INJ_DEF, this is to show:
   (1) x IN perm_count n ==> list_to_bij x IN bij_count n
       Note IMAGE list_to_bij (perm_count n) SUBSET (bij_count n)  by list_to_bij_image_subset
       Hence x IN perm_count n ==> list_to_bij x IN bij_count n    by SUBSET_DEF, IN_IMAGE
   (2) x IN perm_count n /\ y IN perm_count n /\ list_to_bij x = list_to_bij y ==> x = y
       Note LENGTH x = n /\ LENGTH y = n       by perm_count_element_length
        and !j. j < n ==> EL j x = EL j y      by list_to_bij_def, IN_COUNT
       Thus x = y                              by LIST_EQ
*)
Theorem list_to_bij_perm_count_inj:
  !n. INJ list_to_bij (perm_count n) (bij_count n)
Proof
  rw[INJ_DEF] >-
  metis_tac[list_to_bij_image_subset, SUBSET_DEF, IN_IMAGE] >>
  imp_res_tac perm_count_element_length >>
  fs[list_to_bij_def] >>
  `!j. j < n ==> EL j x = EL j y` by metis_tac[] >>
  simp[LIST_EQ]
QED

(* Theorem: INJ f (count n) (count n) ==> ALL_DISTINCT (bij_to_list n f) *)
(* Proof:
   Let ls = [0 ..< n].
   Then ALL_DISTINCT ls                  by listRangeLHI_ALL_DISTINCT
    and !x. MEM x ls <=> x < n           by listRangeLHI_MEM
   Thus !x y. MEM x ls /\ MEM y ls /\ f x = f y ==> x = y
                                         by INJ_DEF, IN_COUNT
    ==> ALL_DISTINCT (MAP f ls)          by ALL_DISTINCT_MAP_INJ
     or ALL_DISTINCT (bij_to_list n f)   by bij_to_list_def
*)
Theorem bij_to_list_inj_all_distinct:
  !f n. INJ f (count n) (count n) ==> ALL_DISTINCT (bij_to_list n f)
Proof
  rw[bij_to_list_def] >>
  fs[INJ_DEF] >>
  rfs[ALL_DISTINCT_MAP_INJ]
QED

(* Theorem: SURJ f (count n) (count n) ==> set (bij_to_list n f) = count n *)
(* Proof:
     set (bij_to_list n f)
   = set (MAP f [0 ..< n])   by bij_to_list_def
   = IMAGE f (set [0 ..< n]) by LIST_TO_SET_MAP
   = IMAGE f (count n)       by listRangeLHI_SET
   = count n                 by IMAGE_SURJ
*)
Theorem bij_to_list_surj_set:
  !f n. SURJ f (count n) (count n) ==> set (bij_to_list n f) = count n
Proof
  simp[bij_to_list_def, LIST_TO_SET_MAP, listRangeLHI_SET, IMAGE_SURJ]
QED

(* Theorem: (bij_count n) SUBSET IMAGE list_to_bij (perm_count n) *)
(* Proof:
   By perm_count_def, SUBSET_DEF, this is to show:
      !x. x IN bij_count n ==>
     ?ls. x = list_to_bij ls /\ ALL_DISTINCT ls /\ set ls = count n
   Note ?f. x = f on count n /\ f PERMUTES count n
                                   by bij_count_element
   Note INJ x (count n) (count n)  by BIJ_DEF, on_bij
    and SURJ x (count n) (count n) by BIJ_DEF, on_bij
   Let ls = bij_to_list n x.
   Then list_to_bij ls = x         by list_to_bij_to_list_eq
    and ALL_DISTINCT ls            by bij_to_list_inj_all_distinct
    and set ls = count n           by bij_to_list_surj_set
*)
Theorem list_to_bij_image_superset:
  !n. (bij_count n) SUBSET IMAGE list_to_bij (perm_count n)
Proof
  rw[perm_count_def, SUBSET_DEF] >>
  fs[bij_count_element] >>
  qexists_tac `bij_to_list n x` >>
  simp[list_to_bij_to_list_eq] >>
  metis_tac[bij_to_list_inj_all_distinct, bij_to_list_surj_set, BIJ_DEF, on_bij]
QED

(* Theorem: bij_count n = IMAGE list_to_bij (perm_count n) *)
(* Proof:
   Let s = bij_count n,
       t = IMAGE list_to_bij (perm_count n).
   Note s SUBSET t         by list_to_bij_image_subset
    and t SUBSET s         by list_to_bij_image_superset
   Thus s = t              by SUBSET_ANTISYM
*)
Theorem list_to_bij_image_thm:
  !n. bij_count n = IMAGE list_to_bij (perm_count n)
Proof
  simp[list_to_bij_image_subset, list_to_bij_image_superset, SUBSET_ANTISYM]
QED

(* Theorem: SURJ list_to_bij (perm_count n) (bij_count n) *)
(* Proof:
   By SURJ_DEF, this is to show:
   (1) x IN perm_count n ==> list_to_bij x IN bij_count n
       Note IMAGE list_to_bij (perm_count n) SUBSET (bij_count n)  by list_to_bij_image_subset
       Hence x IN perm_count n ==> list_to_bij x IN bij_count n    by SUBSET_DEF, IN_IMAGE
   (2) x IN bij_count n ==> ?y. y IN perm_count n /\ list_to_bij y = x
       Let y = bij_to_list n x.
       Then y IN perm_count n      by bij_to_list_image_subset, SUBSET_DEF, IN_IMAGE
       Note ?f. x = f on (count n) by bij_count_element
         so list_to_bij y = x      by list_to_bij_to_list_eq
*)
Theorem list_to_bij_perm_count_surj:
  !n. SURJ list_to_bij (perm_count n) (bij_count n)
Proof
  rw[SURJ_DEF] >-
  metis_tac[list_to_bij_image_subset, SUBSET_DEF, IN_IMAGE] >>
  qexists_tac `bij_to_list n x` >>
  rpt strip_tac >-
  metis_tac[bij_to_list_image_subset, SUBSET_DEF, IN_IMAGE] >>
  fs[list_to_bij_to_list_eq, bij_count_element]
QED

(* Theorem: BIJ list_to_bij (perm_count n) (bij_count n) *)
(* Proof:
   Note  INJ list_to_bij (perm_count n) (bij_count n)  by list_to_bij_perm_count_inj
    and SURJ list_to_bij (perm_count n) (bij_count n)  by list_to_bij_perm_count_surj
     so  BIJ list_to_bij (perm_count n) (bij_count n)  by BIJ_DEF
*)
Theorem list_to_bij_perm_count_bij:
  !n. BIJ list_to_bij (perm_count n) (bij_count n)
Proof
  simp[BIJ_DEF, list_to_bij_perm_count_inj, list_to_bij_perm_count_surj]
QED

(* Theorem: MonoidIso list_to_bij (permutation_group n) (symmetric_group (count n)) *)
(* Proof:
   Let f = list_to_bij,
       g = permutation_group n,
       h = symmetric_group (count n).
   Then MonoidHomo f g h           by list_to_bij_map_homo
    Now g.carrier = perm_count n   by permutation_group_carrier
    and h.carrier = bij_count n    by symmetric_group_carrier, bij_maps_bij_count
    and BIJ f g.carrier h.carrier  by list_to_bij_perm_count_bij
     so MonioidIso f g h           by MonoidIso_def
*)
Theorem list_to_bij_map_iso:
  !n. MonoidIso list_to_bij (permutation_group n) (symmetric_group (count n))
Proof
  rpt strip_tac >>
  assume_tac list_to_bij_map_homo >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  qabbrev_tac `g = permutation_group n` >>
  qabbrev_tac `h = symmetric_group (count n)` >>
  `g.carrier = perm_count n` by rw[permutation_group_carrier, Abbr`g`] >>
  `h.carrier = bij_count n` by fs[symmetric_group_carrier, bij_maps_bij_count, Abbr`h`] >>
  simp[list_to_bij_perm_count_bij, MonoidIso_def]
QED

(* Theorem: GroupIso list_to_bij (permutation_group n) (symmetric_group (count n)) *)
(* Proof: by list_to_bij_map_iso, group_iso_monoid_iso. *)
Theorem permutation_group_iso_symmetric_group[allow_rebind]:
  !n. GroupIso list_to_bij (permutation_group n) (symmetric_group (count n))
Proof
  metis_tac[list_to_bij_map_iso, group_iso_monoid_iso]
QED

(* This is much better than the previous one:
!n. GroupIso (LINV (bij_to_list n) (bij_count n))
               (permutation_group n) (symmetric_group (count n))
*)

(* Theorem: 0 ..< n] IN perm_count n *)
(* Proof:
   Note ALL_DISTINCT [0 ..< n]     by listRangeLHI_ALL_DISTINCT
    and set [0 ..< n] = count n    by listRangeLHI_SET
   Thus [0 ..< n] IN perm_count n  by perm_count_element
*)
Theorem perm_count_has_id:
  !n. [0 ..< n] IN perm_count n
Proof
  simp[perm_count_element, listRangeLHI_SET]
QED

(* Theorem: ls IN perm_count n ==> ([0 ..< n] oo ls) n = ls *)
(* Proof:
   Let t = [0 ..< n].
   Then t IN perm_count n                by perm_count_has_id
    and (t oo ls) n IN perm_count n      by perm_count_list_op_closure
     so LENGTH ls = n                    by perm_count_element_length
     so LENGTH ((t oo ls) n) = n         by perm_count_element_length
   Also set ls = count n                 by perm_count_element
     so !x. x < n ==> EL x ls < n        by set_list_eq_count
   By LIST_EQ, it remains to show:
     !x. x < n ==> EL x ((t oo ls) n) = EL x ls

     EL x ((t oo ls) n)
   = EL (EL x ls) t                      by perm_count_list_op_el
   = EL x ls                             by listRangeLHI_EL, EL x ls < n
*)
Theorem perm_count_list_op_lid:
  !ls n. ls IN perm_count n ==> ([0 ..< n] oo ls) n = ls
Proof
  rpt strip_tac >>
  qabbrev_tac `t = [0 ..< n]` >>
  `t IN perm_count n` by rw[perm_count_has_id, Abbr`t`] >>
  `(t oo ls) n IN perm_count n` by rw[perm_count_list_op_closure] >>
  imp_res_tac perm_count_element_length >>
  `set ls = count n` by fs[perm_count_element] >>
  irule LIST_EQ >>
  simp[] >>
  rpt strip_tac >>
  `EL x ls < n` by fs[set_list_eq_count] >>
  simp[perm_count_list_op_el, listRangeLHI_EL, Abbr`t`]
QED

(* Theorem: ls IN perm_count n ==> (ls oo [0 ..< n]) n = ls *)
(* Proof:
   Let t = [0 ..< n].
   Then t IN perm_count n                by perm_count_has_id
   Note set t = count n                  by perm_count_element
    and LENGTH t = n                     by perm_count_element_length
     (ls oo t) n
   = MAP (\j. EL j ls) t                 by perm_count_list_op_thm
   = MAP ((\j. EL j ls) on count n) t    by map_on_count_length
   = MAP (list_to_bij ls) t              by list_to_bij_alt
   = ls                                  by map_list_to_bij_id
*)
Theorem perm_count_list_op_rid:
  !ls n. ls IN perm_count n ==> (ls oo [0 ..< n]) n = ls
Proof
  rpt strip_tac >>
  qabbrev_tac `t = [0 ..< n]` >>
  `t IN perm_count n` by rw[perm_count_has_id, Abbr`t`] >>
  imp_res_tac perm_count_element_length >>
  imp_res_tac perm_count_element >>
  simp[perm_count_list_op_thm] >>
  metis_tac[map_on_count_length, list_to_bij_alt, map_list_to_bij_id]
QED

(* Theorem: l1 IN perm_count n /\ l2 IN perm_count n /\ l3 IN perm_count n ==>
            (((l1 oo l2) n) oo l3) n = (l1 oo (l2 oo l3) n) n *)
(* Proof:
   Note (l1 oo l2) n IN perm_count n           by perm_count_list_op_closure
    and (l2 oo l3) n IN perm_count n           by perm_count_list_op_closure
   Thus LENGTH ((((l1 oo l2) n) oo l3) n) = n  by perm_count_list_op_length
    and LENGTH ((l1 oo (l2 oo l3) n) n) = n    by perm_count_list_op_length
   By LIST_EQ, it remains to show:
      !x. EL x (((l1 oo l2) n) oo l3) n = EL x (l1 oo (l2 oo l3) n) n
   Note set l3 = count n                       by perm_count_element
     so EL x l3 < n                            by set_list_eq_count
     EL x (((l1 oo l2) n) oo l3) n
   = EL (EL x l3) (l1 oo l2) n)                by perm_count_list_op_el
   = EL (EL (EL x l3) l2) l1                   by perm_count_list_op_el
     EL x (l1 oo (l2 oo l3) n) n
   = EL (EL x ((l2 oo l3) n)) l1               by perm_count_list_op_el
   = EL (EL (EL x l3) l2) l1                   by perm_count_list_op_el

   Therefore,
     (((l1 oo l2) n) oo l3) n = (l1 oo (l2 oo l3) n) n by LIST_EQ
*)
Theorem perm_count_list_op_assoc:
  !l1 l2 l3 n. l1 IN perm_count n /\ l2 IN perm_count n /\ l3 IN perm_count n ==>
               (((l1 oo l2) n) oo l3) n = (l1 oo (l2 oo l3) n) n
Proof
  rpt strip_tac >>
  imp_res_tac perm_count_element_length >>
  irule LIST_EQ >>
  simp[perm_count_list_op_closure, perm_count_list_op_length] >>
  rpt strip_tac >>
  `set l3 = count n` by fs[perm_count_element] >>
  `EL x l3 < n` by fs[set_list_eq_count] >>
  simp[perm_count_list_op_closure, perm_count_list_op_el]
QED

(* Investigation:

perm_count 3 = {[0; 1; 2]; [0; 2; 1]; [2; 0; 1]; [1; 0; 2]; [1; 2; 0]; [2; 1; 0]}

([0;2;1] oo [0;2;1]) 3 = [0;1;2]
([2;0;1] oo [1;2;0]) 3 = [0;1;2]
([1;0;2] oo [1;0;2]) 3 = [0;1;2]
([2;1;0] oo [2;1;0]) 3 = [0;1;2]
([0;1;2] oo [0;1;2]) 3 = [0;1;2]

findi 0 [1;2;0] = 2
findi 1 [1;2;0] = 0
findi 2 [1;2;0] = 1, so [2;0;1] is its inverse.

MAP (\j. findi j ls) [0 ..< n] is the inverse of ls.
*)

(* Define inverse list *)
Definition list_op_inv_def:
   list_op_inv ls = MAP (\j. findi j ls) [0 ..< (LENGTH ls)]
End

(*
EVAL ``list_op_inv [1;2;0]``; [2;0;1]
EVAL ``IMAGE list_op_inv (perm_count 3)``;
val it = |- IMAGE list_op_inv (perm_count 3) =
      {[0; 1; 2]; [0; 2; 1]; [1; 2; 0]; [1; 0; 2]; [2; 0; 1]; [2; 1; 0]}: thm
*)

(* Theorem: ls IN perm_count n ==> list_op_inv ls IN perm_count n *)
(* Proof:
   Let f = \j. findi j ls.
   Note LENGTH ls = n                          by perm_count_element_length
    and ALL_DISTINCT ls /\
        set ls = count n                       by perm_count_element
    and list_op_inv ls = MAP f [0 ..< n]       by list_op_inv_def
   By perm_count_element, this is to show:
   (1) ALL_DISTINCT (list_op_inv ls)
       Note !x y. MEM x ls /\ MEM y ls /\
                  f x = f y ==> x = y          by EL_findi
        and ALL_DISTINCT [0 ..< n]             by listRangeLHI_ALL_DISTINCT
       Thus ALL_DISTINCT (MAP f [0 ..< n])     by ALL_DISTINCT_MAP_INJ
   (2) set (list_op_inv ls) = count n
       Claim: SURJ f (count n) (count n)
       Proof: by SURJ_DEF, this is to show:
              (1) findi j ls < LENGTH ls, true by MEM_findi
              (2) ?j. j < LENGTH ls /\ findi j ls = x
                  Let j = EL x ls.
                  Then j < LENGTH ls           by set_list_eq_count
                   and findi j ls = x          by findi_EL

         set (list_op_inv ls)
       = set (MAP f [0 ..< n])                 by above
       = IMAGE f (set [0 ..< n])               by LIST_TO_SET_MAP
       = IMAGE f (count n)                     by listRangeLHI_SET
       = count n                               by IMAGE_SURJ
*)
Theorem perm_count_has_list_op_inv:
  !ls n. ls IN perm_count n ==> list_op_inv ls IN perm_count n
Proof
  rw[list_op_inv_def] >>
  imp_res_tac perm_count_element_length >>
  simp[] >>
  fs[perm_count_element] >>
  qabbrev_tac `f = \j. findi j ls` >>
  rpt strip_tac >| [
    `!x y. MEM x ls /\ MEM y ls /\ f x = f y ==> x = y` by metis_tac[indexedListsTheory.EL_findi] >>
    fs[ALL_DISTINCT_MAP_INJ],
    simp[LIST_TO_SET_MAP, listRangeLHI_SET] >>
    `SURJ f (count n) (count n)` by
  (rw[SURJ_DEF, Abbr`f`] >-
    simp[indexedListsTheory.MEM_findi] >>
    metis_tac[set_list_eq_count, indexedListsTheory.findi_EL]
    ) >>
    simp[GSYM IMAGE_SURJ]
  ]
QED

(* Theorem: ls IN perm_count n ==> (list_op_inv ls oo ls) n = [0 ..< n] *)
(* Proof:
   Let t = list_op_inv ls.
   Then t IN perm_count n          by perm_count_has_list_op_inv
    and [0 ..< n] IN perm_count n  by perm_count_has_id
     so LENGTH t = n               by perm_count_element_length
    and LENGTH [0 ..< n] = n       by perm_count_element_length
    and LENGTH ((t oo ls) n) = b   by perm_count_list_op_length
    and ALL_DISTINCT ls            by perm_count_element
   By LIST_EQ, it remains to show that:
     EL x ((t oo ls) n)
   = EL (EL x ls) t                by perm_count_list_op_el
   = EL (EL x ls) (MAP (\j. findi j ls) [0 ..< n])     by list_op_inv_def
   = (\j. findi j ls) (EL (EL x ls) [0 ..< n])         by EL_MAP, EL x ls < n
   = (\j. findi j ls) (EL x ls)    by listRangeLHI_EL
   = findi (EL x ls) ls            by function application
   = x                             by findi_EL
*)
Theorem perm_count_list_op_inv:
  !ls n. ls IN perm_count n ==> (list_op_inv ls oo ls) n = [0 ..< n]
Proof
  rpt strip_tac >>
  qabbrev_tac `t = list_op_inv ls` >>
  qabbrev_tac `i = [0 ..< n]` >>
  `i IN perm_count n` by rw[perm_count_has_id, Abbr`i`] >>
  `t IN perm_count n` by rw[perm_count_has_list_op_inv, Abbr`t`] >>
  `(t oo ls) n IN perm_count n` by rw[perm_count_list_op_closure] >>
  imp_res_tac perm_count_element_length >>
  irule LIST_EQ >>
  simp[] >>
  rpt strip_tac >>
  simp[perm_count_list_op_el] >>
  `ALL_DISTINCT ls /\ set ls = count n` by fs[perm_count_element] >>
  `EL x ls < n` by rw[set_list_eq_count] >>
  fs[list_op_inv_def, listRangeLHI_EL, EL_MAP, Abbr`t`, Abbr`i`] >>
  simp[indexedListsTheory.findi_EL]
QED

(*
> type_of ``(permutation_group 3)``;
val it = ``:num list monoid``: hol_type
> type_of ``(permutation_group 3).op``;
val it = ``:num list -> num list -> num list``: hol_type
> type_of ``(permutation_group 3).id``;
val it = ``:num list``: hol_type
> type_of ``(permutation_group 3).inv``;
val it = ``:num list -> num list``: hol_type
*)

(* Theorem: (permutation_group n).inv ls =
            if ls IN perm_count n then list_op_inv ls
            else FAIL ((permutation_group n).inv ls) bad_element *)
(* Proof:
   Discard the FAIL part           by FAIL_DEF
   Let g = permutation_group n,
       t = list_op_inv ls.
   Then Group g                    by permutation_group_group
    and g.carrier = perm_count n   by permutation_group_carrier
    and t IN perm_count n          by perm_count_has_list_op_inv
    and (t oo ls) n = [0 ..< n]    by perm_count_list_op_inv
     or g.op t ls = g.id           by permutation_group_property
   Thus t = g.inv ls               by group_linv_unique
*)
Theorem permutation_group_inv[compute]:
  !ls n. (permutation_group n).inv ls =
         if ls IN perm_count n then list_op_inv ls
         else FAIL ((permutation_group n).inv ls) bad_element
Proof
  rw[combinTheory.FAIL_DEF] >>
  qabbrev_tac `g = permutation_group n` >>
  `Group g` by rw[permutation_group_group, Abbr`g`] >>
  `g.carrier = perm_count n` by rw[permutation_group_carrier, Abbr`g`] >>
  imp_res_tac perm_count_list_op_inv >>
  qabbrev_tac `t = list_op_inv ls` >>
  `t IN perm_count n` by rw[perm_count_has_list_op_inv, Abbr`t`] >>
  `g.op t ls = g.id` by metis_tac[permutation_group_property] >>
  metis_tac[group_linv_unique]
QED


(* A direct proof of  Group (permutation_group n) *)

(* Theorem: Group (permutation_group n) *)
(* Proof:
   By group_alt, permutation_group_property, this is to show:
   (1) x IN perm_count n /\ y IN perm_count n ==> (x oo y) n IN perm_count n
       This is true by perm_count_list_op_closure.
   (2) x IN perm_count n /\ y IN perm_count n /\ z IN perm_count n ==>
       ((x oo y) n oo z) n = (x oo (y oo z) n) n
       This is true by perm_count_list_op_assoc.
   (3) [0 ..< n] IN perm_count n
       This is true by perm_count_has_id.
   (4) x IN perm_count n ==> ([0 ..< n] oo x) n = x
       This is true by perm_count_list_op_lid.
   (5) x IN perm_count n ==> (permutation_group n).inv x IN perm_count n
       This is true by permutation_group_inv, perm_count_has_list_op_inv
   (6) x IN perm_count n ==> ((permutation_group n).inv x oo x) n = [0 ..< n]
       This is true by permutation_group_inv, perm_count_list_op_inv
*)
Theorem permutation_group_group[allow_rebind]:
  !n. Group (permutation_group n)
Proof
  rw_tac bool_ss[group_alt, permutation_group_property, RES_FORALL_THM] >-
  simp[perm_count_list_op_closure] >-
  simp[perm_count_list_op_assoc] >-
  simp[perm_count_has_id] >-
  simp[perm_count_list_op_lid] >-
  metis_tac[permutation_group_inv, perm_count_has_list_op_inv] >>
  metis_tac[permutation_group_inv, perm_count_list_op_inv]
QED


(* ------------------------------------------------------------------------- *)

(* export theory at end *)
val _ = export_theory();

(*===========================================================================*)
