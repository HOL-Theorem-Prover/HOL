Theory fmaptree
Ancestors
  finite_map pred_set
Libs
  BasicProvers boolSimps

(* an fmaptree is a type of tree, where branching is controlled by a
   finite-map.  The one constructor is

    FTNode : 'value -> ('key |-> ('key,'value)fmaptree)
                    -> ('key,'value)fmaptree

   This is rather like a trie.

   The type recurses under a finite map, which the datatype package
   builds directly: a finite map is a functor in its range, so the
   specification below is a fixed point like any other, and the
   constructor's injectivity, the exhaustion theorem, the recursion
   principle and the induction principle all come with it.

   There is an induction principle (ft_ind), where you are able to
   assume that your predicate P holds of every subtree.
*)

(* this specification recurses under a finite map, which the old
   construction cannot build and the BNF package behind Datatype can *)
Datatype: fmaptree = FTNode 'value ('key |-> fmaptree)
End

(* what the declaration saved, under the names the package gives them *)
fun saved s = DB.fetch "-" s
val fmaptree_11 = saved "fmaptree_11"
val fmaptree_nchotomy = saved "fmaptree_nchotomy"
val fmaptree_Axiom = saved "fmaptree_Axiom"
val fmaptree_induction = saved "fmaptree_induction"

Theorem FTNode_11[simp] = fmaptree_11

val item_map_def = new_specification("item_map_def",
  ["item", "map"],
  SIMP_RULE (srw_ss()) [SKOLEM_THM] fmaptree_nchotomy);

val (item_thm, map_thm) =
    CONJ_PAIR (GSYM (SIMP_RULE (srw_ss()) [FORALL_AND_THM]
                               (ISPEC ``FTNode i fm`` item_map_def)))
Theorem item_thm[simp] = item_thm
Theorem map_thm[simp] = map_thm

Definition apply_path_def:
  (apply_path [] ft = SOME ft) /\
  (apply_path (h::t) ft = if h IN FDOM (map ft) then apply_path t (map ft ' h)
                          else NONE)
End

Definition update_at_path_def:
  (update_at_path [] a ft = SOME (FTNode a (map ft))) /\
  (update_at_path (h::t) a ft =
     if h IN FDOM (map ft) then
       case update_at_path t a (map ft ' h) of
         NONE => NONE
       | SOME ft' => SOME (FTNode (item ft) (map ft |+ (h,ft')))
     else NONE)
End

Definition fupd_at_path_def:
  (fupd_at_path [] f ft = f ft) /\
  (fupd_at_path (h::t) f ft =
     if h IN FDOM (map ft) then
       case fupd_at_path t f (map ft ' h) of
         NONE => NONE
       | SOME ft' => SOME (FTNode (item ft) (map ft |+ (h, ft')))
     else NONE)
End

(* the package's induction principle says "for every sub-tree in the
   finite map's range"; this is the same thing said of the keys *)
Theorem ft_ind:
    !P. (!a fm. (!k. k IN FDOM fm ==> P (fm ' k)) ==> P (FTNode a fm)) ==>
        !ft. P ft
Proof
  gen_tac >> strip_tac >> ho_match_mp_tac fmaptree_induction >>
  rpt strip_tac >> last_x_assum irule >> rpt strip_tac >>
  first_x_assum irule >> simp[FRANGE_DEF] >> metis_tac[]
QED

Theorem list_GSPEC_cases[local]:
    { l | P l } = (if P [] then {[]} else {}) UNION
                  { h :: t | P (h :: t) }
Proof
  SRW_TAC [][EXTENSION, EQ_IMP_THM] THEN SRW_TAC [][] THEN
  Cases_on `x` THEN SRW_TAC [][] THEN FULL_SIMP_TAC (srw_ss()) []
QED

Theorem applicable_paths_FINITE:
    !ft. FINITE { p | ?ft'. apply_path p ft = SOME ft' }
Proof
  HO_MATCH_MP_TAC ft_ind THEN SRW_TAC [][] THEN
  CONV_TAC (RAND_CONV (HO_REWR_CONV list_GSPEC_cases)) THEN
  SRW_TAC [][apply_path_def] THEN
  SRW_TAC [COND_elim_ss, DNF_ss, CONJ_ss][] THEN
  Q.MATCH_ABBREV_TAC `FINITE s` THEN
  `s = BIGUNION (IMAGE (\k. IMAGE (CONS k)
                                  { p | ?ft'. apply_path p (fm ' k) =
                                              SOME ft' })
                       (FDOM fm))`
     by (SRW_TAC [DNF_ss][Once EXTENSION, Abbr`s`] THEN METIS_TAC []) THEN
  POP_ASSUM SUBST1_TAC THEN SRW_TAC [][] THEN SRW_TAC [][IMAGE_FINITE]
QED

Theorem apply_path_SNOC:
    !ft x p. apply_path (p ++ [x]) ft =
             case apply_path p ft of
               NONE => NONE
             | SOME ft' => FLOOKUP (map ft') x
Proof
  Induct_on `p` THEN
  SRW_TAC [][apply_path_def, finite_mapTheory.FLOOKUP_DEF]
QED

(* ----------------------------------------------------------------------
    recursion principle

    The axiom hands the recursive results over under the finite map's
    own map function, which is exactly the shape fmtreerec is defined
    at; both used to be built here by hand, out of an inductive
    relation and a choice.
   ---------------------------------------------------------------------- *)

Theorem fmtree_Axiom:
    !h. ?f. !i fm. f (FTNode i fm) = h i fm (f o_f fm)
Proof
  metis_tac[fmaptree_Axiom]
QED

val fmtreerec_def = new_specification(
  "fmtreerec_def", ["fmtreerec"],
  SIMP_RULE (srw_ss()) [SKOLEM_THM]
            (Q.GEN `h` (Q.SPEC `\i fm r. h i r fm` fmtree_Axiom)));

Theorem fmtreerec_thm:
    fmtreerec h (FTNode i fm) = h i (fmtreerec h o_f fm) fm
Proof
  simp[fmtreerec_def]
QED
