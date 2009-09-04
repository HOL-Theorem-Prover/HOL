(*
load "bossLib";
load "computeLib";
*)
open bossLib computeLib;


val thms = ref ([] : thm list);
fun add_thm thm = thms := thm :: (!thms);

fun Define_rw q =
  let val thm = bossLib.Define q
  in add_thm thm; thm end
;

val le_nat_def = Define_rw
 ` (le_nat 0       n       = T)
/\ (le_nat (SUC k) 0       = F)
/\ (le_nat (SUC k) (SUC l) = le_nat k l) `
;

val append_def = Define_rw
 ` (append [] l2          = l2)
/\ (append (x :: l1) l2 = x :: (append l1 l2)) `
;

val double_def = Define_rw ` double l = append l l `
;

val triple_def = Define_rw ` triple l = append l (append l l) `
;

(* merge sort *)

val merge_def = Define_rw
 ` (merge (h1 :: t1) (h2 :: t2) =
      if le_nat h1 h2 then h1 :: merge t1 (h2 :: t2)
      else h2 :: merge (h1 :: t1) t2)
/\ (merge [] l2 = l2)
/\ (merge l1 [] = l1) `
;


val _ = Hol_datatype ` arbin =
            Lf
          | Nd of num => arbin => arbin `
;

val Tree2List_def = Define_rw
 ` (Tree2List Lf           = [])
/\ (Tree2List (Nd n a1 a2) = n :: merge (Tree2List a1) (Tree2List a2)) `
;

val insTree_def = Define_rw
 ` (insTree Lf           n = Nd n Lf Lf)
/\ (insTree (Nd m a1 a2) n =
     if (le_nat n m) then Nd n a2 (insTree a1 m)
     else Nd m a2 (insTree a1 n)) `
;

val List2Tree_def = Define_rw
`  (List2Tree []          = Lf)
/\ (List2Tree (n :: ns) = insTree (List2Tree ns) n) `
;

val merge_sort_def = Define_rw
 ` merge_sort l = Tree2List (List2Tree l) `
;



(* Example *)
val n1 = --`SUC 0 `--;
val n2 = --`SUC ^n1 `--;
val n3 = --`SUC ^n2 `--;
val n4 = --`SUC ^n3 `--;

val l0 = --`[] : num list`--;

fun app_l4 l = --` ^n2 :: 0 :: ^n1 :: 0 :: ^l `--;

fun app_l20 l =
       --` ^n2 :: 0 :: ^n1 :: 0 :: ^n1 :: ^n3 :: ^n4 ::
           ^n1 :: 0 :: ^n1 :: ^n3 :: 0 :: ^n1 :: ^n3 ::
           ^n4 :: ^n2 :: 0 :: ^n1 :: 0 :: ^n1 :: ^l `--
;


val L2_def   = Define_rw ` L2   = [ ^n2; 0] `;
val L4_def   = Define_rw ` L4   = ^(app_l4 l0) `;
val L8_def   = Define_rw ` L8   = ^(funpow 2 app_l4 l0) `;
val L12_def  = Define_rw ` L12  = ^(funpow 3 app_l4 l0) `;
val L16_def  = Define_rw ` L16  = ^(funpow 4 app_l4 l0) `;
val L20'_def = Define_rw ` L20' = ^(funpow 5 app_l4 l0) `;
val L40'_def = Define_rw ` L40' = double L20' `;
val L80'_def = Define_rw ` L80' = double L40'`;


val L20_def    = Define_rw ` L20    = ^(app_l20 l0) `;
val L40_def    = Define_rw ` L40    = double L20`;
val L100_def   = Define_rw ` L100   = ^(funpow 5 app_l20 l0) `;
val L200_def   = Define_rw ` L200   = double L100 `;
val L400_def   = Define_rw ` L400   = double L200 `;
val L1200_def  = Define_rw ` L1200  = triple L400 `;
val L2400_def  = Define_rw ` L2400  = double L1200 `;
val L4800_def  = Define_rw ` L4800  = double L2400 `;
val L9600_def  = Define_rw ` L9600  = double L4800 `;
val L19200_def = Define_rw ` L19200 = double L9600 `;
val L38400_def = Define_rw ` L38400 = double L19200 `;


(* Save the useful thms *)
val sort_thms = rev (!thms);

val rws = reduceLib.reduce_rws();
val _ = add_thms sort_thms rws;

fun norm q = time (CBV_CONV rws) (--q--);
(*
fun norm q = timing.with_stats (timing.tickt "total" (CBV_CONV rws)) (--q--);
*)

(* rules.sml implemented witout expl. subst.: quadratic
 *   Ln    |  time on sprat
 * --------+-----------------
 *   L4    | ~ 0.03s
 *   L12   | ~ 0.11s
 *   L20   | ~ 0.30s
 *   L40   | ~ 0.89s
 *   L100  | ~ 3.5s
 *   L200  | ~ 11.7s = 3300 times slower than Moscow ML
 *   L1200 | ~ 377s
 *)

(* with expl. subst.: N.log N *)
norm ` merge_sort L12 `; (* ~ 0.09s *)
norm ` merge_sort L20 `; (* ~ 0.24s *)
norm ` merge_sort L100 `; (* ~ 2.04s *)
norm ` merge_sort L200 `; (* ~ 4.9s *)
norm ` merge_sort L400 `; (* ~ 11.4s *)
val _ = norm ` merge_sort L1200 `; (* ~ 41.6s / MosML: 0.043s --> 990 *)
val _ = norm ` merge_sort L19200 `; (* ~ 996s / --> 634 *)
val _ = norm ` merge_sort L38400 `; (* ~ 2090s, 66Mo / MosML: 4.3s --> 490 *)


(* Comparison with REWRITE_CONV: exponential *)

fun rw_norm q = time (REWRITE_CONV sort_thms) (--q--);

rw_norm `merge_sort L4`;  (* ~ 0.06s *)
rw_norm `merge_sort L12`; (* ~ 3.4s *)
rw_norm `merge_sort L20`; (* ~ 15mn *)

(* And SIMP_CONV *)
open simpLib;

val srws = flatten (map BODY_CONJUNCTS (COND_CLAUSES :: sort_thms));

fun simp_norm q = time (SIMP_CONV empty_ss srws) (--q--);

simp_norm `merge_sort L12`; (* ~ 5s *)


