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
/\ (append (CONS x l1) l2 = (CONS x (append l1 l2))) `
;

(* merge sort *)

val merge_def = Define_rw
 ` (merge (CONS h1 t1) (CONS h2 t2) =
      if (le_nat h1 h2) then (CONS h1 (merge t1 (CONS h2 t2)))
      else (CONS h2 (merge (CONS h1 t1) t2)))
/\ (merge [] l2 = l2)
/\ (merge l1 [] = l1) `
;


val _ = Hol_datatype ` arbin =
            Lf 
          | Nd of num => arbin => arbin `
;

val Tree2List_def = Define_rw
 ` (Tree2List Lf           = [])
/\ (Tree2List (Nd n a1 a2) = CONS n (merge (Tree2List a1) (Tree2List a2))) `
;

val insTree_def = Define_rw
 ` (insTree Lf           n = Nd n Lf Lf)
/\ (insTree (Nd m a1 a2) n =
     if (le_nat n m) then Nd n a2 (insTree a1 m)
     else Nd m a2 (insTree a1 n)) `
;

val List2Tree_def = Define_rw
`  (List2Tree []          = Lf)
/\ (List2Tree (CONS n ns) = insTree (List2Tree ns) n) `
;

val merge_sort_def = Define_rw
 ` (merge_sort l = Tree2List (List2Tree l)) `
;



(* Example *)
val n1 = --`SUC 0 `--;
val n2 = --`SUC ^n1 `--;
val n3 = --`SUC ^n2 `--;
val n4 = --`SUC ^n3 `--;

fun app_l20 l =
       --` (CONS ^n2 (CONS 0 (CONS ^n1 (CONS 0 (CONS ^n1 (CONS ^n3 (CONS ^n4
           (CONS ^n1 (CONS 0 (CONS ^n1 (CONS ^n3 (CONS 0 (CONS ^n1 (CONS ^n3
           (CONS ^n4 (CONS ^n2 (CONS 0 (CONS ^n1 (CONS 0 (CONS ^n1
	     ^l )))))))))))))))))))) `--
;

val L0 = --`[] : num list`--;
val L20 = app_l20 L0;
val L100 = funpow 5 app_l20 L0;


val L2_def   = Define_rw ` L2 = [ ^n2; 0] `;
val L4_def   = Define_rw ` L4 = [ ^n2; 0; ^n1; 0] `;
val L8_def   = Define_rw ` L8 = [ ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0] `;
val L12_def  = Define_rw
    ` L12 = [ ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0] `;
val L16_def  = Define_rw
  ` L16 = [ ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0] `;
val L20'_def = Define_rw
  ` L20' = [ ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0;
	     ^n2; 0; ^n1; 0] `;
val L40'_def   = Define_rw ` L40' = append L20' L20'`;
val L80'_def   = Define_rw ` L80' = append L40' L40'`;


val L20_def    = Define_rw ` L20 = ^L20 `;
val L40_def    = Define_rw ` L40 = append L20 L20`;

val L100_def   = Define_rw ` L100 = ^L100 `;
val L200_def   = Define_rw ` L200 = append L100 L100 `;
val L400_def   = Define_rw ` L400 = append L200 L200 `;
val L1200_def  = Define_rw ` L1200 = append L400 (append L400 L400) `;
val L2400_def  = Define_rw ` L2400 = append L1200 L1200 `;
val L4800_def  = Define_rw ` L4800 = append L2400 L2400 `;
val L9600_def  = Define_rw ` L9600 = append L4800 L4800 `;
val L19200_def = Define_rw ` L19200 = append L9600 L9600 `;
val L38400_def = Define_rw ` L38400 = append L19200 L19200 `;


(* Save the useful thms *)
val sort_thms = !thms;

val rws = from_list false [COND_CLAUSES];
val _ = add_clauses true sort_thms rws;

fun norm q = time (CBV_CONV rws) (--q--);

(* rules.sml implemented witout expl. subst. *)
norm ` merge_sort L4 `;  (* ~ 0.03s *)
norm ` merge_sort L12 `; (* ~ 0.11s *)
norm ` merge_sort L20 `; (* ~ 0.31s *)
norm ` merge_sort L40 `; (* ~ 0.89s *)
norm ` merge_sort L200 `;  (* ~ 11.3s = 3300 times slower than Moscow ML *)
norm ` merge_sort L1200 `; (* ~ 393s *)


(* Compare with REWRITE_CONV *)

fun rw_norm q = time (REWRITE_CONV sort_thms) (--q--);

rw_norm `merge_sort L4`;  (* ~ 0.06s *)
rw_norm `merge_sort L12`; (* ~ 3.4s *)
rw_norm `merge_sort L20`; (* ~ 15mn *)

(* And SIMP_CONV *)
val srws =
   map SPEC_ALL
   (flatten (map (CONJUNCTS o SPEC_ALL) (COND_CLAUSES::sort_thms)));

fun simp_norm q = time (SIMP_CONV empty_ss srws) (--q--);

simp_norm `merge_sort L12`; (* ~ 5s *)


