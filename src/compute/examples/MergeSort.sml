
open bossLib computeLib;


val thms = ref ([] : thm list);
fun add_thm thm = thms := thm :: (!thms);

fun Define_rw q =
  let val thm = bossLib.Define q
  in add_thm thm; thm end
;

val inf_egal_def = Define_rw
 ` (inf_egal 0       n       = T)
/\ (inf_egal (SUC k) 0       = F)
/\ (inf_egal (SUC k) (SUC l) = inf_egal k l) `
;

(* merge sort *)

val fusion_def = Define_rw
 ` (fusion (CONS h1 t1) (CONS h2 t2) =
      if (inf_egal h1 h2) then (CONS h1 (fusion t1 (CONS h2 t2)))
      else (CONS h2 (fusion (CONS h1 t1) t2)))
/\ (fusion [] l2 = l2)
/\ (fusion l1 [] = l1) `
;


val _ = Hol_datatype ` arbin =
            Fe 
          | Br of num => arbin => arbin `
;

val Tas2Ln_def = Define_rw
 ` (Tas2Ln Fe           = [])
/\ (Tas2Ln (Br n a1 a2) = CONS n (fusion (Tas2Ln a1) (Tas2Ln a2))) `
;

val insTas_def = Define_rw
 ` (insTas Fe           n = Br n Fe Fe)
/\ (insTas (Br m a1 a2) n =
     if (inf_egal n m) then Br n a2 (insTas a1 m)
     else Br m a2 (insTas a1 n)) `
;

val Ln2Tas_def = Define_rw
`  (Ln2Tas []          = Fe)
/\ (Ln2Tas (CONS n ns) = insTas (Ln2Tas ns) n) `
;

val tri_heap_def = Define_rw
 ` (tri_heap l = Tas2Ln (Ln2Tas l)) `
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


val L20 = app_l20 (--`[]:num list`--);
val L100 = funpow 5 app_l20 (--`[]:num list`--);


val L2_def = Define_rw ` L2 = [ ^n2; 0] `;
val L4_def = Define_rw ` L4 = [ ^n2; 0; ^n1; 0] `;
val L8_def = Define_rw ` L8 = [ ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0] `;
val L12_def = Define_rw
    ` L12 = [ ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0] `;
val L16_def = Define_rw
  ` L16 = [ ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0] `;
val L20_def = Define_rw ` L20 = ^L20 `;
val L20'_def = Define_rw
  ` L20' = [ ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0; ^n2; 0; ^n1; 0;
	     ^n2; 0; ^n1; 0] `;


val append_def = Define_rw
 ` (append [] l2          = l2)
/\ (append (CONS x l1) l2 = (CONS x (append l1 l2))) `
;

val L40_def = Define_rw ` L40 = append L20 L20`;
val L40'_def = Define_rw ` L40' = append L20' L20'`;
val L80'_def = Define_rw ` L80' = append L40' L40'`;

val L100_def = Define_rw ` L100 = ^L100 `;
val L200_def = Define_rw ` L200 = append L100 L100 `;
val L400_def = Define_rw ` L400 = append L200 L200 `;
val L1200_def = Define_rw ` L1200 = append L400 (append L400 L400) `;
val L2400_def = Define_rw ` L2400 = append L1200 L1200 `;
val L4800_def = Define_rw ` L4800 = append L2400 L2400 `;
val L9600_def = Define_rw ` L9600 = append L4800 L4800 `;
val L19200_def = Define_rw ` L19200 = append L9600 L9600 `;
val L38400_def = Define_rw ` L38400 = append L19200 L19200 `;


(* Save the state *)
val sort_thms = !thms;

val rws = from_list false [boolTheory.COND_CLAUSES];
val _ = add_clauses true sort_thms rws;


fun norm q = CBV_CONV rws (--q--);


norm ` tri_heap L4 `;  (* ~ 0.03s *)
norm ` tri_heap L12 `;
norm ` tri_heap L20 `; (* ~ 0.33s *)
norm ` tri_heap L200 `;
  (* ~ 12s = 3300 times more than Moscow ML (without expl. subst.) *)


(* Compare with REWRITE_CONV *)

val rw_norm = REWRITE_CONV sort_thms;

rw_norm (--`tri_heap L4`--);  (* ~ 0.06s *)
rw_norm (--`tri_heap L12`--); (* ~ 3.4s *)
rw_norm (--`tri_heap L20`--); (* ~ 15mn *)

(*
SIMP_CONV empty_ss thms (--`tri_heap L12`--);
*)

