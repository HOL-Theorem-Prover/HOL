(*****************************************************************************)
(* Slurp in defaxioms.lisp.trans.ml and put results in variable defaxioms.   *)
(*****************************************************************************)

new_theory "defaxioms";

use (Globals.HOLDIR ^ "/examples/acl2/ml/load_sexp.ml");
use (Globals.HOLDIR ^ "/examples/acl2/ml/defaxioms.lisp.trans.ml");

load_defaxioms();

val string_abbrev_thms = map snd (definitions "-");

val cr_thms =
 map
  GSYM
  [caar_def,cadr_def,cdar_def,cddr_def,
   caaar_def,cdaar_def,cadar_def,cddar_def,caadr_def,cdadr_def,caddr_def,cdddr_def,
   caaaar_def,cadaar_def,caadar_def,caddar_def,caaadr_def,cadadr_def,caaddr_def,cadddr_def,
   cdaaar_def,cddaar_def,cdadar_def,cdddar_def,cdaadr_def,cddadr_def,cdaddr_def,cddddr_def];

val let_simp =
 prove
  (``(!P1 v y. (let (x,y) = (v,y) in P1 x y) = (let x = v in P1 x y))
     /\
     (!P2 v y z. (let (x,y,z) = (v,y,z) in P2 x y z) = (let x = v in P2 x y z))
     /\
     (!P3 v y z w. (let (x,y,z,w) = (v,y,z,w) in P3 x y z w) = (let x = v in P3 x y z w))``,
   RW_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def]);

val simps = 
 [let_simp,andl_fold,itel_fold,itel_append]
 @
 (map 
   GSYM 
   [int_def,nat_def,List_def,asym_def,csym_def,ksym_def,osym_def]);

val simp_defaxioms = ref([] : thm list);
simp_defaxioms := !imported_acl2_theorems;

simp_defaxioms := time (map(SIMP_RULE list_ss simps)) (!simp_defaxioms);

simp_defaxioms :=
 time (foldl 
        (fn (th,thl) => map (SIMP_RULE std_ss [th]) thl) 
        (!simp_defaxioms)) 
        (GSYM(CONJUNCT1 itel_fold)::(rev cr_thms));

simp_defaxioms := time (map(SIMP_RULE std_ss string_abbrev_thms)) (!simp_defaxioms);

!simp_defaxioms;



(*
export_acl2_theory();

compile_theory();
*)


