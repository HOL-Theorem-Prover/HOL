(*****************************************************************************)
(* Slurp in defaxioms.lisp.trans.ml and put results on variable defaxioms.   *)
(*****************************************************************************)

new_theory "defaxioms";

quietdec := true;
use (Globals.HOLDIR ^ "/examples/acl2/ml/load_sexp.ml");
use (Globals.HOLDIR ^ "/examples/acl2/lisp/defaxioms.lisp.trans.ml");
load_defaxioms();
val string_abbrev_thms = map snd (definitions "-");
quietdec := false;

val List_def =
 Define
  `(List[] = nil)
    /\
    (List(s::sl) = cons s (List sl))`;

val acl2_and_def =
 Define
  `acl2_and x y = ite x y (List[])`;

val acl2_and_def =
 Define
  `(acl2_and[] = nil)
   /\
   (acl2_and((test,val)::sl) = ite test val (acl2_and sl))`;

val asym_def = Define `asym = sym ACL2`;
val csym_def = Define `csym = sym COMMON_LISP`;
val ksym_def = Define `ksym = sym KEYWORD`;
val osym_def = Define `osym = sym ACL2_OUTPUT_CHANNEL`;

val let_simp =
 prove
  (``!P v y. (let (x,y) = (v,y) in P x y) = (let x = v in P x y)``,
   RW_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def]);

val simp_defs = let_simp 
                :: map GSYM [int_def,nat_def,
                             List_def, acl2_and_def,
                             acl2_and_def,
                             asym_def,csym_def,ksym_def,osym_def];

val simp_defaxioms = ref([] : thm list);

simp_defaxioms := time (map(SIMP_RULE std_ss simp_defs)) (!defaxioms);

val abbrev_thms = 
 CONJUNCT1 List_def :: CONJUNCT1 acl2_and_def :: string_abbrev_thms;

simp_defaxioms := time (map (SUBS abbrev_thms)) (!simp_defaxioms);

!simp_defaxioms;

(*
val _ = export_acl2_theory();
*)

