quietdec := true;
loadPath := (Globals.HOLDIR ^ "/examples/acl2/ml") :: !loadPath;
map load ["sexp","sexpTheory","hol_defaxiomsTheory"];
open fracTheory ratTheory complex_rationalTheory 
     sexp sexpTheory hol_defaxiomsTheory;
(* use "sexp.ml"; *)
printDepth := 10000;
printLength := 10000;

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
     (!P3 v y z w. (let (x,y,z,w) = (v,y,z,w) in P3 x y z w) = (let x = v in P3
 x y z w))``,
   RW_TAC std_ss []
    THEN FULL_SIMP_TAC std_ss [markerTheory.Abbrev_def]); 

val forall_fold = GSYM(SIMP_CONV list_ss [forall_def] ``forall x. P x``);
val exists_fold = GSYM(SIMP_CONV list_ss [exists_def] ``exists x. P x``);

val bool_to_sexp =
 prove
  (``bool_to_sexp b = if b then t else nil``,
   Cases_on `b`
    THEN RW_TAC std_ss [bool_to_sexp_def]);

val forall2_thm =
 prove
  (``(bool_to_sexp !x y. |= P x y) = 
      bool_to_sexp (!x. |= bool_to_sexp !y. |= P x y)``,
   RW_TAC std_ss [bool_to_sexp,ACL2_TRUE]
    THEN METIS_TAC[]);

val exists2_thm =
 prove
  (``(bool_to_sexp ?x y. |= P x y) = 
      bool_to_sexp (?x. |= bool_to_sexp ?y. |= P x y)``,
   RW_TAC std_ss [bool_to_sexp,ACL2_TRUE]
    THEN METIS_TAC[]);
                                                                                              
(* Add path to ACL2 examples *)
loadPath :=
(Globals.HOLDIR ^ "/examples/acl2/acl2-new-partial/tests/gold") :: (!loadPath);

val simps =
 [let_simp,andl_fold,itel_fold,itel_append,
  forall2_thm,exists2_thm,forall_fold,exists_fold]
 @
 (map
   GSYM
   [int_def,nat_def,List_def,asym_def,csym_def,ksym_def,osym_def]);

quietdec := false;

(*****************************************************************************)
(* load a book after recursively loading included books                      *)
(*****************************************************************************)
fun load_book book_name =
  let val _ = use(book_name ^ ".ml")
      val acl2_list = !acl2_list_ref
      val install_fn = (I ## SIMP_RULE list_ss simps) o install o mk_acl2def
  in
   if is_mlinclude(hd acl2_list) 
    then let val thll = load_book(dest_mlinclude(hd acl2_list))
             val thl = 
              map install_fn (accumulate_discard_events(tl acl2_list))
         in
          thll @ [thl]
         end
    else [map install_fn (accumulate_discard_events acl2_list)]
  end;

(* 

LTL example

val ll = load_book "summary";

val States_def        = Define `States = g (ksym "STATES")`;
val InitialStates_def = Define `InitialStates = g (ksym "INITIAL-STATES")`;
val Variables_def     = Define `Variables = g (ksym "VARIABLES")`;
val Transition_def    = Define `Transition = g (ksym "TRANSITION")`;

val g_simps =
 [let_simp,andl_fold,itel_fold,itel_append]
 @
 (map
   GSYM
   [int_def,nat_def,List_def,asym_def,csym_def,ksym_def,osym_def,
    States_def,InitialStates_def,Variables_def,Transition_def]);   

val ll_simp = map (map (I ## SIMP_RULE list_ss g_simps)) ll;

val forall_fold = GSYM(SIMP_CONV list_ss [forall_def] ``forall x. P x``);

SIMP_RULE list_ss [forall_fold] yh

forall P ==> bool_to_sexp !v. |= P(v)

*)