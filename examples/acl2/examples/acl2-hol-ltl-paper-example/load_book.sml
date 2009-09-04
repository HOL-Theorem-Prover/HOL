
(* Commands when run interactively:
quietdec := true;
loadPath := (Globals.HOLDIR ^ "/examples/acl2/ml") :: !loadPath;
map load ["sexp","sexpTheory","hol_defaxiomsTheory"];
open fracTheory ratTheory complex_rationalTheory 
     sexp sexpTheory hol_defaxiomsTheory;

printDepth := 10000;
printLength := 10000;

quietdec := false;
*)

structure load_book :> load_book =
struct



(*****************************************************************************)
(* Boilerplate needed for compilation                                        *)
(*****************************************************************************)

open HolKernel Parse boolLib bossLib pred_setTheory pred_setLib;

open fracTheory ratTheory sexp complex_rationalTheory sexpTheory 
     hol_defaxiomsTheory;

(*****************************************************************************)
(* END BOILERPLATE                                                           *)
(*****************************************************************************)

val load_simp_fn =
 SIMP_RULE
  list_ss
  ([let_simp,andl_fold,itel_fold,itel_append,
    forall2_thm,exists2_thm,forall_fold,exists_fold,
    implies,andl_simp,not_simp,t_nil]
   @
   (map GSYM [int_def,nat_def,List_def,asym_def,csym_def,ksym_def,osym_def]));

fun get_acl2_thm s = load_simp_fn(DB.fetch "imported_acl2" (s ^ "_thm"));

(*****************************************************************************)
(* load a book after recursively loading included books                      *)
(*****************************************************************************)
fun load_book (load_fn:string->unit) (simp_fn:thm->thm) book_name =
  let val _ = load_fn(book_name ^ ".ml")
      val acl2_list = !acl2_list_ref
      val install_fn = (I ## simp_fn) o install o mk_acl2def
  in
   if is_mlinclude(hd acl2_list) 
    then let val thll = 
              load_book load_fn simp_fn (dest_mlinclude(hd acl2_list))
             val thl = 
              map install_fn (accumulate_discard_events(tl acl2_list))
         in
          thll @ [thl]
         end
    else [map install_fn (accumulate_discard_events acl2_list) 
          handle e => Raise e]
  end;

end
