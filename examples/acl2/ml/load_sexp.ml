quietdec := true;
loadPath := (Globals.HOLDIR ^ "/examples/acl2/ml") :: !loadPath;
map load ["sexp","sexpTheory","hol_defaxiomsTheory"];
open fracTheory ratTheory complex_rationalTheory 
     sexp sexpTheory hol_defaxiomsTheory;
(* use "sexp.ml"; *)
printDepth := 10000;
printLength := 10000;
quietdec := false;

(* Add path to ACL2 examples *)
loadPath :=
(Globals.HOLDIR ^ "/examples/acl2/acl2-new-partial/tests/gold") :: (!loadPath);

(*****************************************************************************)
(* load a book after recursively loading included books                      *)
(*****************************************************************************)
fun load_book book_name =
  let val _ = use(book_name ^ ".ml")
      val acl2_list = !acl2_list_ref
  in
   if is_mlinclude(hd acl2_list) 
    then let val thll = load_book(dest_mlinclude(hd acl2_list))
             val thl = map 
                        (install o mk_acl2def) 
                        (accumulate_discard_events(tl acl2_list))
         in
          thll @ [thl]
         end
    else [map 
           (install o mk_acl2def) 
           (accumulate_discard_events acl2_list)]
  end;
