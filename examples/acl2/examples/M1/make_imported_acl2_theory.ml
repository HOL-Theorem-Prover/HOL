(*
1. Reads the file imported_acl2_books.ml which should define a
   non-empty list of strings called imported_acl2_books.

2. Starts a new theory whose name is imported_acl2Theory.

3. Slurps in the ML files in imported_acl2_books.

4. create and compile imported_acl2Theory.
*)

quietdec := true;
load "sexp";
open sexp;

open pred_setTheory;

load "load_book";
open load_book;
quietdec := false;

use "imported_acl2_books.ml";

val current_package = ref "UnspecifiedPackage";

new_theory "imported_acl2";

(* not using map to guarantee hd-to-tl application order *)
fun aplist (f: string -> (string * thm) list list) l = 
 if null l then () else (f(hd l); aplist f (tl l));

aplist (time (load_book use load_simp_fn)) imported_acl2_books;

export_theory();

compile_theory();



