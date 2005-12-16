quietdec := true;
loadPath := (Globals.HOLDIR ^ "/examples/acl2/ml") :: !loadPath;
map load ["sexp","sexpTheory"];
open fracTheory ratTheory complex_rationalTheory 
     sexp sexpTheory;
use "sexp.ml";
quietdec := false;
