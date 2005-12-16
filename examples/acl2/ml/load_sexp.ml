quietdec := true;
loadPath := "rationals" :: !loadPath;
map load ["sexp","sexpTheory"];
open fracTheory ratTheory complex_rationalTheory 
     sexp sexpTheory;
use "sexp.ml";
quietdec := false;
