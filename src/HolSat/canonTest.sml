(* ========================================================================= *)
(* PROBLEMS TO TEST THE HOL NORMALIZATION FUNCTIONS.                         *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

(*
app load ["numLib"];
*)

(*
*)
structure canonTest :> canonTest =
struct

open HolKernel Parse boolLib numLib;

infixr -->;

(* ------------------------------------------------------------------------- *)
(* The pigeon-hole principle, courtesy of Konrad Slind.                      *)
(* ------------------------------------------------------------------------- *)

val num = mk_type ("num", []);

fun upto b t = if b >= t then [] else b :: upto (b + 1) t;

fun number i [] = []
  | number i (h :: t) = i :: number (i + 1) t;

fun num_of_int i = mk_numeral (Arbnum.fromInt i)

fun ith_var ty i = mk_var ("v" ^ int_to_string i, ty);

val P = mk_var ("P", num --> num --> bool);

fun mkP i j = list_mk_comb (P, [num_of_int i, num_of_int j]);

fun row i j = list_mk_disj (map (mkP i) (upto 0 j));

fun pigeon k = 
 let
   fun shares Pi plist =
     let
       fun row j =
         mk_conj
         (mk_comb (Pi, num_of_int j), list_mk_disj (map (C mkP j) plist))
      in
        list_mk_disj(map row (upto 0 k))
      end
     fun sharesl _ [] = []
       | sharesl i alist =
       shares (mk_comb (P, num_of_int i)) alist :: sharesl (i + 1) (tl alist)
   val in_holes = list_mk_conj (map (C row k) (upto 0 (k + 1)))
   val Sharing = list_mk_disj (sharesl 0 (tl (upto 0 (k+1))))
 in
   mk_disj (mk_neg in_holes, Sharing)
 end;

fun dest_term tm = SOME
  (dest_conj tm handle HOL_ERR _ =>
   dest_disj tm handle HOL_ERR _ =>
   dest_imp tm) handle HOL_ERR _ => NONE;

fun atoms_of tm =
 let
   fun traverse tm s =
     case dest_term tm of NONE => Binaryset.add (s,tm)
     | SOME (x, y) => traverse x (traverse y s)
   val set = traverse tm (Binaryset.empty Term.compare)
 in
   Binaryset.listItems set
 end;
 
fun varify tm =
 let
   val atoms = atoms_of tm
   val theta = map2 (curry op|->) atoms (map (ith_var bool) (number 0 atoms))
 in
   subst theta tm
 end;

val var_pigeon = varify o pigeon;

(* Quick testing
load "canonTools";
open canonTools;

val N = mk_neg;

(* These generate propositional encodings of the pigeon-hole principle. *)
val pigeon1 = time var_pigeon 1;   (* runtime: 0.000s,     gctime: 0.000s  *)
val pigeon2 = time var_pigeon 2;   (* runtime: 0.020s,     gctime: 0.010s  *)
val pigeon3 = time var_pigeon 3;   (* runtime: 0.020s,     gctime: 0.000s  *)
val pigeon4 = time var_pigeon 4;   (* runtime: 0.060s,     gctime: 0.000s  *)
val pigeon5 = time var_pigeon 5;   (* runtime: 0.120s,     gctime: 0.000s  *)
val pigeon6 = time var_pigeon 6;   (* runtime: 0.250s,     gctime: 0.010s  *)
val pigeon7 = time var_pigeon 7;   (* runtime: 0.450s,     gctime: 0.000s  *)
val pigeon8 = time var_pigeon 8;   (* runtime: 0.810s,     gctime: 0.020s  *)
val pigeon9 = time var_pigeon 9;   (* runtime: 1.320s,     gctime: 0.010s  *)
val pigeon10 = time var_pigeon 10; (* runtime: 2.050s,     gctime: 0.030s  *)
val pigeon20 = time var_pigeon 20; (* runtime: 49.340s,    gctime: 0.510s  *)

(* These result in a large CNF formula that is unsatisfiable. *)
time CNF_CONV (N pigeon1);         (* runtime: 0.010s,     gctime: 0.000s  *)
time CNF_CONV (N pigeon2);         (* runtime: 0.050s,     gctime: 0.020s  *)
time CNF_CONV (N pigeon3);         (* runtime: 0.140s,     gctime: 0.010s  *)
time CNF_CONV (N pigeon4);         (* runtime: 0.300s,     gctime: 0.050s  *)
time CNF_CONV (N pigeon10);        (* runtime: 4.960s,     gctime: 0.320s  *)
time CNF_CONV (N pigeon20);        (* runtime: 111.780s,   gctime: 4.750s  *)

(* Without tautology checking, so result in (very) large CNF formulas. *)
tautology_checking := false;
time CNF_CONV pigeon1;             (* runtime: 0.010s,     gctime: 0.000s  *)
time CNF_CONV pigeon2;             (* runtime: 0.780s,     gctime: 0.060s  *)
(* time CNF_CONV pigeon3;             runtime: 23623.570s, gctime: 1739.000s *)

(* These reduce the formulas to T, thus proving them. *)
tautology_checking := true;
time CNF_CONV pigeon1;             (* runtime: 0.010s,     gctime: 0.010s  *)
time CNF_CONV pigeon2;             (* runtime: 0.370s,     gctime: 0.030s  *)
time CNF_CONV pigeon3;             (* runtime: 104.530s,   gctime: 7.640s  *)
(* time CNF_CONV pigeon4;  didn't finish after >7 hours                    *)

(* Putting formulas in definitional CNF results in only a linear expansion *)
time DEF_CNF_CONV (N pigeon1);     (* runtime: 0.070s,     gctime: 0.000s  *)
time DEF_CNF_CONV (N pigeon2);     (* runtime: 0.460s,     gctime: 0.100s  *)
time DEF_CNF_CONV (N pigeon3);     (* runtime: 1.460s,     gctime: 0.210s  *)
time DEF_CNF_CONV (N pigeon4);     (* runtime: 3.770s,     gctime: 0.770s  *)
time DEF_CNF_CONV (N pigeon5);     (* runtime: 8.590s,     gctime: 1.990s  *)
time DEF_CNF_CONV (N pigeon6);     (* runtime: 17.360s,    gctime: 3.880s  *)
time DEF_CNF_CONV (N pigeon7);     (* runtime: 33.990s,    gctime: 7.700s  *)
time DEF_CNF_CONV (N pigeon8);     (* runtime: 63.180s,    gctime: 15.400s *)
time DEF_CNF_CONV (N pigeon9);     (* runtime: 111.540s,   gctime: 27.510s *)
time DEF_CNF_CONV (N pigeon10);    (* runtime: 187.620s,   gctime: 47.150s *)

time DEF_CNF_CONV pigeon1;         (* runtime: 0.080s,     gctime: 0.000s  *)
time DEF_CNF_CONV pigeon2;         (* runtime: 0.470s,     gctime: 0.070s  *)
time DEF_CNF_CONV pigeon3;         (* runtime: 1.480s,     gctime: 0.310s  *)
time DEF_CNF_CONV pigeon4;         (* runtime: 3.600s,     gctime: 0.580s  *)
time DEF_CNF_CONV pigeon5;         (* runtime: 8.000s,     gctime: 1.550s  *)
time DEF_CNF_CONV pigeon6;         (* runtime: 16.370s,    gctime: 3.240s  *)
time DEF_CNF_CONV pigeon7;         (* runtime: 32.280s,    gctime: 7.100s  *)
time DEF_CNF_CONV pigeon8;         (* runtime: 59.860s,    gctime: 14.120s *)
time DEF_CNF_CONV pigeon9;         (* runtime: 105.650s,   gctime: 25.410s *)
time DEF_CNF_CONV pigeon10;        (* runtime: 179.030s,   gctime: 42.820s *)
*)

end