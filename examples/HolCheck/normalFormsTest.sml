(* ========================================================================= *)
(* PROBLEMS TO TEST THE HOL NORMALIZATION FUNCTIONS.                         *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

(*
app load ["numLib"];
*)

(*
*)
structure normalFormsTest :> normalFormsTest =
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

(* ------------------------------------------------------------------------- *)
(* Large formulas.                                                           *)
(* ------------------------------------------------------------------------- *)

(* An example from Mike, originally called add4. *)

val valid_1 =
 `(N3 = A_0_) /\
  (N4 = A_2_) /\
  (N5 = A_4_) /\
  (N6 = A_5_) /\
  (N7 = A_6_) /\
  (N8 = A_8_) /\
  (N9 = A_3_) /\
  (N10 = A_7_) /\
  (N11 = A_9_) /\
  (N12 = A_11_) /\
  (N13 = A_1_) /\
  (N14 = A_10_) /\
  (N15 = ANDA) /\
  (N16 = EXORA) /\
  (N17 = B_3_) /\
  (N18 = B_4_) /\
  (N19 = B_6_) /\
  (N20 = B_1_) /\
  (N21 = B_7_) /\
  (N22 = B_9_) /\
  (N23 = B_2_) /\
  (N24 = B_5_) /\
  (N25 = B_8_) /\
  (N26 = B_10_) /\
  (N27 = B_11_) /\
  (N28 = B_0_) /\
  (N29 = ANDB) /\
  (N30 = EXORB) /\
  (N31 = CARRYIN) /\
  (N98 = ~N29) /\
  (N104 = ~N30) /\
  (N97 = ~N15) /\
  (N103 = ~N16) /\
  (N102 = ~N31) /\
  (N105 = ~N102) /\
  (N243 = ~N14 \/ ~N97) /\
  (N235 = ~N103) /\
  (N244 = ~N26 \/ ~N98) /\
  (N236 = ~N104) /\
  (N224 = ~N22 \/ ~N98) /\
  (N232 = ~N104) /\
  (N223 = ~N11 \/ ~N97) /\
  (N231 = ~N103) /\
  (N217 = ~N8 \/ ~N97) /\
  (N209 = ~N103) /\
  (N218 = ~N25 \/ ~N98) /\
  (N210 = ~N104) /\
  (N197 = ~N21 \/ ~N98) /\
  (N206 = ~N104) /\
  (N196 = ~N10 \/ ~N97) /\
  (N205 = ~N103) /\
  (N190 = ~N19 \/ ~N98) /\
  (N182 = ~N104) /\
  (N189 = ~N7 \/ ~N97) /\
  (N181 = ~N103) /\
  (N251 = ~N27 \/ ~N98) /\
  (N259 = ~N104) /\
  (N250 = ~N12 \/ ~N97) /\
  (N258 = ~N103) /\
  (N163 = ~N18 \/ ~N98) /\
  (N155 = ~N104) /\
  (N162 = ~N5 \/ ~N97) /\
  (N154 = ~N103) /\
  (N170 = ~N24 \/ ~N98) /\
  (N178 = ~N104) /\
  (N169 = ~N6 \/ ~N97) /\
  (N177 = ~N103) /\
  (N136 = ~N23 \/ ~N98) /\
  (N128 = ~N104) /\
  (N135 = ~N4 \/ ~N97) /\
  (N127 = ~N103) /\
  (N116 = ~N20 \/ ~N98) /\
  (N124 = ~N104) /\
  (N115 = ~N13 \/ ~N97) /\
  (N123 = ~N103) /\
  (N110 = ~N28 \/ ~N98) /\
  (N100 = ~N104) /\
  (N109 = ~N3 \/ ~N97) /\
  (N99 = ~N103) /\
  (N142 = ~N17 \/ ~N98) /\
  (N150 = ~N104) /\
  (N141 = ~N9 \/ ~N97) /\
  (N149 = ~N103) /\
  (N87 = ~N243) /\
  (N89 = ~N244) /\
  (N83 = ~N224) /\
  (N85 = ~N223) /\
  (N79 = ~N217) /\
  (N81 = ~N218) /\
  (N75 = ~N197) /\
  (N77 = ~N196) /\
  (N73 = ~N190) /\
  (N71 = ~N189) /\
  (N91 = ~N251) /\
  (N93 = ~N250) /\
  (N65 = ~N163) /\
  (N63 = ~N162) /\
  (N67 = ~N170) /\
  (N69 = ~N169) /\
  (N57 = ~N136) /\
  (N55 = ~N135) /\
  (N51 = ~N116) /\
  (N53 = ~N115) /\
  (N49 = ~N110) /\
  (N47 = ~N109) /\
  (N59 = ~N142) /\
  (N61 = ~N141) /\
  (N241 = N87 /\ N103 \/ ~N87 /\ ~N103) /\
  (N242 = N89 /\ N104 \/ ~N89 /\ ~N104) /\
  (N227 = N83 /\ N104 \/ ~N83 /\ ~N104) /\
  (N226 = N85 /\ N103 \/ ~N85 /\ ~N103) /\
  (N215 = N79 /\ N103 \/ ~N79 /\ ~N103) /\
  (N216 = N81 /\ N104 \/ ~N81 /\ ~N104) /\
  (N200 = N75 /\ N104 \/ ~N75 /\ ~N104) /\
  (N199 = N77 /\ N103 \/ ~N77 /\ ~N103) /\
  (N188 = N73 /\ N104 \/ ~N73 /\ ~N104) /\
  (N187 = N71 /\ N103 \/ ~N71 /\ ~N103) /\
  (N254 = N91 /\ N104 \/ ~N91 /\ ~N104) /\
  (N253 = N93 /\ N103 \/ ~N93 /\ ~N103) /\
  (N160 = N65 /\ N104 \/ ~N65 /\ ~N104) /\
  (N159 = N63 /\ N103 \/ ~N63 /\ ~N103) /\
  (N173 = N67 /\ N104 \/ ~N67 /\ ~N104) /\
  (N172 = N69 /\ N103 \/ ~N69 /\ ~N103) /\
  (N134 = N57 /\ N104 \/ ~N57 /\ ~N104) /\
  (N133 = N55 /\ N103 \/ ~N55 /\ ~N103) /\
  (N119 = N51 /\ N104 \/ ~N51 /\ ~N104) /\
  (N118 = N53 /\ N103 \/ ~N53 /\ ~N103) /\
  (N108 = N49 /\ N104 \/ ~N49 /\ ~N104) /\
  (N107 = N47 /\ N103 \/ ~N47 /\ ~N103) /\
  (N145 = N59 /\ N104 \/ ~N59 /\ ~N104) /\
  (N144 = N61 /\ N103 \/ ~N61 /\ ~N103) /\
  (N88 = ~N241) /\
  (N90 = ~N242) /\
  (N84 = ~N227) /\
  (N86 = ~N226) /\
  (N80 = ~N215) /\
  (N82 = ~N216) /\
  (N76 = ~N200) /\
  (N78 = ~N199) /\
  (N74 = ~N188) /\
  (N72 = ~N187) /\
  (N92 = ~N254) /\
  (N94 = ~N253) /\
  (N66 = ~N160) /\
  (N64 = ~N159) /\
  (N68 = ~N173) /\
  (N70 = ~N172) /\
  (N58 = ~N134) /\
  (N56 = ~N133) /\
  (N52 = ~N119) /\
  (N54 = ~N118) /\
  (N50 = ~N108) /\
  (N48 = ~N107) /\
  (N60 = ~N145) /\
  (N62 = ~N144) /\
  (N234 = ~N88) /\
  (N230 = ~N86) /\
  (N208 = ~N80) /\
  (N204 = ~N78) /\
  (N180 = ~N72) /\
  (N257 = ~N94) /\
  (N152 = ~N64) /\
  (N176 = ~N70) /\
  (N126 = ~N56) /\
  (N122 = ~N54) /\
  (N96 = ~N48) /\
  (N148 = ~N62) /\
  (N237 = N90 /\ N88 \/ ~N90 /\ ~N88) /\
  (N229 = N84 /\ N86 \/ ~N84 /\ ~N86) /\
  (N211 = N82 /\ N80 \/ ~N82 /\ ~N80) /\
  (N203 = N76 /\ N78 \/ ~N76 /\ ~N78) /\
  (N183 = N74 /\ N72 \/ ~N74 /\ ~N72) /\
  (N256 = N92 /\ N94 \/ ~N92 /\ ~N94) /\
  (N156 = N66 /\ N64 \/ ~N66 /\ ~N64) /\
  (N175 = N68 /\ N70 \/ ~N68 /\ ~N70) /\
  (N129 = N58 /\ N56 \/ ~N58 /\ ~N56) /\
  (N121 = N52 /\ N54 \/ ~N52 /\ ~N54) /\
  (N101 = N50 /\ N48 \/ ~N50 /\ ~N48) /\
  (N147 = N60 /\ N62 \/ ~N60 /\ ~N62) /\
  (N233 = ~N237) /\
  (N221 = ~N229) /\
  (N207 = ~N211) /\
  (N193 = ~N203) /\
  (N179 = ~N183) /\
  (N248 = ~N256) /\
  (N151 = ~N156) /\
  (N166 = ~N175) /\
  (N125 = ~N129) /\
  (N113 = ~N121) /\
  (N95 = ~N101) /\
  (N139 = ~N147) /\
  (N245 = ~N233) /\
  (N228 = ~N221) /\
  (N219 = ~N207) /\
  (N167 = ~N166 \/ ~N151 \/ ~N179 \/ ~N193) /\
  (N202 = ~N193) /\
  (N191 = ~N179) /\
  (N255 = ~N248) /\
  (N164 = ~N151) /\
  (N174 = ~N166) /\
  (N137 = ~N125) /\
  (N120 = ~N113) /\
  (N111 = ~N95) /\
  (N146 = ~N139) /\
  (N106 = N105 /\ ~N95 \/ ~N105 /\ N95) /\
  (N161 = ~N167) /\
  (N112 = ~N95 /\ ~N48 \/ ~N111 /\ ~N102) /\
  (N114 = ~N112) /\
  (N39 = ~N106) /\
  (N130 = ~N120 /\ ~N112 \/ ~N122 /\ ~N113) /\
  (N117 = N114 /\ N113 \/ ~N114 /\ ~N113) /\
  (N131 = ~N130) /\
  (N138 = ~N125 /\ ~N56 \/ ~N137 /\ ~N130) /\
  (N32 = ~N117) /\
  (N132 = N131 /\ ~N125 \/ ~N131 /\ N125) /\
  (N153 = ~N146 /\ ~N138 \/ ~N148 /\ ~N139) /\
  (N140 = ~N138) /\
  (N37 = ~N132) /\
  (N157 = ~N153) /\
  (N165 = ~N151 /\ ~N64 \/ ~N164 /\ ~N153) /\
  (N143 = N140 /\ N139 \/ ~N140 /\ ~N139) /\
  (N158 = N157 /\ ~N151 \/ ~N157 /\ N151) /\
  (N184 = ~N174 /\ ~N165 \/ ~N176 /\ ~N166) /\
  (N168 = ~N165) /\
  (N33 = ~N143) /\
  (N43 = ~N158) /\
  (N185 = ~N184) /\
  (N192 = ~N179 /\ ~N72 \/ ~N191 /\ ~N184) /\
  (N171 = N168 /\ N166 \/ ~N168 /\ ~N166) /\
  (N195 = ~N192) /\
  (N186 = N185 /\ ~N179 \/ ~N185 /\ N179) /\
  (N201 = ~N202 /\ ~N192 \/ ~N204 /\ ~N193) /\
  (N34 = ~N171) /\
  (N198 = N195 /\ N193 \/ ~N195 /\ ~N193) /\
  (N35 = ~N186) /\
  (N194 = ~N167 /\ ~N153 \/ ~N161 /\ ~N201) /\
  (N36 = ~N198) /\
  (N212 = ~N194) /\
  (N213 = ~N212) /\
  (N220 = ~N207 /\ ~N80 \/ ~N219 /\ ~N212) /\
  (N214 = N213 /\ ~N207 \/ ~N213 /\ N207) /\
  (N222 = ~N220) /\
  (N238 = ~N228 /\ ~N220 \/ ~N230 /\ ~N221) /\
  (N38 = ~N214) /\
  (N225 = N222 /\ N221 \/ ~N222 /\ ~N221) /\
  (N239 = ~N238) /\
  (N246 = ~N233 /\ ~N88 \/ ~N245 /\ ~N238) /\
  (N40 = ~N225) /\
  (N240 = N239 /\ ~N233 \/ ~N239 /\ N233) /\
  (N261 = ~N255 /\ ~N246 \/ ~N257 /\ ~N248) /\
  (N249 = ~N246) /\
  (N262 = N261 /\ N246 \/ ~N261 /\ ~N246) /\
  (N41 = ~N240) /\
  (N44 = ~N261) /\
  (N252 = N249 /\ N248 \/ ~N249 /\ ~N248) /\
  (N45 = ~N262) /\
  (N42 = ~N252) /\
  (N46 = ~N42) /\
  (O_4_ = N43) /\
  (O_11_ = N42) /\
  (O_10_ = N41) /\
  (O_9_ = N40) /\
  (O_0_ = N39) /\
  (O_8_ = N38) /\
  (O_2_ = N37) /\
  (O_7_ = N36) /\
  (O_6_ = N35) /\
  (O_5_ = N34) /\
  (O_3_ = N33) /\
  (O_1_ = N32) /\
  (AFTBUF1 = ~ANDA) /\
  (AFTBUF2 = ~ANDB) /\
  (AFTBUF3 = ~EXORA) /\
  (AFTBUF4 = ~EXORB) /\
  (AFTBUF5 = ~CARRYIN) /\
  (N1_0_ = AFTBUF1 /\ A_0_) /\
  (N1_1_ = AFTBUF1 /\ A_1_) /\
  (N1_2_ = AFTBUF1 /\ A_2_) /\
  (N1_3_ = AFTBUF1 /\ A_3_) /\
  (N1_4_ = AFTBUF1 /\ A_4_) /\
  (N1_5_ = AFTBUF1 /\ A_5_) /\
  (N1_6_ = AFTBUF1 /\ A_6_) /\
  (N1_7_ = AFTBUF1 /\ A_7_) /\
  (N1_8_ = AFTBUF1 /\ A_8_) /\
  (N1_9_ = AFTBUF1 /\ A_9_) /\
  (N1_10_ = AFTBUF1 /\ A_10_) /\
  (N1_11_ = AFTBUF1 /\ A_11_) /\
  (N3_0_ = AFTBUF2 /\ B_0_) /\
  (N3_1_ = AFTBUF2 /\ B_1_) /\
  (N3_2_ = AFTBUF2 /\ B_2_) /\
  (N3_3_ = AFTBUF2 /\ B_3_) /\
  (N3_4_ = AFTBUF2 /\ B_4_) /\
  (N3_5_ = AFTBUF2 /\ B_5_) /\
  (N3_6_ = AFTBUF2 /\ B_6_) /\
  (N3_7_ = AFTBUF2 /\ B_7_) /\
  (N3_8_ = AFTBUF2 /\ B_8_) /\
  (N3_9_ = AFTBUF2 /\ B_9_) /\
  (N3_10_ = AFTBUF2 /\ B_10_) /\
  (N3_11_ = AFTBUF2 /\ B_11_) /\
  (N2_0_ = AFTBUF3 /\ ~N1_0_ \/ ~AFTBUF3 /\ N1_0_) /\
  (N2_1_ = AFTBUF3 /\ ~N1_1_ \/ ~AFTBUF3 /\ N1_1_) /\
  (N2_2_ = AFTBUF3 /\ ~N1_2_ \/ ~AFTBUF3 /\ N1_2_) /\
  (N2_3_ = AFTBUF3 /\ ~N1_3_ \/ ~AFTBUF3 /\ N1_3_) /\
  (N2_4_ = AFTBUF3 /\ ~N1_4_ \/ ~AFTBUF3 /\ N1_4_) /\
  (N2_5_ = AFTBUF3 /\ ~N1_5_ \/ ~AFTBUF3 /\ N1_5_) /\
  (N2_6_ = AFTBUF3 /\ ~N1_6_ \/ ~AFTBUF3 /\ N1_6_) /\
  (N2_7_ = AFTBUF3 /\ ~N1_7_ \/ ~AFTBUF3 /\ N1_7_) /\
  (N2_8_ = AFTBUF3 /\ ~N1_8_ \/ ~AFTBUF3 /\ N1_8_) /\
  (N2_9_ = AFTBUF3 /\ ~N1_9_ \/ ~AFTBUF3 /\ N1_9_) /\
  (N2_10_ = AFTBUF3 /\ ~N1_10_ \/ ~AFTBUF3 /\ N1_10_) /\
  (N2_11_ = AFTBUF3 /\ ~N1_11_ \/ ~AFTBUF3 /\ N1_11_) /\
  (N4_0_ = AFTBUF4 /\ ~N3_0_ \/ ~AFTBUF4 /\ N3_0_) /\
  (N4_1_ = AFTBUF4 /\ ~N3_1_ \/ ~AFTBUF4 /\ N3_1_) /\
  (N4_2_ = AFTBUF4 /\ ~N3_2_ \/ ~AFTBUF4 /\ N3_2_) /\
  (N4_3_ = AFTBUF4 /\ ~N3_3_ \/ ~AFTBUF4 /\ N3_3_) /\
  (N4_4_ = AFTBUF4 /\ ~N3_4_ \/ ~AFTBUF4 /\ N3_4_) /\
  (N4_5_ = AFTBUF4 /\ ~N3_5_ \/ ~AFTBUF4 /\ N3_5_) /\
  (N4_6_ = AFTBUF4 /\ ~N3_6_ \/ ~AFTBUF4 /\ N3_6_) /\
  (N4_7_ = AFTBUF4 /\ ~N3_7_ \/ ~AFTBUF4 /\ N3_7_) /\
  (N4_8_ = AFTBUF4 /\ ~N3_8_ \/ ~AFTBUF4 /\ N3_8_) /\
  (N4_9_ = AFTBUF4 /\ ~N3_9_ \/ ~AFTBUF4 /\ N3_9_) /\
  (N4_10_ = AFTBUF4 /\ ~N3_10_ \/ ~AFTBUF4 /\ N3_10_) /\
  (N4_11_ = AFTBUF4 /\ ~N3_11_ \/ ~AFTBUF4 /\ N3_11_) /\
  (COUT1 = AFTBUF5 /\ N4_0_ \/ AFTBUF5 /\ N2_0_ \/ N4_0_ /\ N2_0_) /\
  (COUT2 = COUT1 /\ N4_1_ \/ COUT1 /\ N2_1_ \/ N4_1_ /\ N2_1_) /\
  (COUT3 = COUT2 /\ N4_2_ \/ COUT2 /\ N2_2_ \/ N4_2_ /\ N2_2_) /\
  (COUT4 = COUT3 /\ N4_3_ \/ COUT3 /\ N2_3_ \/ N4_3_ /\ N2_3_) /\
  (COUT5 = COUT4 /\ N4_4_ \/ COUT4 /\ N2_4_ \/ N4_4_ /\ N2_4_) /\
  (COUT6 = COUT5 /\ N4_5_ \/ COUT5 /\ N2_5_ \/ N4_5_ /\ N2_5_) /\
  (COUT7 = COUT6 /\ N4_6_ \/ COUT6 /\ N2_6_ \/ N4_6_ /\ N2_6_) /\
  (COUT8 = COUT7 /\ N4_7_ \/ COUT7 /\ N2_7_ \/ N4_7_ /\ N2_7_) /\
  (COUT9 = COUT8 /\ N4_8_ \/ COUT8 /\ N2_8_ \/ N4_8_ /\ N2_8_) /\
  (COUT10 = COUT9 /\ N4_9_ \/ COUT9 /\ N2_9_ \/ N4_9_ /\ N2_9_) /\
  (COUT11 = COUT10 /\ N4_10_ \/ COUT10 /\ N2_10_ \/ N4_10_ /\ N2_10_) /\
  (HULP0 = ~(N2_0_ = ~(N4_0_ = AFTBUF5))) /\
  (HULP1 = ~(N2_1_ = ~(N4_1_ = COUT1))) /\
  (HULP2 = ~(N2_2_ = ~(N4_2_ = COUT2))) /\
  (HULP3 = ~(N2_3_ = ~(N4_3_ = COUT3))) /\
  (HULP4 = ~(N2_4_ = ~(N4_4_ = COUT4))) /\
  (HULP5 = ~(N2_5_ = ~(N4_5_ = COUT5))) /\
  (HULP6 = ~(N2_6_ = ~(N4_6_ = COUT6))) /\
  (HULP7 = ~(N2_7_ = ~(N4_7_ = COUT7))) /\
  (HULP8 = ~(N2_8_ = ~(N4_8_ = COUT8))) /\
  (HULP9 = ~(N2_9_ = ~(N4_9_ = COUT9))) /\
  (HULP10 = ~(N2_10_ = ~(N4_10_ = COUT10))) /\
  (HULP11 = ~(N2_11_ = ~(N4_11_ = COUT11))) /\
  (HULP12 = COUT11 /\ N4_11_ \/ COUT11 /\ N2_11_ \/  N4_11_ /\ N2_11_)
  ==> (O_0_ = HULP0) /\
      (O_1_ = HULP1) /\
      (O_2_ = HULP2) /\
      (O_3_ = HULP3) /\
      (O_4_ = HULP4) /\
      (O_5_ = HULP5) /\
      (O_6_ = HULP6) /\
      (O_7_ = HULP7) /\
      (O_8_ = HULP8) /\
      (O_9_ = HULP9) /\
      (O_10_ = HULP10) /\                      
      (O_11_ =  HULP11)`;

(* Quick testing
app load ["normalForms", "HolSatLib"];
open canonTools;

val N = mk_neg;

val DN_valid1 = time DEF_CNF_CONV (N valid1);
val DNS_valid1 = time (snd o strip_exists o rhs o concl) DN_valid1;
val DNS_SAT_valid1 = time (HolSatLib.satOracle HolSatLib.zchaff) DNS_valid1;
(* Parsing:     runtime: 7.810s,   gctime: 3.450s,   systime: 0.000s. *)
(* Normalizing: runtime: 897.030s, gctime: 446.330s, systime: 1.270s. *)
(* Stripping:   runtime: 48.160s,  gctime: 26.200s,  systime: 0.020s. *)
(* SAT solving: runtime: 7.480s,   gctime: 0.090s,   systime: 0.020s. *)

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
