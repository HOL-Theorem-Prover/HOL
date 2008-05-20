open HolKernel Parse boolLib bossLib bitTheory
     markerTheory pairTheory arithmeticTheory wordsTheory wordsLib
     Serpent_Bitslice_UtilityTheory;

val _ = new_theory "Serpent_Bitslice_SBox";

(* RNDxxx is the SBox in xxx round, invRNDxxx is the invSBox in xxx round *)

val RND00_def = Define`
  RND00  (a:word32,b:word32,c:word32,d:word32) =
   (let t01 = b ?? c in
    let t02 = a !! d in
    let t03 = a ?? b in
    let z = t02 ?? t01 in
    let t05 = c !! z in
    let t06 = a ?? d in
    let t07 = b !! c in
    let t08 = d && t05 in
    let t09 = t03 && t07 in
    let y = t09 ?? t08 in
    let t11 = t09 && y in
    let t12 = c ?? d in
    let t13 = t07 ?? t11 in
    let t14 = b && t06 in
    let t15 = t06 ?? t13 in
    let w = ~t15 in
    let t17 = w ?? t14 in
    let x = t12 ?? t17 in
      (w,x,y,z))`;

val InvRND00_def = Define`
  InvRND00  (a:word32,b:word32,c:word32,d:word32) =
   (let t01 = c ?? d in
    let t02 = a !! b in
    let t03 = b !! c in
    let t04 = c && t01 in
    let t05 = t02 ?? t01 in
    let t06 = a !! t04 in
    let y = ~t05 in
    let t08 = b ?? d in
    let t09 = t03 && t08 in
    let t10 = d !! y in
    let x = t09 ?? t06 in
    let t12 = a !! t05 in
    let t13 = x ?? t12 in
    let t14 = t03 ?? t10 in
    let t15 = a ?? c in
    let z = t14 ?? t13 in
    let t17 = t05 && t13 in
    let t18 = t14 !! t17 in
    let w = t15 ?? t18 in
      (w,x,y,z))`;

val RND01_def = Define`
  RND01  (a:word32,b:word32,c:word32,d:word32) =
   (let t01 = a !! d in
    let t02 = c ?? d in
    let t03 = ~b in
    let t04 = a ?? c in
    let t05 = a !! t03 in
    let t06 = d && t04 in
    let t07 = t01 && t02 in
    let t08 = b !! t06 in
    let y = t02 ?? t05 in
    let t10 = t07 ?? t08 in
    let t11 = t01 ?? t10 in
    let t12 = y ?? t11 in
    let t13 = b && d in
    let z = ~t10 in
    let x = t13 ?? t12 in
    let t16 = t10 !! x in
    let t17 = t05 && t16 in
    let w = c ?? t17 in
      (w,x,y,z))`;

val InvRND01_def = Define`
  InvRND01  (a:word32,b:word32,c:word32,d:word32) =
   (let t01 = a ?? b in
    let t02 = b !! d in
    let t03 = a && c in
    let t04 = c ?? t02 in
    let t05 = a !! t04 in
    let t06 = t01 && t05 in
    let t07 = d !! t03 in
    let t08 = b ?? t06 in
    let t09 = t07 ?? t06 in
    let t10 = t04 !! t03 in
    let t11 = d && t08 in
    let y = ~t09 in
    let x = t10 ?? t11 in
    let t14 = a !! y in
    let t15 = t06 ?? x in
    let z = t01 ?? t04 in
    let t17 = c ?? t15 in
    let w = t14 ?? t17 in
      (w,x,y,z))`;

val  RND02_def = Define`
    RND02  (a:word32,b:word32,c:word32,d:word32) =
   (let t01 = a !! c in
    let t02 = a ?? b in
    let t03 = d ?? t01 in
    let w = t02 ?? t03 in
    let t05 = c ?? w in
    let t06 = b ?? t05 in
    let t07 = b !! t05 in
    let t08 = t01 && t06 in
    let t09 = t03 ?? t07 in
    let t10 = t02 !! t09 in
    let x = t10 ?? t08 in
    let t12 = a !! d in
    let t13 = t09 ?? x in
    let t14 = b ?? t13 in
    let z = ~t09 in
    let y = t12 ?? t14 in
      (w,x,y,z))`;

val InvRND02_def = Define`
  InvRND02  (a:word32,b:word32,c:word32,d:word32) =
   (let t01 = a ?? d in
    let t02 = c ?? d in
    let t03 = a && c in
    let t04 = b !! t02 in
    let w = t01 ?? t04 in
    let t06 = a !! c in
    let t07 = d !! w in
    let t08 = ~d in
    let t09 = b && t06 in
    let t10 = t08 !! t03 in
    let t11 = b && t07 in
    let t12 = t06 && t02 in
    let z = t09 ?? t10 in
    let x = t12 ?? t11 in
    let t15 = c && z in
    let t16 = w ?? x in
    let t17 = t10 ?? t15 in
    let y = t16 ?? t17 in
      (w,x,y,z))`;

val  RND03_def = Define`
  RND03  (a:word32,b:word32,c:word32,d:word32) =
   (let t01 = a ?? c in
    let t02 = a !! d in
    let t03 = a && d in
    let t04 = t01 && t02 in
    let t05 = b !! t03 in
    let t06 = a && b in
    let t07 = d ?? t04 in
    let t08 = c !! t06 in
    let t09 = b ?? t07 in
    let t10 = d && t05 in
    let t11 = t02 ?? t10 in
    let z = t08 ?? t09 in
    let t13 = d !! z in
    let t14 = a !! t07 in
    let t15 = b && t13 in
    let y = t08 ?? t11 in
    let w = t14 ?? t15 in
    let x = t05 ?? t04 in
      (w,x,y,z))`;

val  InvRND03_def = Define`
  InvRND03  (a:word32,b:word32,c:word32,d:word32) =
   (let t01 = c !! d in
    let t02 = a !! d in
    let t03 = c ?? t02 in
    let t04 = b ?? t02 in
    let t05 = a ?? d in
    let t06 = t04 && t03 in
    let t07 = b && t01 in
    let y = t05 ?? t06 in
    let t09 = a ?? t03 in
    let w = t07 ?? t03 in
    let t11 = w !! t05 in
    let t12 = t09 && t11 in
    let t13 = a && y in
    let t14 = t01 ?? t05 in
    let x = b ?? t12 in
    let t16 = b !! t13 in
    let z = t14 ?? t16 in
      (w,x,y,z))`;

val  RND04_def = Define`
  RND04  (a:word32,b:word32,c:word32,d:word32) =
   (let t01 = a !! b in
    let t02 = b !! c in
    let t03 = a ?? t02 in
    let t04 = b ?? d in
    let t05 = d !! t03 in
    let t06 = d && t01 in
    let z = t03 ?? t06 in
    let t08 = z && t04 in
    let t09 = t04 && t05 in
    let t10 = c ?? t06 in
    let t11 = b && c in
    let t12 = t04 ?? t08 in
    let t13 = t11 !! t03 in
    let t14 = t10 ?? t09 in
    let t15 = a && t05 in
    let t16 = t11 !! t12 in
    let y = t13 ?? t08 in
    let x = t15 ?? t16 in
    let w = ~t14 in
      (w,x,y,z))`;

val  InvRND04_def = Define`
  InvRND04  (a:word32,b:word32,c:word32,d:word32) =
   (let t01 = b !! d in
    let t02 = c !! d in
    let t03 = a && t01 in
    let t04 = b ?? t02 in
    let t05 = c ?? d in
    let t06 = ~t03 in
    let t07 = a && t04 in
    let x = t05 ?? t07 in
    let t09 = x !! t06 in
    let t10 = a ?? t07 in
    let t11 = t01 ?? t09 in
    let t12 = d ?? t04 in
    let t13 = c !! t10 in
    let z = t03 ?? t12 in
    let t15 = a ?? t04 in
    let y = t11 ?? t13 in
    let w = t15 ?? t09 in
      (w,x,y,z))`;

val  RND05_def = Define`
  RND05  (a:word32,b:word32,c:word32,d:word32) =
   (let t01 = b ?? d in
    let t02 = b !! d in
    let t03 = a && t01 in
    let t04 = c ?? t02 in
    let t05 = t03 ?? t04 in
    let w = ~t05 in
    let t07 = a ?? t01 in
    let t08 = d !! w in
    let t09 = b !! t05 in
    let t10 = d ?? t08 in
    let t11 = b !! t07 in
    let t12 = t03 !! w in
    let t13 = t07 !! t10 in
    let t14 = t01 ?? t11 in
    let y = t09 ?? t13 in
    let x = t07 ?? t08 in
    let z = t12 ?? t14 in
      (w,x,y,z))`;

val  InvRND05_def = Define`
  InvRND05  (a:word32,b:word32,c:word32,d:word32) =
   (let t01 = a && d in
    let t02 = c ?? t01 in
    let t03 = a ?? d in
    let t04 = b && t02 in
    let t05 = a && c in
    let w = t03 ?? t04 in
    let t07 = a && w in
    let t08 = t01 ?? w in
    let t09 = b !! t05 in
    let t10 = ~b in
    let x = t08 ?? t09 in
    let t12 = t10 !! t07 in
    let t13 = w !! x in
    let z = t02 ?? t12 in
    let t15 = t02 ?? t13 in
    let t16 = b ?? d in
    let y = t16 ?? t15 in
      (w,x,y,z))`;

val  RND06_def = Define`
  RND06  (a:word32,b:word32,c:word32,d:word32) =
   (let t01 = a && d in
    let t02 = b ?? c in
    let t03 = a ?? d in
    let t04 = t01 ?? t02 in
    let t05 = b !! c in
    let x = ~t04 in
    let t07 = t03 && t05 in
    let t08 = b && x in
    let t09 = a !! c in
    let t10 = t07 ?? t08 in
    let t11 = b !! d in
    let t12 = c ?? t11 in
    let t13 = t09 ?? t10 in
    let y = ~t13 in
    let t15 = x && t03 in
    let z = t12 ?? t07 in
    let t17 = a ?? b in
    let t18 = y ?? t15 in
    let w = t17 ?? t18 in
      (w,x,y,z))`;

val InvRND06_def = Define`
  InvRND06  (a:word32,b:word32,c:word32,d:word32) =
   (let t01 = a ?? c in
    let t02 = ~c in
    let t03 = b && t01 in
    let t04 = b !! t02 in
    let t05 = d !! t03 in
    let t06 = b ?? d in
    let t07 = a && t04 in
    let t08 = a !! t02 in
    let t09 = t07 ?? t05 in
    let x = t06 ?? t08 in
    let w = ~t09 in
    let t12 = b && w in
    let t13 = t01 && t05 in
    let t14 = t01 ?? t12 in
    let t15 = t07 ?? t13 in
    let t16 = d !! t02 in
    let t17 = a ?? x in
    let z = t17 ?? t15 in
    let y = t16 ?? t14 in
      (w,x,y,z))`;

val RND07_def = Define`
  RND07  (a:word32,b:word32,c:word32,d:word32) =
   (let t01 = a && c in
    let t02 = ~d in
    let t03 = a && t02 in
    let t04 = b !! t01 in
    let t05 = a && b in
    let t06 = c ?? t04 in
    let z = t03 ?? t06 in
    let t08 = c !! z in
    let t09 = d !! t05 in
    let t10 = a ?? t08 in
    let t11 = t04 && z in
    let x = t09 ?? t10 in
    let t13 = b ?? x in
    let t14 = t01 ?? x in
    let t15 = c ?? t05 in
    let t16 = t11 !! t13 in
    let t17 = t02 !! t14 in
    let w = t15 ?? t17 in
    let y = a ?? t16 in
      (w,x,y,z))`;

val InvRND07_def = Define`
  InvRND07  (a:word32,b:word32,c:word32,d:word32) =
   (let t01 = a && b in
    let t02 = a !! b in
    let t03 = c !! t01 in
    let t04 = d && t02 in
    let z = t03 ?? t04 in
    let t06 = b ?? t04 in
    let t07 = d ?? z in
    let t08 = ~t07 in
    let t09 = t06 !! t08 in
    let t10 = b ?? d in
    let t11 = a !! d in
    let x = a ?? t09 in
    let t13 = c ?? t06 in
    let t14 = c && t11 in
    let t15 = d !! x in
    let t16 = t01 !! t10 in
    let w = t13 ?? t15 in
    let y = t14 ?? t16 in
      (w,x,y,z))`;

val RND08_def = Define `RND08 b128 = RND00 b128`;
val RND09_def = Define `RND09 b128 = RND01 b128`;
val RND10_def = Define `RND10 b128 = RND02 b128`;
val RND11_def = Define `RND11 b128 = RND03 b128`;
val RND12_def = Define `RND12 b128 = RND04 b128`;
val RND13_def = Define `RND13 b128 = RND05 b128`;
val RND14_def = Define `RND14 b128 = RND06 b128`;
val RND15_def = Define `RND15 b128 = RND07 b128`;
val RND16_def = Define `RND16 b128 = RND00 b128`;
val RND17_def = Define `RND17 b128 = RND01 b128`;
val RND18_def = Define `RND18 b128 = RND02 b128`;
val RND19_def = Define `RND19 b128 = RND03 b128`;
val RND20_def = Define `RND20 b128 = RND04 b128`;
val RND21_def = Define `RND21 b128 = RND05 b128`;
val RND22_def = Define `RND22 b128 = RND06 b128`;
val RND23_def = Define `RND23 b128 = RND07 b128`;
val RND24_def = Define `RND24 b128 = RND00 b128`;
val RND25_def = Define `RND25 b128 = RND01 b128`;
val RND26_def = Define `RND26 b128 = RND02 b128`;
val RND27_def = Define `RND27 b128 = RND03 b128`;
val RND28_def = Define `RND28 b128 = RND04 b128`;
val RND29_def = Define `RND29 b128 = RND05 b128`;
val RND30_def = Define `RND30 b128 = RND06 b128`;
val RND31_def = Define `RND31 b128 = RND07 b128`;

val InvRND08_def = Define `InvRND08 b128 = InvRND00 b128`;
val InvRND09_def = Define `InvRND09 b128 = InvRND01 b128`;
val InvRND10_def = Define `InvRND10 b128 = InvRND02 b128`;
val InvRND11_def = Define `InvRND11 b128 = InvRND03 b128`;
val InvRND12_def = Define `InvRND12 b128 = InvRND04 b128`;
val InvRND13_def = Define `InvRND13 b128 = InvRND05 b128`;
val InvRND14_def = Define `InvRND14 b128 = InvRND06 b128`;
val InvRND15_def = Define `InvRND15 b128 = InvRND07 b128`;
val InvRND16_def = Define `InvRND16 b128 = InvRND00 b128`;
val InvRND17_def = Define `InvRND17 b128 = InvRND01 b128`;
val InvRND18_def = Define `InvRND18 b128 = InvRND02 b128`;
val InvRND19_def = Define `InvRND19 b128 = InvRND03 b128`;
val InvRND20_def = Define `InvRND20 b128 = InvRND04 b128`;
val InvRND21_def = Define `InvRND21 b128 = InvRND05 b128`;
val InvRND22_def = Define `InvRND22 b128 = InvRND06 b128`;
val InvRND23_def = Define `InvRND23 b128 = InvRND07 b128`;
val InvRND24_def = Define `InvRND24 b128 = InvRND00 b128`;
val InvRND25_def = Define `InvRND25 b128 = InvRND01 b128`;
val InvRND26_def = Define `InvRND26 b128 = InvRND02 b128`;
val InvRND27_def = Define `InvRND27 b128 = InvRND03 b128`;
val InvRND28_def = Define `InvRND28 b128 = InvRND04 b128`;
val InvRND29_def = Define `InvRND29 b128 = InvRND05 b128`;
val InvRND30_def = Define `InvRND30 b128 = InvRND06 b128`;
val InvRND31_def = Define `InvRND31 b128 = InvRND07 b128`;

val tac =
  SIMP_TAC std_ss [FORALL_PROD,LET_THM,
    RND00_def,InvRND00_def,RND01_def,InvRND01_def,RND02_def,InvRND02_def,
    RND03_def,InvRND03_def,RND04_def,InvRND04_def,RND05_def,InvRND05_def,
    RND06_def,InvRND06_def,RND07_def,InvRND07_def] THEN
  SRW_TAC [] [] THEN WORD_DECIDE_TAC;
      
val RND00_THM = Q.store_thm("RND00_THM", `!v. InvRND00 (RND00 v) = v`, tac);
val RND01_THM = Q.store_thm("RND01_THM", `!v. InvRND01 (RND01 v) = v`, tac);
val RND02_THM = Q.store_thm("RND02_THM", `!v. InvRND02 (RND02 v) = v`, tac);
val RND03_THM = Q.store_thm("RND03_THM", `!v. InvRND03 (RND03 v) = v`, tac);
val RND04_THM = Q.store_thm("RND04_THM", `!v. InvRND04 (RND04 v) = v`, tac);
val RND05_THM = Q.store_thm("RND05_THM", `!v. InvRND05 (RND05 v) = v`, tac);
val RND06_THM = Q.store_thm("RND06_THM", `!v. InvRND06 (RND06 v) = v`, tac);
val RND07_THM = Q.store_thm("RND07_THM", `!v. InvRND07 (RND07 v) = v`, tac);

val tac = METIS_TAC
  [RND08_def,InvRND08_def,RND09_def,InvRND09_def,RND10_def,InvRND10_def,
   RND11_def,InvRND11_def,RND12_def,InvRND12_def,RND13_def,InvRND13_def,
   RND14_def,InvRND14_def,RND15_def,InvRND15_def,RND16_def,InvRND16_def,
   RND17_def,InvRND17_def,RND18_def,InvRND18_def,RND19_def,InvRND19_def,
   RND20_def,InvRND20_def,RND21_def,InvRND21_def,RND22_def,InvRND22_def,
   RND23_def,InvRND23_def,RND24_def,InvRND24_def,RND25_def,InvRND25_def,
   RND26_def,InvRND26_def,RND27_def,InvRND27_def,RND28_def,InvRND28_def,
   RND29_def,InvRND29_def,RND30_def,InvRND30_def,RND31_def,InvRND31_def,
   RND00_THM,RND01_THM,RND02_THM,RND03_THM,RND04_THM,RND05_THM,RND06_THM,
   RND07_THM];

val RND08_THM = Q.store_thm ("RND08_THM", `!v. InvRND08 (RND08 v) = v`, tac);
val RND09_THM = Q.store_thm ("RND09_THM", `!v. InvRND09 (RND09 v) = v`, tac);
val RND10_THM = Q.store_thm ("RND10_THM", `!v. InvRND10 (RND10 v) = v`, tac);
val RND11_THM = Q.store_thm ("RND11_THM", `!v. InvRND11 (RND11 v) = v`, tac);
val RND12_THM = Q.store_thm ("RND12_THM", `!v. InvRND12 (RND12 v) = v`, tac);
val RND13_THM = Q.store_thm ("RND13_THM", `!v. InvRND13 (RND13 v) = v`, tac);
val RND14_THM = Q.store_thm ("RND14_THM", `!v. InvRND14 (RND14 v) = v`, tac);
val RND15_THM = Q.store_thm ("RND15_THM", `!v. InvRND15 (RND15 v) = v`, tac);
val RND16_THM = Q.store_thm ("RND16_THM", `!v. InvRND16 (RND16 v) = v`, tac);
val RND17_THM = Q.store_thm ("RND17_THM", `!v. InvRND17 (RND17 v) = v`, tac);
val RND18_THM = Q.store_thm ("RND18_THM", `!v. InvRND18 (RND18 v) = v`, tac);
val RND19_THM = Q.store_thm ("RND19_THM", `!v. InvRND19 (RND19 v) = v`, tac);
val RND20_THM = Q.store_thm ("RND20_THM", `!v. InvRND20 (RND20 v) = v`, tac);
val RND21_THM = Q.store_thm ("RND21_THM", `!v. InvRND21 (RND21 v) = v`, tac);
val RND22_THM = Q.store_thm ("RND22_THM", `!v. InvRND22 (RND22 v) = v`, tac);
val RND23_THM = Q.store_thm ("RND23_THM", `!v. InvRND23 (RND23 v) = v`, tac);
val RND24_THM = Q.store_thm ("RND24_THM", `!v. InvRND24 (RND24 v) = v`, tac);
val RND25_THM = Q.store_thm ("RND25_THM", `!v. InvRND25 (RND25 v) = v`, tac);
val RND26_THM = Q.store_thm ("RND26_THM", `!v. InvRND26 (RND26 v) = v`, tac);
val RND27_THM = Q.store_thm ("RND27_THM", `!v. InvRND27 (RND27 v) = v`, tac);
val RND28_THM = Q.store_thm ("RND28_THM", `!v. InvRND28 (RND28 v) = v`, tac);
val RND29_THM = Q.store_thm ("RND29_THM", `!v. InvRND29 (RND29 v) = v`, tac);
val RND30_THM = Q.store_thm ("RND30_THM", `!v. InvRND30 (RND30 v) = v`, tac);
val RND31_THM = Q.store_thm ("RND31_THM", `!v. InvRND31 (RND31 v) = v`, tac);

val _ = export_theory();
