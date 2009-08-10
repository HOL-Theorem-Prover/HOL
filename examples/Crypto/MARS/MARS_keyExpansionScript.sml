(* Interative use:
 quietdec := true;
 app load ["MARS_SboxTheory","MARS_DataTheory"];
 open listTheory wordsTheory MARS_SboxTheory MARS_DataTheory;
 quietdec := false;
*)

open HolKernel Parse boolLib bossLib
     listTheory wordsTheory MARS_SboxTheory MARS_DataTheory;

val _ = new_theory "MARS_keyExpansion";

(****************************************************************************)
(****************************************************************************)
(*------------------Key-Expansion function----------------------------------*)
(*------------------kr is the number of words in the key bufferck[], 4<=kr<=14*)
(*------------------K[] is the expaned key array,consisting of 40 words-----*)
(*------------------T[] is a temporary array, consisting of 15 words--------*)
(*------------------BB[] is a fixed table of four words---------------------*)
(****************************************************************************)


(*----------Now define some array operations on lists-----------------------*)
(*----------"sub" returns the element at designated position ---------------*)
(*----------"update" updates the element at designated position ------------*)

val update_def = Define
   `(update([], i:num, x) = []) /\
    (update(h::t, 0, x) = x::t) /\
    (update(h::t, SUC i, x) = h::update(t,i,x))`;


val sub_def = Define
   `(sub(h::t, 0) = h) /\
    (sub(h::t, SUC i) = sub (t,i))`;


val LENGTH_UPDATE = Q.prove
  (`!l i x. LENGTH (update(l, i, x)) = LENGTH l`,
    Induct_on `l` THENL [
      RW_TAC list_ss [update_def],
      Cases_on `i` THEN
      RW_TAC list_ss [update_def]]
  );

(* --------------------------------------------------------------------------*)
(*   some assistant functions                                                *)
(* --------------------------------------------------------------------------*)

val l8b_def = Define `l8b x = x && 0xffw : word32`;
val l9b_def = Define `l9b x = x && 0x1ffw : word32`;


(*--------------Initialize T[] with the original Key data k[]--------------- *)
(*----Note that the k[] should be in list form-------------------------------*)

(*-------------------Initialize T[] with key data ---------------------------*)
val Init_T_rnd = Define
   `Init_T_rnd i (l:word32 list) k =
      if i = 0 then [HD l] else
      if i > k then (Init_T_rnd (i-1) l k) ++ [0w] else
      if i = k then (Init_T_rnd (i-1) l k) ++ [n2w k] else
      (Init_T_rnd (i-1) l k) ++ [sub(l, i)]`;

val Init_T_def = Define `Init_T(key_list) =
    Init_T_rnd 14 key_list (LENGTH key_list)`;

(*--------------Computing 40 words of K[] based on T[]-----------------------*)
(*--------------Each iteration computes 10 words ----------------------------*)

val  (linear_rnd_def, linear_rnd_ind)  = Defn.tprove (
  Hol_defn "linear_rnd"
   `linear_rnd i t j =
     if i > 14 then t else
       linear_rnd (i+1)
         (update(t, i, ((sub(t, (i-7) MOD 15) ?? sub(t,(i-2) MOD 15)) #<< 3) ??
            (4w * n2w i + n2w j))) j`,
	WF_REL_TAC `measure ($- 15 o FST)`);

val linear_def = Define
    `linear (t, j) = linear_rnd 0 t j`;

(*   Next stir the array T[ ] using four rounds of type-1 Feistel network   *)
val  (stiring_rnd_def, stiring_rnd_ind)  = Defn.tprove (
    Hol_defn "stiring_rnd"
    `stiring_rnd i t j =
        if i > 14 then t else
        stiring_rnd (i+1)
          (update(t, i, (sub(t,i) + Sbox(l9b(sub(t, (i-1) MOD 15)))) #<< 9)) j`,
        WF_REL_TAC `measure ($- 15 o FST)`);

val stiring_step_def = Define
    `stiring_step (t, j) = stiring_rnd 0 t j`;

val stiring_def = Define
    `stiring (t, j) =
      stiring_step(stiring_step(stiring_step(stiring_step(t,j),j),j),j)`;

val store_10_words_def = Define
    `store_10_words (t) =
	[sub(t,0); sub(t,4); sub(t,8); sub(t,12); sub(t,1);
         sub(t,5); sub(t,9); sub(t,13); sub(t,2); sub(t,6)]`;

val Init_K_def = Define
    `Init_K (t) =
	let t1 = store_10_words(stiring(linear(t,0),0)) in
	let t2 = store_10_words(stiring(linear(t1,1),1)) in
	let t3 = store_10_words(stiring(linear(t2,2),2)) in
	let t4 = store_10_words(stiring(linear(t3,3),3)) in
          t1 ++ t2 ++ t3 ++ t4`;

val INIT_K_LENGTH = Q.store_thm
("INIT_K_LENGTH",
 `!t. LENGTH (Init_K t) = 40`,
  RW_TAC list_ss [Init_K_def, store_10_words_def] THEN
  Q.UNABBREV_TAC `t1` THEN Q.UNABBREV_TAC `t2` THEN Q.UNABBREV_TAC `t3` THEN
  Q.UNABBREV_TAC `t4` THEN
  RW_TAC list_ss [LENGTH_APPEND, LENGTH]
);


(*--------------------Modify multiplication keys-----------------------------*)

val BB_def = Define `BB =
    [0xa4a8d57bw; 0x5b5d193bw; 0xc8a8309bw; 0x73f9a978w] : word32 list`;

val gen_mask_def = Define `
  gen_mask(x:word32) =
    let m = (~x ?? (x >> 1)) && 0x7fffffffw in
    let m = m && (m >> 1) && (m >> 2) in
    let m = m && (m >> 3) && (m >> 6) in
    let m1 = m in
    let m = m << 1 in
    let m = m !! (m << 1) in
    let m = m !! (m << 2) in
    let m = m !! (m << 4) in
    let m = m !! (m << 1) && (~x) && 0x80000000w
    in if m1=0w then 0w else m && 0xfffffffcw`;

val mul_rnd_def = Define `
  mul_rnd(k:word32 list,i:num) =
    (* Record the two lowest bits of K[i], by setting j = K[i] & 3, and then
       consider the word with these two bits set to 1, w = K[i] | 3           *)
    let j = w2n (sub(k,i) && 0x3w) in
    let w = sub(k,i) !! 0x3w in

    let m = gen_mask(w) in

    let r = w2n(sub(k,i-1) && 0x1fw) in
    let p = sub(BB,j) #<< r
    in update(k, i, w ?? (p && m))`;

val mul_def = Define `
  mul (k) = mul_rnd(mul_rnd(mul_rnd(mul_rnd(mul_rnd(mul_rnd(mul_rnd(mul_rnd
	(mul_rnd(mul_rnd(mul_rnd(mul_rnd(mul_rnd(mul_rnd(mul_rnd(mul_rnd(k,35),
	33),31),29),27),25),23),21),19),17),15),13),11),9),7),5)`;


val MUL_RND_LENGTH = Q.store_thm
("MUL_RND_LENGTH",
 `!k i. LENGTH (mul_rnd (k, i)) = LENGTH k`,
  SIMP_TAC std_ss [mul_rnd_def, LET_THM]
  THEN RW_TAC list_ss [LENGTH_UPDATE]
);


val key_expansion_def = Define `
  key_expansion(k) = mul(Init_K(Init_T(k)))`;


val KEY_EXPANSION_LENGTH = Q.store_thm
("KEY_EXPANSION_LENGTH",
 `!k. LENGTH (key_expansion k) = 40`,
  SIMP_TAC std_ss [key_expansion_def, mul_def]
  THEN RW_TAC list_ss [INIT_K_LENGTH, MUL_RND_LENGTH]
);


val _ = export_theory();
