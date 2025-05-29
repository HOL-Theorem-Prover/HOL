open HolKernel boolLib bossLib Parse
     listTheory rich_listTheory arithmeticTheory logrootTheory
     bitTheory wordsTheory numposrepTheory byteTheory wordsLib
     (*intLib*)

(* The RIPEMD-160 Specification: https://homes.esat.kuleuven.be/~bosselae/ripemd160/pdf/AB-9601/AB-9601.pdf *)
(* See Appendix A for Pseudo-code for RIPEMD-160 *)

val _ = new_theory"ripemd160";

(* auxiliary function used in chg_end_def *)
Definition chg_end_acc_def:
  (chg_end_acc acc [] = acc) ∧ (chg_end_acc acc (b::bits) = chg_end_acc (TAKE 8 (b::bits) ++ acc) (DROP 8 (b::bits)))
Termination
  WF_REL_TAC`measure (LENGTH o SND)` \\ Cases \\ rw[]
End

Theorem chg_end_acc_sum_leng:
  ∀acc bits. LENGTH $ chg_end_acc acc bits = LENGTH acc + LENGTH bits
Proof
  ho_match_mp_tac chg_end_acc_ind >>
  rw[chg_end_acc_def, listTheory.LENGTH_TAKE_EQ]
QED

(* change bits in little-endian to that in big-endian or vice versa, padding 0s to the left of bits when
   necessary to make the length of bits a multiple of 8 *)
Definition chg_end_def:
  chg_end bits =
  let
    l = LENGTH bits;
    n = l MOD 8;
    k = (8 - n) MOD 8
  in
    chg_end_acc [] $ (REPLICATE k 0 ++ bits)
End

Theorem chg_end_length_multiple:
  divides 8 $ LENGTH (chg_end bits)
Proof
  simp[chg_end_def, chg_end_acc_sum_leng, dividesTheory.DIVIDES_MOD_0] >>
  Cases_on ‘LENGTH bits MOD 8’ >-
   simp[Once $ GSYM MOD_PLUS] >>
  simp[Once $ GSYM MOD_PLUS] >>
  ‘SUC n < 8’ by (
    pop_assum (SUBST1_TAC o GSYM) >>
    simp[MOD_LESS]
  ) >>
  simp[]
QED

Theorem chg_end_length:
  LENGTH (chg_end bits) = LENGTH bits + (8 − LENGTH bits MOD 8) MOD 8
Proof
  rw[chg_end_def,chg_end_acc_sum_leng]
QED

Definition pad_message_def:
  pad_message bits =
  let
    l  = LENGTH bits;
    n  = (l + 1) MOD 512;
    k  = if n <= 448 then 448 - n else 512 + 448 - n;
    lb = chg_end $ PAD_LEFT 0 64 (if l = 0 then [] else REVERSE $ n2l 2 l)
  in
    bits ++ (1 :: REPLICATE k 0) ++ lb
End

Theorem pad_message_length_multiple:
  LENGTH bits < 2 ** 64 ⇒ divides 512 $ LENGTH (pad_message bits)
Proof
  strip_tac>>
  ‘LENGTH (n2l 2 (LENGTH bits)) ≤ 64’ by (
    ‘LENGTH bits ≤ 2 ** 64 - 1’ by decide_tac>>
    Cases_on ‘LENGTH bits’>>
    simp[numposrepTheory.LENGTH_n2l]>>
    ‘0 < SUC n’ by simp[]>>
    drule_then assume_tac logrootTheory.LOG2_LE_MONO>>
    pop_assum $ drule_then assume_tac>>
    gvs[])>>
  rw[pad_message_def]>>gvs[]
  >-simp[chg_end_length,bitstringTheory.length_pad_left]
  >-(
    simp[chg_end_length,bitstringTheory.length_pad_left,ADD1]>>
    cheat
    (*replace cheat by what follows: Cases_on ‘LENGTH (n2l 2 (LENGTH bits)) = 64’
    >-(
      simp[dividesTheory.DIVIDES_MOD_0]
    )
    >-(cheat)*))
  >-(
    simp[chg_end_length,bitstringTheory.length_pad_left,ADD1]>>
    cheat)
QED

Definition parse_block_def:
  parse_block acc bits =
  if NULL bits then REVERSE acc : word32 list
  else parse_block ((word_from_bin_list $ REVERSE $ chg_end $ TAKE 32 bits)::acc) (DROP 32 bits)
Termination
  WF_REL_TAC`measure (LENGTH o SND)` \\ Cases \\ rw[]
End

(* parse bits (assumed to have length that is a multiple of 512) into blocks, each of which is a schedule
   consisting of 16 words of 32 bits *)
Definition parse_message_def:
  parse_message acc bits =
  if NULL bits then REVERSE acc else
  parse_message (parse_block [] (TAKE 512 bits) :: acc) (DROP 512 bits)
Termination
  WF_REL_TAC`measure (LENGTH o SND)` \\ Cases \\ rw[]
End

(* TO DO: Change the last else-branch into an exception *)
Definition f_def:
  f j x y z: word32 =
  if 0 ≤ j ∧ j ≤ 15 then x ?? y ?? z
  else if 16 ≤ j ∧ j ≤ 31 then (x && y) || (¬x && z)
  else if 32 ≤ j ∧ j ≤ 47 then (x || ¬y) ?? z
  else if 48 ≤ j ∧ j ≤ 63 then (x && z) || (y && ¬z)
  else if 64 ≤ j ∧ j ≤ 79 then x ?? (y || ¬z)
  else 0x0w
End

(* TO DO: Change the last else-branch into an exception *)
Definition K_def:
  K j: word32 =
  if 0 ≤ j ∧ j ≤ 15 then 0x00000000w
  else if 16 ≤ j ∧ j ≤ 31 then 0x5A827999w
  else if 32 ≤ j ∧ j ≤ 47 then 0x6ED9EBA1w
  else if 48 ≤ j ∧ j ≤ 63 then 0x8F1BBCDCw
  else if 64 ≤ j ∧ j ≤ 79 then 0xA953FD4Ew
  else 0x0w
End

(* TO DO: Change the last else-branch into an exception *)
Definition K'_def:
  K' j: word32 =
  if 0 ≤ j ∧ j ≤ 15 then 0x50A28BE6w
  else if 16 ≤ j ∧ j ≤ 31 then 0x5C4DD124w
  else if 32 ≤ j ∧ j ≤ 47 then 0x6D703EF3w
  else if 48 ≤ j ∧ j ≤ 63 then 0x7A6D76E9w
  else if 64 ≤ j ∧ j ≤ 79 then 0x00000000w
  else 0x0w
End

Definition rho_def:
  rho n = EL n [7;4;13;1;10;6;15;3;12;0;9;5;2;14;11;8]
End

Definition pi_def:
  pi i = (9 * i + 5) MOD 16
End

Definition r_def:
  r j =
    let
      qt = j DIV 16;
      rm = j MOD 16
    in
      FUNPOW rho qt rm
End

Definition r'_def:
  r' j =
    let
      qt = j DIV 16;
      rm = pi (j MOD 16)
    in
      FUNPOW rho qt rm
End

Definition shift_lookup_table_def:
  shift_lookup_table =
  [[11;14;15;12;5;8;7;9;11;13;14;15;6;7;9;8];
   [12;13;11;15;6;9;9;7;12;15;11;13;7;8;7;7];
   [13;15;14;11;7;7;6;8;13;14;13;12;5;5;6;9];
   [14;11;12;14;8;6;5;5;15;12;15;14;9;9;8;6];
   [15;12;13;13;9;5;8;6;14;11;12;11;8;6;5;5]]
End

Definition s_def:
  s j =
    let
      row = j DIV 16;
      col = r j
    in
      EL col (EL row shift_lookup_table)
End

Definition s'_def:
  s' j =
    let
      row = j DIV 16;
      col = r' j
    in
      EL col (EL row shift_lookup_table)
End

Definition initial_value_def:
  initial_value: word32 # word32 # word32 # word32 # word32 = (0x67452301w, 0xEFCDAB89w, 0x98BADCFEw, 0x10325476w, 0xC3D2E1F0w)
End

Definition rol_def:
  rol n (x: 'a word) = (x << n) || (x >>> (dimindex(:'a) - n))
End

Definition inner_for_loop_def:
  inner_for_loop block (j, (A, B, C, D, E), (A', B', C', D', E')) =
  let
    T1 = rol (s  j) (A  + f j        B  C  D  + EL (r  j) block + K  j) + E;
    T2 = rol (s' j) (A' + f (79 - j) B' C' D' + EL (r' j) block + K' j) + E'
  in
    (SUC j, (E, T1, B, rol 10 C, D), (E', T2, B', rol 10 C', D'))
End

(* the body of the outer for-loop *)
Definition process_block_def:
  process_block (h0, h1, h2, h3, h4) block =
  let
    hs = FUNPOW (inner_for_loop block) 80 (0, (h0, h1, h2, h3, h4), (h0, h1, h2, h3, h4))
  in
    case hs of
      (_, (A, B, C, D, E), (A', B', C', D', E')) =>
          (h1 + C + D', h2 + D + E', h3 + E + A', h4 + A + B', h0 + B + C')
End

Definition outer_for_loop_def:
  outer_for_loop blocks = FOLDL process_block initial_value blocks
End

(* change w (a word of 32 bits) in little-endian to that in big-endian or vice versa *)
Definition word32_chg_end_def:
  word32_chg_end (w: word32): word32 = word_from_bin_list $ REVERSE $ chg_end $ REVERSE $ w2l 2 w
End

Definition RIPEMD_160_def:
  RIPEMD_160 m: 160 word =
  let
    p      = pad_message m;
    blocks = parse_message [] p
  in
    case outer_for_loop blocks of
      (h0, h1, h2, h3, h4) => concat_word_list
                              [(word32_chg_end h4);
                               (word32_chg_end h3);
                               (word32_chg_end h2);
                               (word32_chg_end h1);
                               (word32_chg_end h0)]
End

val _ = export_theory();
