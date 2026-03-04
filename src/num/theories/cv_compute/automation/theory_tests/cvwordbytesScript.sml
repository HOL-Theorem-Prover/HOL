Theory cvwordbytes
Ancestors cv_std byte
Libs cv_transLib wordsLib

(* word_of_bytes tests at 32 and 64 bits *)

Theorem word_of_bytes_be_32_ex:
  word_of_bytes_be [9w;3w;11w] = 0x9030b00w : word32
Proof
  CONV_TAC cv_eval
QED

Theorem word_of_bytes_le_32_ex:
  word_of_bytes_le [9w;3w;11w] = 0xb0309w : word32
Proof
  CONV_TAC cv_eval
QED

Theorem word_of_bytes_be_64_ex:
  word_of_bytes_be [9w;3w;11w] = 0x9030b0000000000w : word64
Proof
  CONV_TAC cv_eval
QED

Theorem word_of_bytes_le_64_ex:
  word_of_bytes_le [9w;3w;11w] = 0xb0309w : word64
Proof
  CONV_TAC cv_eval
QED

(* word_to_bytes tests at 32 and 64 bits *)

Theorem word_to_bytes_le_32_ex:
  word_to_bytes_le (0x44332211w : word32) = [0x11w; 0x22w; 0x33w; 0x44w]
Proof
  CONV_TAC cv_eval
QED

Theorem word_to_bytes_be_32_ex:
  word_to_bytes_be (0x44332211w : word32) = [0x44w; 0x33w; 0x22w; 0x11w]
Proof
  CONV_TAC cv_eval
QED

Theorem word_to_bytes_le_64_ex:
  word_to_bytes_le (0x8877665544332211w : word64) =
    [0x11w; 0x22w; 0x33w; 0x44w; 0x55w; 0x66w; 0x77w; 0x88w]
Proof
  CONV_TAC cv_eval
QED

Theorem word_to_bytes_be_64_ex:
  word_to_bytes_be (0x8877665544332211w : word64) =
    [0x88w; 0x77w; 0x66w; 0x55w; 0x44w; 0x33w; 0x22w; 0x11w]
Proof
  CONV_TAC cv_eval
QED

(* Translate at a new type: 128 bits.
   This demonstrates that users can translate word_of_bytes/word_to_bytes
   at any word size where 8 divides dimindex, without defining new constants. *)

val () = cv_trans (word_of_bytes_le_eq_num_of_bytes
                   |> INST_TYPE [alpha |-> “:128”]
                   |> SRULE[dividesTheory.compute_divides]);

val () = cv_trans (word_of_bytes_be_eq_num_of_bytes
                   |> INST_TYPE [alpha |-> “:128”]
                   |> SRULE[dividesTheory.compute_divides]);

val () = cv_trans (word_to_bytes_le_eq_bytes_of_num
                   |> INST_TYPE [alpha |-> “:128”]);

val () = cv_trans (word_to_bytes_be_eq_bytes_of_num
                   |> INST_TYPE [alpha |-> “:128”]);

(* Test 128-bit translations *)

Theorem word_of_bytes_le_128_ex:
  word_of_bytes_le [1w;2w;3w;4w] = 0x04030201w : word128
Proof
  CONV_TAC cv_eval
QED

Theorem word_of_bytes_be_128_ex:
  word_of_bytes_be [1w;2w;3w;4w] = 0x01020304000000000000000000000000w : word128
Proof
  CONV_TAC cv_eval
QED

Theorem word_to_bytes_le_128_ex:
  word_to_bytes_le (0x0102030405060708090a0b0c0d0e0f10w : word128) =
    [0x10w; 0x0fw; 0x0ew; 0x0dw; 0x0cw; 0x0bw; 0x0aw; 0x09w;
     0x08w; 0x07w; 0x06w; 0x05w; 0x04w; 0x03w; 0x02w; 0x01w]
Proof
  CONV_TAC cv_eval
QED

Theorem word_to_bytes_be_128_ex:
  word_to_bytes_be (0x0102030405060708090a0b0c0d0e0f10w : word128) =
    [0x01w; 0x02w; 0x03w; 0x04w; 0x05w; 0x06w; 0x07w; 0x08w;
     0x09w; 0x0aw; 0x0bw; 0x0cw; 0x0dw; 0x0ew; 0x0fw; 0x10w]
Proof
  CONV_TAC cv_eval
QED
