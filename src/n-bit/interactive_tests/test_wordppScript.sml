open HolKernel boolLib Parse wordsLib testutils

val _ = new_theory "test_wordpp";


(********** Helper functions **********)

fun test (expected, s) = tpp_expected {
  input = s, output = expected, testf = standard_tpp_message };

fun concat_type s ty = s ^ " :" ^ ty;

(* Allow specification of word length, without expecting it in output *)
fun test_with_type (ty, (expected, s)) = test (expected, concat_type s ty);

fun remove l ls = filter (fn a => a <> l) ls;

(* Test multiple input formats against a single expected output format *)
fun run_tests tys expected inputs = let
  val inputs' = remove expected inputs
  val tests = List.concat (map (zip tys) (map (zip expected) inputs')) in
  map test_with_type tests end;


(********** Specify tests **********)

val tys = ["word3", "word2", "word10", "word24"];

val default = ["0w", "1w", "42w", "0x10000w"];

val dec = ["0w", "1w", "42w", "65536w"];

val bin = ["0b0w", "0b1w", "0b101010w", "0b10000000000000000w"];

val padded_bin = ["0b000w", "0b01w", "0b0000101010w",
                       "0b000000010000000000000000w"];

val oct = ["00w", "01w", "052w", "0200000w"];

val hex = ["0x0w", "0x1w", "0x2Aw", "0x10000w"];

val padded_hex = ["0x0w", "0x1w", "0x2Aw", "0x010000w"];

val tests = [default, dec, bin, padded_bin, oct, hex, padded_hex];


val tys_neg = ["word8", "word1", "word6", "17 word"];

val default_neg = ["0w", "-1w", "-22w", "-0x10000w"];

val dec_neg = ["0w", "-1w", "-22w", "-65536w"];

val bin_neg = ["0b0w", "-0b1w", "-0b10110w", "-0b10000000000000000w"];

val padded_bin_neg = ["0b00000000w", "-0b1w", "-0b010110w",
                       "-0b10000000000000000w"];

val oct_neg = ["00w", "-01w", "-026w", "-0200000w"];

val hex_neg = ["0x0w", "-0x1w", "-0x16w", "-0x10000w"];

val padded_hex_neg = ["0x00w", "-0x1w", "-0x16w", "-0x10000w"];

(*
val neg_tests = [default_neg, dec_neg, bin_neg, padded_bin_neg, oct_neg,
                 hex_neg, padded_hex_neg];
*)

(********** Execute tests **********)
(* interactive only:
val _ = diemode := FailException
*)
val _ = base_tokens.allow_octal_input := true;

(* Test default printing *)
val _ = tprint "Testing default words output";
val _ = run_tests tys default tests;

(* Test decimal printing *)
val _ = tprint "Testing output_words_as_dec";
val _ = output_words_as_dec();
val _ = run_tests tys dec tests;

(* Test binary printing *)
val _ = tprint "Testing output_words_as_bin";
val _ = output_words_as_bin();
val _ = run_tests tys bin tests;

(* Test padded binary printing *)
val _ = tprint "Testing output_words_as_padded_bin";
val _ = output_words_as_padded_bin();
val _ = run_tests tys padded_bin tests;

(* Test octal printing *)
val _ = tprint "Testing output_words_as_oct";
val _ = output_words_as_oct();
val _ = run_tests tys oct tests;

(* Test hexadecimal printing *)
val _ = tprint "Testing output_words_as_hex";
val _ = output_words_as_hex();
val _ = run_tests tys hex tests;

(* Test padded hexadecimal printing *)
val _ = tprint "Testing output_words_as_padded_hex";
val _ = output_words_as_padded_hex();
val _ = run_tests tys padded_hex tests;

(* Test resetting to default printing *)
val _ = tprint "Testing remove_word_printer";
val _ = remove_word_printer();
val _ = run_tests tys default tests;

(* Test two's complement printing printer *)
val _ = tprint "Testing two's complement printing";
val _ = set_trace "word pp as 2's comp" 1;
val _ = run_tests tys_neg default_neg tests;

val _ = output_words_as_dec();
val _ = run_tests tys_neg dec_neg tests;

val _ = output_words_as_bin();
val _ = run_tests tys_neg bin_neg tests;

val _ = output_words_as_padded_bin();
val _ = run_tests tys_neg padded_bin_neg tests;

val _ = output_words_as_oct();
val _ = run_tests tys_neg oct_neg tests;

val _ = output_words_as_hex();
val _ = run_tests tys_neg hex_neg tests;

val _ = output_words_as_padded_hex();
val _ = run_tests tys_neg padded_hex_neg tests;

val _ = export_theory();

