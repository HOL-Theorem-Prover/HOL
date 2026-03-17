open HolKernel Parse boolLib testutils
open bagTheory

fun pairpr (p1,p2) (x,y) = "(" ^ p1 x ^ "," ^ p2 y ^ ")"
fun listpr p xs = "[" ^ String.concatWith "," (map p xs) ^ "]"

val _ = List.app convtest [
  ("bagSimps.CANCEL_CONV(1)", bagSimps.CANCEL_CONV,
   “b5 + (b1: 'a bag) + b2 + b4 - (b2 + b1)”,
   “(b4:'a bag) + b5 - {||}”),
  ("bagSimps.CANCEL_CONV(2)", bagSimps.CANCEL_CONV,
   “b5 + (b1: 'a bag) + b2 + b4 = b2 + b6 + b1”, “(b4:'a bag) + b5 = b6”),
  ("bagSimps.CANCEL_CONV(3)", bagSimps.CANCEL_CONV,
   “SUB_BAG b2 (b5 + (b1: 'a bag) + b2 + b4)”, “{||} <= b1 + b4 + b5”),
  ("bagSimpleLib.BAG_CARD_CONV(1)", bagSimpleLib.BAG_CARD_CONV,
   “BAG_CARD {| 1; 1; 2 |}”, “3n”),
  ("bagSimpleLib.BAG_CARD_CONV(2)", bagSimpleLib.BAG_CARD_CONV,
   “BAG_CARD {| |}”, “0n”),
  ("bagSimpleLib.BAG_CARD_CONV(3)", bagSimpleLib.BAG_CARD_CONV,
   “BAG_CARD {| 1;2;3;4;5;6 |}”, “6n”),
  ("bagSimpleLib.BAG_CARD_CONV(3)", bagSimpleLib.BAG_CARD_CONV,
   “BAG_CARD (BAG_UNION {| 1;1 |} {| 1;2;3;4;5;6 |})”, “8n”)
];

val _ = tprint "mk_card {| 2; 3 |}"
val _ = require_msg (check_result (aconv “BAG_CARD {| 2; 3 |}”))
                    term_to_string
                    bagSyntax.mk_card
                    “{| 2; 3 |}”

val _ = tprint "list_mk_insert ([“1”,“2”], “{| 3 |}”)"
val _ = require_msg (check_result (aconv “{| 1; 2; 3 |}”))
                    term_to_string
                    bagSyntax.list_mk_insert
                    ([“1”,“2”], “{| 3 |}”)

val _ = shouldfail {
      checkexn = check_HOL_ERRexn (fn (str,f,_) => str = "bagSyntax"),
      printarg = K "dest_sub_bag {| 1 |} (fails)",
      printresult =
      (fn (t1,t2) => "(" ^ term_to_string t1 ^ "," ^ term_to_string t2 ^ ")"),
      testfn = bagSyntax.dest_sub_bag
    } “{| 1 |}”

val _ = tprint "dest_card “BAG_CARD {| 1; 2 |}”"
val _ = require_msg (check_result (aconv “{| 1; 2 |}”))
                    term_to_string
                    bagSyntax.dest_card
                    “BAG_CARD {| 1; 2; |}”

val _ = tprint "dest_card “BAG_CARD {||}”"
val _ = require_msg (check_result (aconv “{||}:bool bag”))
                    term_to_string
                    bagSyntax.dest_card
                    “BAG_CARD ({||}:bool bag)”

val fakeeb = new_constant("EMPTY_BAG", “:num bag”)
val _ = shouldfail {
  checkexn = is_struct_HOL_ERR "bagLib",
  printarg = K "dest_bag with fake empty_BAG",
  printresult = pairpr (listpr term_to_string, type_to_string),
  testfn = bagSyntax.dest_bag}
  “BAG_INSERT 2 scratch$EMPTY_BAG”

val _ = tprint "dest_bag on real empty_bag"
val _ = require_msg (check_result (fn (ts,ty) => null ts andalso ty = bool))
                    (pairpr (listpr term_to_string, type_to_string))
                    bagSyntax.dest_bag
                    “bag$EMPTY_BAG : bool bag”

val _ = tprint "dest_bag on 2-element bag"
val _ = require_msg
          (check_result (fn (ts,ty) => tml_eq [“1n”,“2n”] ts andalso
                                       ty = “:num”))
          (pairpr (listpr term_to_string, type_to_string))
          bagSyntax.dest_bag
          “BAG_INSERT 1n (BAG_INSERT 2n bag$EMPTY_BAG) : num bag”
