open HolKernel Parse boolLib testutils
open bagTheory

val _ = List.app convtest [
  ("bagSimps.CANCEL_CONV(1)", bagSimps.CANCEL_CONV,
   “b5 + (b1: 'a bag) + b2 + b4 - (b2 + b1)”,
   “(b4:'a bag) + b5 - {||}”),
  ("bagSimps.CANCEL_CONV(2)", bagSimps.CANCEL_CONV,
   “b5 + (b1: 'a bag) + b2 + b4 = b2 + b6 + b1”, “(b4:'a bag) + b5 = b6”),
  ("bagSimps.CANCEL_CONV(3)", bagSimps.CANCEL_CONV,
   “SUB_BAG b2 (b5 + (b1: 'a bag) + b2 + b4)”, “{||} <= b1 + b4 + b5”)
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
