open HolKernel Parse boolLib testutils

val _ = List.app convtest [
  ("bagSimps.CANCEL_CONV(1)", bagSimps.CANCEL_CONV,
   “b5 + (b1: 'a bag) + b2 + b4 - (b2 + b1)”,
   “(b4:'a bag) + b5 - {||}”),
  ("bagSimps.CANCEL_CONV(2)", bagSimps.CANCEL_CONV,
   “b5 + (b1: 'a bag) + b2 + b4 = b2 + b6 + b1”, “(b4:'a bag) + b5 = b6”),
  ("bagSimps.CANCEL_CONV(3)", bagSimps.CANCEL_CONV,
   “SUB_BAG b2 (b5 + (b1: 'a bag) + b2 + b4)”, “{||} <= b1 + b4 + b5”)
];
