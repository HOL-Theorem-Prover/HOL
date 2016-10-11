open HolKernel Parse boolLib testutils
open sumTheory

val _ = set_trace "Unicode" 0

val _ = tpp "case s of INL b => b | INR c => ~c"
