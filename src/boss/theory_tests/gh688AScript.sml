open HolKernel Parse boolLib bossLib;

open testutils
val _ = new_theory "gh688A";

val _ = add_user_printer("", ``{ y | y < x}``);
val _ = overload_on("foo", ``\x. { y | y < x}``);

val _ = set_trace "Unicode" 0
val _ = List.app tpp ["foo 3", "{x | x <= 10}"]

val _ = export_theory();
