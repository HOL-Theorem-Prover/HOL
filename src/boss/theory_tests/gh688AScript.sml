Theory gh688A
Libs
  testutils

val _ = add_user_printer("", ``{ y | y < x}``);
Overload foo = ``\x. { y | y < x}``

val _ = set_trace "Unicode" 0
val _ = List.app tpp ["foo 3", "{x | x <= 10}"]

