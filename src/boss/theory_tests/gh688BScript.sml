Theory gh688B
Ancestors
  gh688A

val _ = HOLFlags.set_bflag (Parse.avoid_unicode, true)
val _ = List.app testutils.tpp ["foo 3", "{x | x <= 10}"]

