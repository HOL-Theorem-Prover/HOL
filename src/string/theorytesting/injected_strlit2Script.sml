Theory injected_strlit2
Ancestors
  injected_strlit

val _ = testutils.tpp "«foo bar»"

val _ = remove_strliteral_form {tmnm = "SINJ2"}


