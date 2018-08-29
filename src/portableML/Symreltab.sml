structure Symreltab = Table(
  type key = string * string
  val ord = Portable.pair_compare (String.compare, String.compare)
  fun pp (s1,s2) =
    let
      open HOLPP Portable
    in
      block CONSISTENT 0 [
        add_string "(",
        block CONSISTENT 1 [add_string (mlquote s1), add_string ",",
                            add_break (1,0), add_string (mlquote s2)],
        add_string ")"
      ]
    end
);
