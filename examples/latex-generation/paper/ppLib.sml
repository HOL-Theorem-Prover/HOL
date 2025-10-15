structure ppLib =
struct

open Parse
open bstTheory

val _ = add_rule {
  term_name = "elemcount",
  fixity = Closefix,
  pp_elements = [TOK "(ec1)", TM, TOK "(ec2)"],
  block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
  paren_style = OnlyIfNecessary
}


end (* struct *)
