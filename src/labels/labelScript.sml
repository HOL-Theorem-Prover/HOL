open HolKernel Parse boolLib

val _ = new_theory "label";

val _ = add_rule { block_style = (AroundEachPhrase, (PP.CONSISTENT, 2)),
                   fixity = Infix(NONASSOC, 80),
                   paren_style = OnlyIfNecessary,
                   pp_elements = [HardSpace 1, TOK ":-", BreakSpace(1,0)],
                   term_name = ":-"};

val _ = new_type ("label", 0);

val label_def = new_definition(
  "label_def",
  ``((lab:label) :- (argument:bool)) = argument``);

val _ = export_theory();
