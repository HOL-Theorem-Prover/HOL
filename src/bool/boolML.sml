structure boolML :> boolML =
struct

fun implies ant conseq = if ant then conseq else true;

val _ = app ConstMapML.insert
           [(boolSyntax.T,           ("Bool","true")),
            (boolSyntax.F,           ("Bool","false")),
            (boolSyntax.negation,    ("Bool","not")),
            (boolSyntax.conjunction, ("","andalso")),
            (boolSyntax.disjunction, ("","orelse")),
            (boolSyntax.implication, ("boolML","implies"))];


end
