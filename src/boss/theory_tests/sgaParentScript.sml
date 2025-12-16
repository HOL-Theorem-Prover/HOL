Theory sgaParent
Ancestors sgaf2 sgaf1

Theorem test1 = if “sgaf1$f1” ~~ “foo” then TRUTH
                else raise Fail "Unexpected overload resolution"
