Theory sgaChild
Ancestors sgaf1 sgaParent

Theorem test2 = if “foo” ~~ “sgaf1$f1” then TRUTH
                else raise Fail "Unexpected overload resolution"
