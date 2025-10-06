Theory addDB[bare]
Libs
  HolKernel Parse boolLib

val _ = set_trace "Theory.allow_rebinds" 1

Definition foo_def[nocompute]: foo x <=> ~x
End

val th1 = DB.fetch "-" "foo_def"
val th2 = DB.fetch "addDB" "foo_def"

Theorem foo_thm = CONJ TRUTH TRUTH

val th3 = DB.fetch "-" "foo_thm"
val th4 = DB.fetch "addDB" "foo_thm"
val th5 = DB.fetch "-" "foo_def"

Theorem foo_thm = CONJ TRUTH (REFL “t:bool”)

val th6 = DB.fetch "-" "foo_thm"

val _ = length (DB.find "foo_") = 2 orelse raise Fail "bad DB.find"

val _ = length (DB.definitions "-") = 1 orelse raise Fail "bad DB.definitions"
val _ = length (DB.definitions "addDB") = 1 orelse
        raise Fail "bad DB.definitions"
val _ = length (DB.theorems "-") = 1 orelse raise Fail "bad DB.theorems"
val _ = length (DB.theorems "addDB") = 1 orelse raise Fail "bad DB.theorems"

Definition bar_def[nocompute]: bar x <=> x /\ foo x
End

val _ = delete_const "bar"

val _ = length (DB.definitions "-") = 1 orelse raise Fail "bad DB.definitions"


