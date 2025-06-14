val x = List.hd list = 1 handle Subscript => false

val x = List.length list = 1 andalso List.hd list > 0

infix 5 !!!
fun op!!! _ = false

val x = 10 !!! "hello" : bool

val x = foo bar handle Subscript => false
