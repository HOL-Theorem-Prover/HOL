Theory gh224a[bare]
Libs
  HolKernel Parse boolLib Datatype

val _ = Datatype `bar = <| size : num |>`

val _ = Datatype `A_x = <| y : num |>`
val _ = Datatype `A = <| x : A_x |>`


