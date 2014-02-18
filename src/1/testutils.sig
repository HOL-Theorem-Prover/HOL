signature testutils =
sig

val linewidth : int ref
val die : string -> 'a
val tprint : string -> unit
val tpp : string -> unit
val tpp_expected : {testf:string->string,input:string,output:string} -> unit
val standard_tpp_message : string -> string
val unicode_off : ('a -> 'b) -> 'a -> 'b
val raw_backend : ('a -> 'b) -> 'a -> 'b


end
