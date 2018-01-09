signature testutils =
sig

datatype 'a testresult = Normal of 'a | Exn of exn

val linewidth : int ref
val really_die : bool ref
val OK : unit -> unit
val die : string -> 'a
val tprint : string -> unit
val tadd : string -> unit
val tpp : string -> unit
val tpp_expected : {testf:string->string,input:string,output:string} -> unit
val standard_tpp_message : string -> string
val unicode_off : ('a -> 'b) -> 'a -> 'b
val raw_backend : ('a -> 'b) -> 'a -> 'b
val convtest : (string * (Term.term -> Thm.thm) * Term.term * Term.term) -> unit
val timed : ('a -> 'b) -> ('b testresult -> unit) -> 'a -> unit
val exncheck : ('a -> unit) -> 'a testresult -> unit

val bold : string -> string
val boldred : string -> string
val boldgreen : string -> string
val red : string -> string
val dim : string -> string
val clear : string -> string

end
