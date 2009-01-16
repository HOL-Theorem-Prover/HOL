signature Portable =
sig
  type ppstream  = General.ppstream
  type time      = Time.time
  type instream  = TextIO.instream
  type outstream = TextIO.outstream
  include PP where type break_style = PP.break_style

  val with_ppstream : ppstream
                       -> {add_break      : int * int -> unit,
                           add_newline    : unit -> unit,
                           add_string     : string -> unit,
                           begin_block    : break_style -> int -> unit,
                           clear_ppstream : unit -> unit,
                           end_block      : unit -> unit,
                           flush_ppstream : unit -> unit}

  val mk_consumer : 'a -> 'a
  val defaultConsumer : unit -> {consumer : string -> unit,
                                 flush : unit -> unit,
                                 linewidth : int}
  val stdOut_ppstream : unit -> ppstream
  val pr_list : ('a -> unit) -> (unit -> 'b) -> (unit -> 'c)
                -> 'a list -> unit
  val pr_list_to_ppstream
     : ppstream -> (ppstream -> 'a -> unit)
                  -> (ppstream -> unit)
                   -> (ppstream -> unit) -> 'a list -> unit
  val pprint : (ppstream -> 'a -> unit) -> 'a -> unit

  val dec: int ref -> unit
  val inc: int ref -> unit

  val explode: string -> string list
  val implode: string list -> string
  val ordof: string * int -> int

  val time_eq: time -> time -> bool
  val timestamp: unit -> time
  val mk_time: {sec : Arbnum.num, usec : Arbnum.num} -> time
  val time_to_string: time -> string
  val dest_time: time -> {sec : Arbnum.num, usec : Arbnum.num}
  val time_lt: time -> time -> bool

  val getEnv: string -> string option
  val getArgs: unit -> string list
  val argv: unit -> string list
  val system: string -> int
  val cd: string -> unit
  val pwd: unit -> string
  val listDir: string -> string list
  val exit: unit -> 'a

  val pointer_eq : 'a * 'a -> bool
  val ref_to_int : 'a ref -> int

  val end_of_stream: instream -> bool
  val flush_out: outstream -> unit
  val stdin   : instream
  val std_out : outstream
  val close_out: outstream -> unit
  val output: outstream * string -> unit
  val close_in: instream -> unit
  val open_out: string -> outstream
  val outputc: outstream -> string -> unit
  val input_line: instream -> string
  val open_in : string -> instream
  exception Io of string

  exception Mod
  exception Div
  exception Interrupt

  type 'a quotation = 'a frag list
  type 'a frag = 'a frag

  val norm_quote : 'a quotation -> 'a quotation
end
