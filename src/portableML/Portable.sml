(* ===================================================================== *)
(* FILE          : Portable.sml                                          *)
(* DESCRIPTION   : Structure for SML System dependent functions.         *)
(* AUTHOR        : Ken Larsen, University of Cambridge (or DTU)          *)
(*                 based on code by                                      *)
(*                 Elsa L. Gunter, AT&T Bell Laboratories                *)
(* DATE          : 19 September, 1997                                    *)
(* ===================================================================== *)

(* Copyright 1993 by AT&T Bell Laboratories *)
(* Copyright 1997 by University of Cambridge *)

(* Share and Enjoy *)

structure Portable :> Portable =
struct

exception Div = General.Div
exception Mod = General.Div
exception Interrupt = General.Interrupt

(*---------------------------------------------------------------------------
      Refs
 ---------------------------------------------------------------------------*)

fun inc r = (r := !r + 1)
fun dec r = (r := !r - 1);


(*---------------------------------------------------------------------------
   SML/NJ v.93 style string operations
 ---------------------------------------------------------------------------*)

fun ordof (string,place) = Char.ord(String.sub(string,place))
val implode = String.concat;
val explode = map Char.toString o String.explode;

(*---------------------------------------------------------------------------
    System
 ---------------------------------------------------------------------------*)

val getEnv   = Process.getEnv
val cd       = FileSys.chDir
val pwd      = FileSys.getDir
val listDir  = Mosml.listDir
fun system s = if Process.system s = Process.success then 0 else 1
val getArgs  = CommandLine.arguments
val argv     = getArgs
fun exit()   = Process.exit Process.success


(*---------------------------------------------------------------------------
    IO
 ---------------------------------------------------------------------------*)

exception Io of string;
type instream      = TextIO.instream
type outstream     = TextIO.outstream
val std_out        = TextIO.stdOut
val stdin          = TextIO.stdIn
fun open_in file   = TextIO.openIn file
                     handle General.Io{cause=SysErr(s,_),...} => raise (Io s)
                                   (* handle OS.SysErr (s,_) => raise Io s; *)
fun open_out file  = TextIO.openOut file
                     handle General.Io{cause=SysErr(s,_),...} => raise (Io s)
                                   (* handle OS.SysErr (s,_) => raise Io s; *)
val output         = TextIO.output
fun outputc strm s = output(strm,s)
val close_in       = TextIO.closeIn
val close_out      = TextIO.closeOut
val flush_out      = TextIO.flushOut
val input_line     = TextIO.inputLine
val end_of_stream  = TextIO.endOfStream

(*---------------------------------------------------------------------------
    Efficiency hack.
 ---------------------------------------------------------------------------*)

local val cast : 'a -> int = Obj.magic
in
fun pointer_eq (x:'a, y:'a) = (cast x = cast y)
fun ref_to_int (r : 'a ref) = cast r
end;

(*---------------------------------------------------------------------------
    Time
 ---------------------------------------------------------------------------*)

type time = Time.time

local open Time
in
  val timestamp : unit -> time = now
  val time_to_string : time -> string = toString
  fun dest_time t =
     let val r = toReal t
         val sec = Arbnum.floor (toReal t)
         val sec_million = Arbnum.*(sec, Arbnum.fromInt 1000000)
         val r_million = r * 1000000.0
         val usec = Arbnum.-(Arbnum.floor r_million, sec_million)
     in
        {sec=sec, usec=usec}
     end
  fun mk_time {sec,usec} =
      fromReal (Real.+(Arbnum.toReal sec, Arbnum.toReal usec / 1000000.0))
  fun time_eq (t1:time) t2 = (t1 = t2)
  fun time_lt (t1:time) t2 = Time.<(t1,t2)
end


(*---------------------------------------------------------------------------
    Pretty Printing
 ---------------------------------------------------------------------------*)

open PP

type ppstream = General.ppstream;

fun with_ppstream ppstrm =
  {add_string     = add_string ppstrm,
   add_break      = add_break ppstrm,
   begin_block    = begin_block ppstrm,
   end_block      = fn () => end_block ppstrm,
   add_newline    = fn () => add_newline ppstrm,
   clear_ppstream = fn () => clear_ppstream ppstrm,
   flush_ppstream = fn () => flush_ppstream ppstrm}

fun defaultConsumer () =
   {consumer  = fn s => TextIO.output(TextIO.stdOut, s),
    linewidth = 72,
    flush     = fn () => TextIO.flushOut TextIO.stdOut}

fun pp_to_string linewidth ppfn ob =
    let val l = ref ([]:string list)
	fun attach s = l := (s::(!l))
    in with_pp {consumer = attach,
		linewidth=linewidth, flush = fn()=>()}
               (fn ppstrm =>  ppfn ppstrm ob);
	String.concat(List.rev(!l))
    end

val mk_consumer = fn x => x

(*---------------------------------------------------------------------------*)
(* Generate a standard ppstream                                              *)
(*---------------------------------------------------------------------------*)

fun stdOut_ppstream () = mk_ppstream (defaultConsumer());

(*---------------------------------------------------------------------------
 * Print a list of items.
 *
 *     pfun = print_function
 *     dfun = delim_function
 *     bfun = break_function
 *---------------------------------------------------------------------------*)

fun pr_list_to_ppstream ppstrm pfun dfun bfun =
 let fun pr [] = ()
       | pr [i] = pfun ppstrm i
       | pr (i::rst) = ( pfun ppstrm i; dfun ppstrm ; bfun ppstrm ; pr rst )
 in pr end;


(*---------------------------------------------------------------------------
 * Simple and heavily used.
 * pfun = item printing function
 * dfun = delimiter printing function
 * bfun = break printer function
 *---------------------------------------------------------------------------*)

fun pr_list pfun dfun bfun =
   let fun pr [] = ()
         | pr [i] = pfun i
         | pr (i::rst) = ( pfun i; dfun() ; bfun() ; pr rst )
   in pr end;

(*---------------------------------------------------------------------------*)
(* Send the results of prettyprinting to stdOut                              *)
(*---------------------------------------------------------------------------*)

fun pprint pp x =
 let val strm = stdOut_ppstream ()
 in
   let val _  = pp strm x
   in flush_ppstream strm; ()
   end handle e => (flush_ppstream strm; raise e)
 end;



type 'a frag = 'a General.frag;
type 'a quotation = 'a frag list;

(*---------------------------------------------------------------------------
      MoscowML returns lists of QUOTE'd strings when a quote is spread
      over more than one line. "norm_quote" concatenates all adjacent
      QUOTE elements in this list.
 ---------------------------------------------------------------------------*)

fun norm_quote [] = []
  | norm_quote [x] = [x]
  | norm_quote (QUOTE s1::QUOTE s2::rst) = norm_quote (QUOTE(s1^s2)::rst)
  | norm_quote (h::rst) = h::norm_quote rst;

end (* Portable *)
