load "Future";
val realtime = Portable.realtime

signature CMAP = sig
  val cmap : ('a -> 'b) -> 'a list -> 'b list
end
structure CMap : CMAP =
struct
  open Future
  fun cmap f l =
    joins (forks default_params (List.map (fn x => fn () => f x) l))
end;

val cmap = CMap.cmap

fun HOLfact i = EVAL “FACT ^(numSyntax.mk_numeral (Arbnum.fromInt (i + 30)))”

fun hello i = (OS.Process.sleep (Time.fromMilliseconds ((i mod 5) * 100));
               print ("Hello: " ^ LargeInt.toString i ^ "\n");
               i);

val args = List.tabulate(15, (fn i => fn () => hello (LargeInt.fromInt i)));

val _ = print "\n\nHellos (roughly 3s, serially)\n"
val results = realtime Future.joins (Future.forks Future.default_params args);

val _ = print "\nFactorials serially\n"

fun countl n = List.tabulate(n, fn x => x)
fun fact (n:IntInf.int) = if n <= 2 then 1 else n * fact (n - 1)

val large_facts = realtime (cmap HOLfact) (countl 40)

val _ = Multithreading.max_threads_update 1;

val _ = print "\nNow trying in multi-threaded mode\n";
val _ = Multithreading.max_threads_update 0;
val _ = print ("Multithreading number = " ^
               Int.toString (Multithreading.max_threads()) ^ "\n")

val results = realtime Future.joins (Future.forks Future.default_params args);

val _ = print "\nFactorials\n"

val large_facts' = realtime (cmap HOLfact) (countl 40)
