load "Future";
val realtime = Portable.realtime


fun hello i = (OS.Process.sleep (Time.fromSeconds (i mod 5));
               print ("Hello: " ^ LargeInt.toString i ^ "\n");
               i);

val args = List.tabulate(15, (fn i => fn () => hello (LargeInt.fromInt i)));

val results = realtime Future.joins (Future.forks Future.default_params args);

val _ = Multithreading.max_threads_update 1;

val _ = print "\nNow trying in multi-threaded mode\n";
val _ = Multithreading.max_threads_update 8;

val results = realtime Future.joins (Future.forks Future.default_params args);
