(* ----------------------------------------------------------------------
   Microbenchmark: scaling of `simp[]` cost vs. arith d.p. cache state.

   Hypothesis: per-call cost grows linearly with |cache_F|, the list
   stored under boolSyntax.F in the arith d.p. cache, because every
   call scans that list once per hypothesis-component group.

   Workload: each iteration does

       SIMP_CONV (bool_ss ++ ARITH_ss) [ASSUME (0 < z_i + 1)]
                                       (x_i < y_i)

   with fresh free variables per iteration.  The goal is unprovable
   from arithmetic alone; the hypothesis is an arithmetic theorem
   that gets folded into the RCACHE context.  The decider falls into
   the `prove_false_context` path, which appends one entry to the F
   list per call.

   Run:
       bin/hol run developers/bench-arith-cache.sml | tee /tmp/bench.log

   ---------------------------------------------------------------------- *)

open HolKernel boolLib bossLib simpLib boolSimps;
val () = numLib.prefer_num ();

val arith_cache = numSimps.arith_cache

fun f_list_length () =
    case List.find (aconv boolSyntax.F o #1) (Cache.cache_values arith_cache) of
      NONE => 0
    | SOME (_, lst) => length lst

fun keyspace_size () = length (Cache.cache_values arith_cache)

val () = numSimps.clear_arith_caches ()

val ss = bool_ss ++ numSimps.ARITH_ss

fun num_var s = mk_var (s, numSyntax.num)

fun mk_goal i =
    let val x = num_var ("x" ^ Int.toString i)
        val y = num_var ("y" ^ Int.toString i)
    in numSyntax.mk_less (x, y) end

fun mk_ctxt i =
    let val z = num_var ("z" ^ Int.toString i)
        val one = numSyntax.term_of_int 1
        val zero = numSyntax.term_of_int 0
        val sum = numSyntax.mk_plus (z, one)
    in ASSUME (numSyntax.mk_less (zero, sum)) end

fun bench_iter i =
    let val tm = mk_goal i
        val ctxt = mk_ctxt i
    in
      ignore (SIMP_CONV ss [ctxt] tm
              handle Conv.UNCHANGED => REFL tm
                   | HOL_ERR _ => REFL tm)
    end

fun bench_batch start size =
    let val t0 = Time.now ()
        fun loop i = if i >= start + size then ()
                     else (bench_iter i; loop (i + 1))
        val () = loop start
    in
      Time.- (Time.now (), t0)
    end

val batch_size = 500
val n_batches  = 40

(* Time the construction of `simp []` itself (no goal applied), repeated
   N times, in microseconds.  If this scales with cache state, the cache
   matters at tactic-construction time; if it stays flat, the cost is
   purely in tactic application. *)
fun time_construct_simp n =
    let
      val t0 = Time.now ()
      fun loop i =
          if i >= n then ()
          else (ignore (bossLib.simp [] : tactic); loop (i + 1))
      val () = loop 0
    in
      Time.toMicroseconds (Time.- (Time.now (), t0))
    end

val () = print "Batch    ms  |cache_F|  |keys|  build/1k(us)\n"
val () =
    let
      fun pad n s = StringCvt.padLeft #" " n s
      fun run i =
          if i >= n_batches then ()
          else
            let
              val dt = bench_batch (i * batch_size) batch_size
              val ms = Time.toMilliseconds dt
              val build_us = time_construct_simp 1000
            in
              print (pad 5  (Int.toString (i + 1)) ^ "  " ^
                     pad 4  (LargeInt.toString ms) ^ "  " ^
                     pad 9  (Int.toString (f_list_length ())) ^ "  " ^
                     pad 5  (Int.toString (keyspace_size ())) ^ "  " ^
                     pad 13 (LargeInt.toString build_us) ^ "\n");
              run (i + 1)
            end
    in
      run 0
    end
