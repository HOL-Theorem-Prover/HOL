(* ----------------------------------------------------------------------
   Microbenchmark for the proposed Bloom-filter optimisation of the
   `hypinfo << hypinfo` subset check in src/simp/src/Cache.sml.

   Compares two variants of the check on the same workload:
     nb_subset:   HOLset.isSubset only (current behaviour, after the
                  Redblackset cardinality short-circuit landed)
     bl_subset:   bit-mask Bloom pre-check, then HOLset.isSubset

   Workload: 50 hypinfos modelled on the arith-d.p. recurrence
   bench's pattern (8 hyps each, shared variables a..f, distinct
   K constants).  Bloom is precisely the case it should help:
   cardinality matches across all 50 patterns, so the Redblackset
   short-circuit gives no help, but the terms inside differ
   (different literal constants).

   Verifies both variants agree on every input pair before timing.

   Run:
       bin/hol run developers/claude/bloom_bench.sml
   ---------------------------------------------------------------------- *)

open HolKernel boolLib bossLib;
val () = numLib.prefer_num ();

(* ---------- term hash ---------- *)
val P : Word64.word = 0wx9E3779B185EBCA87  (* splitmix-style constant *)

fun mix (a : Word64.word, b : Word64.word) : Word64.word =
    let val a' = Word64.* (Word64.xorb (a, Word64.>> (a, 0w30)), P)
    in Word64.+ (a', b) end

fun strhash s =
    CharVector.foldl (fn (c, h) => mix (h, Word64.fromInt (Char.ord c)))
                     (0w0 : Word64.word)
                     s

fun term_hash t =
    if is_var t then
      let val (n, _) = dest_var t in strhash n end
    else if is_const t then
      let val {Name, Thy, ...} = dest_thy_const t
      in mix (strhash Thy, strhash Name) end
    else if is_comb t then
      mix (term_hash (rator t), term_hash (rand t))
    else if is_abs t then
      mix (Word64.<< (term_hash (bvar t), 0w3), term_hash (body t))
    else 0w0 : Word64.word

(* Derive three 6-bit positions from the term hash, OR'd into the
   64-bit filter.  Three bits per element keeps false-positive rate
   low for our typical hypset sizes (5-10 elements). *)
fun term_bloom t =
    let
      val h = term_hash t
      val one  = 0w1  : Word64.word
      val mask = 0wx3F : Word64.word
      fun bit shift =
          let val pos = Word64.toInt (Word64.andb (Word64.>> (h, shift), mask))
          in Word64.<< (one, Word.fromInt pos) end
    in
      Word64.orb (Word64.orb (bit 0w0, bit 0w6), bit 0w16)
    end

(* ---------- hypinfo with bloom ---------- *)
type hypinfo_bl = {
  hyps  : term HOLset.set,
  thms  : term HOLset.set,
  bloom : Word64.word
}

val empty_hypinfo_bl : hypinfo_bl =
    {hyps = empty_tmset, thms = empty_tmset, bloom = 0w0 : Word64.word}

fun bl_addth (th, {hyps, thms, bloom}) =
    let
      val newhyps  = hypset th
      val newconcl = concl th
      val hyp_bloom = HOLset.foldl
                        (fn (h, acc) => Word64.orb (acc, term_bloom h))
                        (0w0 : Word64.word) newhyps
      val concl_bloom = term_bloom newconcl
    in
      {hyps = HOLset.union (hyps, newhyps),
       thms = HOLset.add (thms, newconcl),
       bloom = Word64.orb (Word64.orb (bloom, hyp_bloom), concl_bloom)}
    end

(* with Bloom: bit-mask test before the tree walk *)
fun bl_subset ({hyps=h1, thms=t1, bloom=b1} : hypinfo_bl)
              ({hyps=h2, thms=t2, bloom=b2} : hypinfo_bl) : bool =
    Word64.andb (b1, Word64.notb b2) = (0w0 : Word64.word) andalso
    HOLset.isSubset (h1, h2) andalso
    HOLset.isSubset (t1, t2)

(* without Bloom: the existing behaviour.  HOLset.isSubset already
   has the Redblackset cardinality short-circuit committed earlier. *)
fun nb_subset ({hyps=h1, thms=t1, ...} : hypinfo_bl)
              ({hyps=h2, thms=t2, ...} : hypinfo_bl) : bool =
    HOLset.isSubset (h1, h2) andalso HOLset.isSubset (t1, t2)

(* ---------- workload ---------- *)
val a = mk_var ("a", numSyntax.num)
val b = mk_var ("b", numSyntax.num)
val c = mk_var ("c", numSyntax.num)
val d = mk_var ("d", numSyntax.num)
val e = mk_var ("e", numSyntax.num)
val f = mk_var ("f", numSyntax.num)

local open numSyntax in
val sum_abc = mk_plus (mk_plus (a, b), c)
val sum_def = mk_plus (mk_plus (d, e), f)
end

fun mk_hi i =
    let open numSyntax
        val K    = term_of_int (10 + i)
        val K3p1 = term_of_int (3 * (10 + i) + 1)
        val ths = [ASSUME (mk_leq (a, K)),
                   ASSUME (mk_leq (b, K)),
                   ASSUME (mk_leq (c, K)),
                   ASSUME (mk_geq (sum_abc, K3p1)),
                   ASSUME (mk_geq (d, a)),
                   ASSUME (mk_geq (e, b)),
                   ASSUME (mk_geq (f, c)),
                   ASSUME (mk_leq (sum_def, K3p1))]
    in
      List.foldl bl_addth empty_hypinfo_bl ths
    end

val n_hi = 50
val hypinfos = List.tabulate (n_hi, mk_hi)

(* ---------- correctness ---------- *)
val () = print "\n=== Bloom microbench ===\n"
val () = print ("verifying bl_subset and nb_subset agree on all pairs...\n")
val () =
    let
      fun loop_o []        = ()
        | loop_o (q :: qs) =
            (List.app (fn c =>
                 if bl_subset c q = nb_subset c q then ()
                 else (print "MISMATCH detected -- aborting\n";
                       OS.Process.exit OS.Process.failure))
              hypinfos;
             loop_o qs)
    in loop_o hypinfos end
val () = print ("  agreement on " ^ Int.toString (n_hi * n_hi) ^ " pairs OK\n\n")

(* ---------- timing ---------- *)
val n_iter = 100   (* 100 × 50 × 50 = 250,000 subset checks per variant *)

fun bench label sub =
    let
      val t0 = Time.now ()
      fun loop_outer 0 = ()
        | loop_outer i =
            (List.app (fn q =>
                 List.app (fn c => ignore (sub c q)) hypinfos)
              hypinfos;
             loop_outer (i - 1))
      val () = loop_outer n_iter
      val ms = Time.toMilliseconds (Time.- (Time.now (), t0))
    in
      print ("  " ^ label ^ ": " ^ LargeInt.toString ms ^ " ms\n")
    end

val () = print ("workload: " ^ Int.toString n_iter ^ " × " ^
                Int.toString n_hi ^ " × " ^ Int.toString n_hi ^
                " = " ^ Int.toString (n_iter * n_hi * n_hi) ^
                " subset calls per variant\n\n")

(* warm-up to avoid first-run jitter *)
val () = bench "warm-up (nb)" nb_subset

(* three runs each, in alternation, so any GC / load drift hits both *)
val () = bench "nb_subset (no Bloom)  run 1" nb_subset
val () = bench "bl_subset (with Bloom) run 1" bl_subset
val () = bench "nb_subset (no Bloom)  run 2" nb_subset
val () = bench "bl_subset (with Bloom) run 2" bl_subset
val () = bench "nb_subset (no Bloom)  run 3" nb_subset
val () = bench "bl_subset (with Bloom) run 3" bl_subset
val () = print "=== end ===\n\n"
val () = OS.Process.exit OS.Process.success
