(* ----------------------------------------------------------------------
   Why `DEPTH_CONV reduceLib.REDUCE_CONV` is the wrong way to discharge
   numeral equalities, and what to use instead.

   THE FINDING, which is not what it looks like.  `DEPTH_CONV
   reduceLib.REDUCE_CONV` does not merely run slowly on big terms: it
   DOES NOT TERMINATE, on any term at all, including `1 = 2`.

   Cause.  `REDUCE_CONV` is `computeLib.CBV_CONV cs`
   (src/num/reduce/src/reduceLib.sml:83) and `CBV_CONV` never fails --
   handed an irreducible term it returns the reflexive `|- t = t`
   (help/Docfiles/reduceLib.REDUCE_CONV.smd: "Never fails, but may give
   a reflexive equation").  `DEPTH_CONV` is
   `SUB_CONV (DEPTH_CONV conv) THENC REPEATC conv` (src/1/Conv.sml:461),
   and `REPEATC` stops only when its conv raises `UNCHANGED` or
   `HOL_ERR` (src/1/Conv.sml:298).  Neither ever happens, so `REPEATC`
   loops at the first leaf it reaches, accumulating `TRANS`.  Both
   manuals warn of this from their own side; `numSimps.sml:45` guards
   against it with `CHANGED_CONV`.

   So this is a category error, not a tuning problem: `REDUCE_CONV` is
   already a full recursive evaluation and wants calling ONCE, at the
   top.  The conv built for use under a traversal is `RED_CONV`
   (reduceLib.sml:17), a `FIRST_CONV` over the atomic convs with a
   proper `failwith`.

   This file therefore does NOT run `DEPTH_CONV REDUCE_CONV` -- it
   would never return.  It demonstrates the cause (that REDUCE_CONV
   answers reflexively instead of failing), then measures the
   alternatives that do terminate.

   Metric is primitive inferences (`Count`), not wall clock: this VM
   reports steal=0 and cannot see host contention, so seconds here are
   not evidence.  Inference counts are noise-free.

   Run:
       bin/hol run developers/bench-reduce-traversal.sml | tee /tmp/bench.log

   (`bin/hol run FILE`, not stdin: a session fed from stdin prints
   nothing until it exits, so a killed run tells you nothing.)

   Must be run from a directory whose load path reaches stringTheory,
   e.g. examples/diningcryptos -- src/string is not in sigobj after a
   core build.
   ---------------------------------------------------------------------- *)

open HolKernel Parse boolLib bossLib;
val () = List.app load ["stringTheory", "stringSyntax", "numSimps",
                        "extra_stringTheory", "combinTheory", "pairTheory"];
open reduceLib stringSyntax;
val () = numLib.prefer_num ();

fun say s = (print s; TextIO.flushOut TextIO.stdOut);

(* -- the pieces the right conversion is built from --------------------- *)

(* `NEQ_CONV` only checks the equality is at :num; on `x = y` it builds
   a cv term and runs cv_compute before failing, which is real work
   wasted at every non-ground node.  Guard it. *)
fun GROUND_NEQ_CONV tm =
    case Lib.total boolSyntax.dest_eq tm of
        SOME (l, r) => if numSyntax.is_numeral l andalso numSyntax.is_numeral r
                       then NEQ_CONV tm
                       else failwith "GROUND_NEQ_CONV"
      | NONE => failwith "GROUND_NEQ_CONV";

(* A depth traversal with a stop predicate -- HOL4 ships none.
   `TRY_CONV`, not `REPEATC`: the result is `T` or `F`, so a second
   application can never fire, and `REPEATC` is exactly the trap above. *)
fun DEPTH_CONV_SKIP stop conv tm =
    if stop tm then raise Conv.UNCHANGED
    else (Conv.SUB_CONV (DEPTH_CONV_SKIP stop conv)
          THENC Conv.TRY_CONV conv) tm;

(* Stop on TYPE, not on `Literal.is_string_lit`: that walks the spine,
   so using it as the guard would make the traversal quadratic.  A
   :char or :string subterm holds no :bool redex. *)
fun stop t = let val ty = Term.type_of t
             in ty = char_ty orelse ty = string_ty end;

(* -- workload ---------------------------------------------------------- *)

fun subterms tm =
    case dest_term tm of
        COMB (f, x) => 1 + subterms f + subterms x
      | LAMB (v, b) => 1 + subterms v + subterms b
      | _ => 1;

(* Nested if-chain over string keys with unreduced numeral equalities at
   the leaves: the shape the biased dining-cryptographers proofs reach
   once the protocol is unfolded.  `lits` switches the keys between
   string literals and string variables, so the pair isolates exactly
   what descending into literals costs. *)
fun mk_chain lits n =
  let
    fun key i = if lits then fromMLstring ("announces" ^ Int.toString i)
                else mk_var ("k" ^ Int.toString i, string_ty)
    val s = mk_var ("s", string_ty)
    fun payload i = mk_eq (numSyntax.term_of_int i,
                           numSyntax.term_of_int (i + 1))
    fun build i = if i >= n then mk_eq (s, key 999)
                  else mk_cond (mk_eq (s, key i), payload i, build (i + 1))
  in mk_abs (s, build 0) end;

(* The two sides must DIFFER.  `mk_eq (c, c)` is settled by
   reflexivity and measures nothing: the real comparison is between two
   distinct states, which is what the O(n*m) loop in the proof does. *)
fun mk_chain' lits n =
  let
    fun key i = if lits then fromMLstring ("announces" ^ Int.toString i)
                else mk_var ("k" ^ Int.toString i, string_ty)
    val s = mk_var ("s", string_ty)
    fun payload i = mk_eq (numSyntax.term_of_int (i + 1),
                           numSyntax.term_of_int i)
    fun build i = if i >= n then mk_eq (s, key 999)
                  else mk_cond (mk_eq (s, key i), payload i, build (i + 1))
  in mk_abs (s, build 0) end;

fun mk_goal lits n = mk_eq (mk_chain lits n, mk_chain' lits n);

(* -- measurement ------------------------------------------------------- *)

fun run name conv tm =
  let
    val m = Count.mk_meter ()
    val t = Timer.startRealTimer ()
    val outcome = (ignore (conv tm); "ok")
                  handle Conv.UNCHANGED => "unchanged"
                       | HOL_ERR _ => "declined"
                       | Interrupt => raise Interrupt
                       | _ => "ERROR"
    val secs = Time.toReal (Timer.checkRealTimer t)
    val prims = #prims (Count.read m)
  in
    say (StringCvt.padRight #" " 32 name ^
         StringCvt.padLeft #" " 9 (Int.toString prims) ^ " prims " ^
         StringCvt.padLeft #" " 7 (Real.fmt (StringCvt.FIX (SOME 3)) secs) ^
         "s  " ^ outcome ^ "\n");
    prims
  end;

(* -- 1. the cause, demonstrated rather than suffered ------------------- *)

val () = say "\n=== why DEPTH_CONV REDUCE_CONV cannot terminate ===\n";
val () =
  let
    val t = mk_eq (numSyntax.term_of_int 1, numSyntax.term_of_int 2)
    val th = REDUCE_CONV t
    val refl_on_irreducible =
        let val u = mk_eq (mk_var ("x", numSyntax.num),
                           mk_var ("y", numSyntax.num))
        in (let val th' = REDUCE_CONV u
            in "returned " ^ thm_to_string th' ^ "  (reflexive: " ^
               Bool.toString (aconv (lhs (concl th')) (rhs (concl th'))) ^ ")"
            end)
           handle Conv.UNCHANGED => "raised UNCHANGED"
                | HOL_ERR _ => "raised HOL_ERR"
        end
  in
    say ("REDUCE_CONV on a reducible `1 = 2`:   " ^ thm_to_string th ^ "\n");
    say ("REDUCE_CONV on irreducible `x = y`:   " ^ refl_on_irreducible ^ "\n");
    say ("  REPEATC stops only on UNCHANGED/HOL_ERR, so a conv that\n" ^
         "  answers reflexively instead loops forever at the first leaf.\n")
  end;

(* -- 2. the alternatives that do terminate ----------------------------- *)

val SIMP_REDUCE = SIMP_CONV (pure_ss ++ numSimps.REDUCE_ss) [];

fun bench n =
  let
    val gl = mk_goal true n
    val gv = mk_goal false n
    val () = say ("\n--- " ^ Int.toString n ^ " keys: " ^
                  Int.toString (subterms gl) ^ " subterms with literals, " ^
                  Int.toString (subterms gv) ^ " with variables\n")
    val a = run "DEPTH_CONV RED_CONV  (lits)" (DEPTH_CONV RED_CONV) gl
    val b = run "DEPTH_CONV RED_CONV  (vars)" (DEPTH_CONV RED_CONV) gv
    val _ = run "REDUCE_CONV once     (lits)" REDUCE_CONV gl
    val _ = run "REDUCE_CONV once     (vars)" REDUCE_CONV gv
    val _ = run "SIMP + REDUCE_ss     (lits)" SIMP_REDUCE gl
    val _ = run "SKIP + GROUND_NEQ    (lits)"
                  (DEPTH_CONV_SKIP stop GROUND_NEQ_CONV) gl
    val _ = run "SKIP + GROUND_NEQ    (vars)"
                  (DEPTH_CONV_SKIP stop GROUND_NEQ_CONV) gv
  in
    say ("    literal penalty for DEPTH_CONV RED_CONV: " ^
         (if b > 0 then Real.fmt (StringCvt.FIX (SOME 1))
                          (Real.fromInt a / Real.fromInt b) ^ "x prims"
          else "n/a") ^ "\n")
  end;

val () = say "\n=== cost of the alternatives (prims, noise-free) ===\n";
val () = List.app bench [1, 2, 4, 8];

(* -- 3. correctness: a fast conv that does nothing is not a result ----- *)

val () = say "\n=== do the cheap traversals actually discharge `m = n`? ===\n";
val () =
  let
    val g = mk_goal true 2
    val one_eq = mk_eq (numSyntax.term_of_int 1, numSyntax.term_of_int 2)
    fun check nm conv =
      let val r = rhs (concl (conv g))
                  handle Conv.UNCHANGED => g | HOL_ERR _ => g
      in say (StringCvt.padRight #" " 32 nm ^
              "changed=" ^ Bool.toString (not (aconv g r)) ^
              "  `1 = 2` still present=" ^
              Bool.toString (can (find_term (aconv one_eq)) r) ^ "\n")
      end
  in
    check "DEPTH_CONV RED_CONV" (DEPTH_CONV RED_CONV);
    check "SIMP + REDUCE_ss" SIMP_REDUCE;
    check "SKIP + GROUND_NEQ" (DEPTH_CONV_SKIP stop GROUND_NEQ_CONV);
    check "REDUCE_CONV once" REDUCE_CONV
  end;

(* -- 4. EVAL on string literals: the cost, and how to remove it ------ *)

(* EVAL is `computeLib` CBV, so it charges per term node whether or not
   any rule could fire.  On a bare string literal -- nothing to decide,
   already a value -- it costs ~60 primitive inferences per character
   and returns the reflexive `|- "abc" = "abc"`:

       length  1   21 nodes    61 prims
       length  4   81 nodes   241 prims      ~3 prims per term node
       length 16  321 nodes   961 prims

   A CBV over a numeral-only compset with NO string or list rules costs
   exactly the same, so the price is not rule lookup: it is `from_term`
   copying the term into the shadow representation (clauses.sml:309)
   plus `strong` re-deriving each argument (computeLib.sml:233).

   `computeLib.set_skip` does remove it -- but mind two traps.

   TRAP 1: THE ARITY.  `set_skip c (SOME n)` on two-argument `CONS`:

       SOME 0   13 prims   [FACT 8; FACT 8]   nothing evaluated
       SOME 1 2514 prims   [40320; FACT 8]    tail skipped
       SOME 2 5027 prims   [40320; 40320]     NO-OP, same as plain

   `SOME <arity>` is the no-op.  I first wrote `SOME 2` for `CONS` and
   `SOME 1` for `CHR`, measured no difference, and concluded set_skip
   could not help.  It helps entirely.  A claim that a knob does
   nothing needs a positive control showing the knob doing something.

   TRAP 2: IT IS NOT TYPE-AWARE.  `computeLib.set_skip`
   (computeLib.sml:297) destructures `{Name,Thy,...}` and discards the
   type; the compset is keyed on `(Name,Thy)` pairs.  So skipping
   `CONS` stops evaluation inside EVERY list, not just `:char list`:

                      len 1  len 4  len 16   "ab"="az"  [FACT 4; FACT 4]
       EVAL              61    241     961       F          [24; 24]
       skip CHR only     19     73     289       F          [24; 24]
       skip CHR + CONS   13     13      13       F     [FACT 4; FACT 4]

   `CHR : num -> char` is string-specific, so skipping it alone is
   safe: ordinary lists still evaluate, string equality is still
   decided (it comes from rules on `=`, not from normalising the
   literal), and the cost drops 3.3x.  It stays linear in length
   because the CONS spine is still walked.  Skipping CONS as well
   makes it constant, at the price of breaking list evaluation
   everywhere -- too blunt for a shared compset. *)

val SKIP_CHR =
  let val cs = computeLib.copy (computeLib.the_compset ())
      val cs = computeLib.set_skip cs stringSyntax.chr_tm (SOME 0)
  in computeLib.CBV_CONV cs end;

val () = say "\n=== EVAL vs an EVAL that will not enter a character ===\n";
fun evalbench n =
  let
    val gl = mk_goal true n
    val gv = mk_goal false n
    val () = say ("\n--- " ^ Int.toString n ^ " keys\n")
    val a = run "EVAL                 (lits)" EVAL gl
    val b = run "EVAL                 (vars)" EVAL gv
    val c = run "EVAL, CHR skipped    (lits)" SKIP_CHR gl
  in
    say ("    literal penalty " ^
         (if b > 0 then Real.fmt (StringCvt.FIX (SOME 1))
                          (Real.fromInt a / Real.fromInt b) ^ "x" else "n/a") ^
         ";  skipping CHR " ^
         (if c > 0 then Real.fmt (StringCvt.FIX (SOME 1))
                          (Real.fromInt a / Real.fromInt c) ^ "x cheaper"
          else "n/a") ^ "\n")
  end;
val () = List.app evalbench [1, 2, 4, 8];

(* -- 5. does abbreviating the literals pay, for dc_dup_conv? ---------

   CAVEAT, learned the hard way.  This section says yes -- ~4x fewer
   inferences with the prefix abbreviated -- and that conclusion does
   NOT carry to the real proof.  Applying the same abbreviation to
   `biased_dc3_leakage_result` made it *at least* 6x SLOWER (>45 min
   against a ~7 min baseline, at 97% CPU on an unloaded machine) and it
   was abandoned.

   Why the microcosm misleads: here there is ONE prefix and one
   injectivity fact, so the assumption fully replaces what `EVAL` knew.
   In the real proof there are four prefixes compared against each
   other in mixed combinations, and with concrete literals `EVAL`
   decides every such pair directly.  Abbreviate them and that ability
   is gone; whatever the supplied assumptions do not cover now falls
   through to an `EVAL` that can no longer decide it either, and the
   enclosing `REPEATC (CHANGED_CONV ...)` keeps retrying.  Removing a
   capability is not the same as removing a cost.

   So: a benchmark of one prefix cannot settle a question about four.
   Size the microcosm to the real case before trusting it. *)

(* The real conversion from examples/diningcryptos, parameterised by the
   string facts it is given, so the concrete and abbreviated cases can
   be compared on the same code. *)
fun dc_dup_conv_with ths =
  SIMP_CONV (srw_ss()) ([combinTheory.o_DEF, pairTheory.PAIR_EQ] @ ths)
  THENC EVAL
  THENC SIMP_CONV bool_ss ths
  THENC EVAL;

(* Two state functions keyed on a prefix: concrete literal vs variable.
   `pfx` is the prefix term; everything else is identical, so the pair
   isolates exactly what abbreviation buys. *)
val toString_tm = prim_mk_const {Thy = "extra_string", Name = "toString"};
fun num2str t = mk_comb (toString_tm, t);
fun nvar s = mk_var (s, numSyntax.num);

fun mk_state pfx shift n =
  let
    val s = mk_var ("s", string_ty)
    fun key i = mk_strcat (pfx, num2str (numSyntax.term_of_int i))
    fun payload i = mk_eq (numSyntax.term_of_int (i + shift),
                           numSyntax.term_of_int i)
    fun build i = if i >= n then boolSyntax.F
                  else mk_cond (mk_eq (s, key i), payload i, build (i + 1))
  in mk_abs (s, build 0) end;

val () = say "\n=== abbreviation vs concrete literals ===\n";
val () =
  let
    val lit = fromMLstring "announces"
    val abb = mk_var ("announces_str", string_ty)
    (* with the prefix abbreviated the conv can no longer see that two
       keys differ, so it needs the injectivity fact as an assumption --
       exactly what 57abf1f80 threads in via Q.SUBGOAL_THEN *)
    val inj =
      ASSUME (list_mk_forall
                ([nvar "m", nvar "n"],
                 mk_eq (mk_eq (mk_strcat (abb, num2str (nvar "m")),
                               mk_strcat (abb, num2str (nvar "n"))),
                        mk_eq (nvar "m", nvar "n"))))
    fun trial nm pfx ths n =
      let val g = mk_eq (mk_state pfx 1 n, mk_state pfx 2 n)
      in ignore (run nm (dc_dup_conv_with ths) g) end
  in
    List.app (fn n =>
      (say ("\n--- " ^ Int.toString n ^ " keys\n");
       trial "concrete literal prefix" lit
             [extra_stringTheory.STRCAT_toString_inj] n;
       trial "abbreviated prefix (var)" abb [inj] n))
      [2, 4, 8]
  end handle e =>
    say ("abbreviation trial raised: " ^ General.exnMessage e ^ "\n");

val () = say "\ndone\n";
