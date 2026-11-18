open HolKernel Parse boolLib normalForms metisLib

open testutils;

val _ = new_theory "scratch"

val _ = let
  val p = mk_var("p", bool)
  val q = mk_var("q", bool)
  val v1 = genvar bool
  val v2 = genvar bool
  val t1 = mk_conj(p,q)
  val C = normalForms.PRETTIFY_VARS_CONV
  val gt1 = mk_abs(v1, mk_conj(v1, p))
  val gt2 = list_mk_abs([q, v1,v2], list_mk_conj([p,q,v1,q,v2]))
  fun test (t1,t2) = convtest ("PRETTIFY_CONV "^term_to_string t1, C, t1, t2)
in
  app test [(t1, t1), (mk_abs(p,t1), mk_abs(p,t1)),
            (v1, v1), (gt1, ``\v. v /\ p``),
            (gt2, ``\q v v0. p /\ q /\ v /\ q /\ v0``)]
end

val _ = Parse.reveal "C";

fun normalForms_test (fname, function :conv, problem, result) = let
  val padr = StringCvt.padRight #" ";
  val padl = StringCvt.padLeft #" ";
  val f_s = padr 16 fname;
  val p_s = padr 25 (term_to_string problem);
  val r_s = padl 10 (term_to_string result);
  val _ = tprint (f_s ^ p_s ^ " = " ^ r_s);
in
    require_msg (check_result (fn tm => (result ~~ (rhs (concl tm)))))
                (term_to_string o rhs o concl)
                function (* 'b -> 'a *)
                problem  (* 'b *)
end;

val test_cases =
  [("PRETTIFY_VARS_CONV", PRETTIFY_VARS_CONV,
    (rhs (concl (DEF_CNF_CONV ``~(p <=> q) ==> q /\ r``))),
   ``?v x. (x \/ p \/ q) /\ (x \/ ~p \/ ~q) /\ (p \/ ~q \/ ~x) /\
           (q \/ ~p \/ ~x) /\ (v \/ ~q \/ ~r) /\ (r \/ ~v) /\ (q \/ ~v) /\
           (v \/ x)``),
(* "No numerals currently allowed"
   ("SKI_CONV", SKI_CONV, ``?f. !y. f y = y + 1``,
    ``$? (S (K $!) (S (S (K S) (S (K (S (K $=))) I)) (K (S $+ (K 1)))))``),
 *)
   ("SKI_CONV", SKI_CONV, ``\x:'a. ((f :'a->'a->'a) x o (g :'a->'a))``,
    ``S (S (K $o) (f :'a->'a->'a)) (K (g :'a->'a))``),
   ("SKI_CONV", SKI_CONV, ``\x y. (f :'a->'a->'a) x y``,
    ``S (S (K S) (S (K K) (f :'a->'a->'a))) (K I)``),
   ("SKI_CONV", SKI_CONV, ``$? = \P. P ($@ P)``, ``$? = S I $@``),
   ("SKI_CONV", SKI_CONV, ``$==> = \a b. ~a \/ b``,
    ``$==> = S (S (K S) (S (K K) (S (K $\/) $~))) (K I)``),
   ("SKI_CONV", SKI_CONV, ``$! = \P. K T = P``, ``$! = S (K ($= (K T))) I``),
   ("SKI_CONV", SKI_CONV, ``!x:'a y:'a. P x y``,
    ``$! (S (K $!) (S (S (K S) (S (K K) (P :'a->'a->bool))) (K I)))``),
   ("SKI_CONV", SKI_CONV, ``!x:'a y:'a. P y x``,
    ``$! (S (K $!) (S (K (S (P :'a->'a->bool))) K))``),
   ("SKI_CONV", SKI_CONV, ``(P = Q) <=> (!x. P x <=> Q x)``,
    ``(P = Q <=> $! (S (S (K $<=>) P) Q))``),
(* "No numerals currently allowed"
   ("SKICo_CONV", SKICo_CONV, ``?f. !y. f y = y + 1``,
    ``$? ($! o C (S o $o $=) (C $+ 1))``),
 *)
   ("SKICo_CONV", SKICo_CONV, ``\x:'a. ((f :'a->'a->'a) x o (g :'a->'a))``,
    ``C ($o o (f :'a->'a->'a)) (g :'a->'a)``),
   ("SKICo_CONV", SKICo_CONV, ``\x y. (f :'a->'a->'a) x y``,
    ``C ($o o (f :'a->'a->'a)) I``),
   ("SKICo_CONV", SKICo_CONV, ``$? = \P. P ($@ P)``, ``$? = S I $@``),
   ("SKICo_CONV", SKICo_CONV, ``$==> = \a b. ~a \/ b``,
    ``$==> = C ($o o $\/ o $~) I``),
   ("SKICo_CONV", SKICo_CONV, ``$! = \P. K T = P``, ``$! = $= (K T)``),
   ("SKICo_CONV", SKICo_CONV, ``!x y. (P :'a->'a->bool) x y``,
    ``$! ($! o C ($o o (P :'a->'a->bool)) I)``),
   ("SKICo_CONV", SKICo_CONV, ``!x y. (P :'a->'a->bool) y x``,
    ``$! ($! o C (P :'a->'a->bool))``),
   ("SKICo_CONV", SKICo_CONV, ``(P = Q) = (!x. P x = Q x)``,
    ``(P = Q <=> $! (S ($= o P) Q))``),
   ("SIMPLIFY_CONV", SIMPLIFY_CONV, ``(!x y. P x \/ (P y /\ F)) ==> ?z. P z``,
    ``(!x. P x) ==> ?z. P z``),
   ("NNF_CONV", NNF_CONV, ``(!x. P(x)) ==> ((?y. Q(y)) = (?z. P(z) /\ Q(z)))``,
    ``((?y. Q y) \/ !z. ~P z \/ ~Q z) /\ ((!y. ~Q y) \/ ?z. P z /\ Q z) \/
      ?x. ~P x``),
   ("NNF_CONV", NNF_CONV, ``~(~(x = y) = z) = ~(x = ~(y = z))``,
    ``(((x \/ y) /\ (~x \/ ~y) \/ z) /\ ((x \/ ~y) /\ (~x \/ y) \/ ~z) \/
       (x \/ (y \/ ~z) /\ (~y \/ z)) /\ (~x \/ (y \/ z) /\ (~y \/ ~z))) /\
      (((x \/ y) /\ (~x \/ ~y) \/ ~z) /\ ((x \/ ~y) /\ (~x \/ y) \/ z) \/
       (x \/ (y \/ z) /\ (~y \/ ~z)) /\ (~x \/ (y \/ ~z) /\ (~y \/ z)))``),
   ("SKOLEMIZE_CONV", SKOLEMIZE_CONV,
    ``!x. (?y. Q y \/ !z. ~P z \/ ~Q z) \/ ~P x``,
    ``?y. !x. (Q (y x) \/ !z. ~P z \/ ~Q z) \/ ~P x``),
   ("TAUTOLOGY_CONV", TAUTOLOGY_CONV, ``p \/ r \/ ~p \/ ~q``, T),
   ("CONTRACT_CONV", CONTRACT_CONV, ``(p \/ r) \/ p \/ ~q``, ``r \/ p \/ ~q``)
  ];

val _ = List.app (ignore o normalForms_test) test_cases;

val _ = new_constant("todie", bool)
val c = mk_const("todie", bool)
val _ = delete_const "todie"
fun goalpr _ = "<some goals>"
val _ = shouldfail {
      checkexn = is_struct_HOL_ERR "metisTools",
      printarg = K "Check correct failure on outdated const in thms",
      printresult = goalpr,
      testfn = fn ths => runtac (METIS_TAC ths) ([], “p ==> q”)
    } [ASSUME c]

val _ = shouldfail {
      checkexn = is_struct_HOL_ERR "metisTools",
      printarg = K "Check correct failure on outdated const in goal",
      printresult = goalpr,
      testfn = runtac (METIS_TAC [])
    } ([], mk_imp(c, mk_var("p", bool)))

(* ----------------------------------------------------------------------
    metis.trace governs how loud metis is.  The prover itself reads a
    cache of the flag (mlibUseful.trace_level), so a cache that nobody
    refreshes shows up as dots in the log of every script that calls
    METIS_TAC -- which is what these tests are here to catch.
   ---------------------------------------------------------------------- *)

local
  val tm = “(!x:'a. P x ==> Q x) /\ P a ==> Q a”
  fun said f =
    let
      val buf = ref ([] : string list)
      val saved = !Feedback.MESG_outstream
      val () = Feedback.MESG_outstream := (fn s => buf := s :: !buf)
      fun restore () = Feedback.MESG_outstream := saved
      val _ = f () handle e => (restore(); raise e)
    in
      restore(); String.concat (List.rev (!buf))
    end
  fun at n = HOLFlags.set_flag (metisTools.metis_trace, n)
  fun check nm silent f =
    let
      val _ = tprint nm
      val s = said f
    in
      if (s = "") = silent then OK()
      else if silent then die ("said: " ^ String.toString s)
      else die "said nothing"
    end
  fun tac_on t = runtac t ([], tm)
  val flagnm = HOLFlags.flag_name metisTools.metis_trace
in
val _ = at 0
val _ = check "METIS_TAC is silent at metis.trace = 0" true
              (fn () => tac_on (METIS_TAC []))
val _ = at 1
val _ = check "METIS_TAC chats at metis.trace = 1" false
              (fn () => tac_on (METIS_TAC []))
val _ = check "trace_tac quietens METIS_TAC" true
              (fn () => tac_on (Tactical.trace_tac (flagnm, 0) (METIS_TAC [])))
val _ = check "with_flags quietens METIS_PROVE" true
              (fn () => HOLFlags.with_flags [(metisTools.metis_trace, 0)]
                                            (METIS_PROVE []) tm)
val _ = at 0
end

val _ = Process.exit Process.success;
