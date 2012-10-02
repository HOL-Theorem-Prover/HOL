(*=====================================================================  *)
(* FILE          : quantHeuristicsLibBase.sml                            *)
(* DESCRIPTION   : some code to find instantations for quantified        *)
(*                 variables                                             *)
(*                                                                       *)
(* AUTHORS       : Thomas Tuerk                                          *)
(* DATE          : December 2008                                         *)
(* ===================================================================== *)


structure quantHeuristicsLibBase :> quantHeuristicsLibBase =
struct

(*
quietdec := true;
loadPath :=
            (concat [Globals.HOLDIR, "/src/quantHeuristics"])::
            !loadPath;

map load ["quantHeuristicsTheory"];
load "ConseqConv"
show_assums := true;
quietdec := true;
*)

open HolKernel Parse boolLib Drule ConseqConv simpLib
     quantHeuristicsTheory quantHeuristicsTools pairTools


(*
quietdec := false;
*)

val std_ss = numLib.std_ss



(*******************************************************
 * Traces and other global parameters
 *******************************************************)

val QUANT_INSTANTIATE_HEURISTIC___max_rec_depth = ref 250;

val QUANT_INSTANTIATE_HEURISTIC___debug = ref 0;
val _ = register_trace("QUANT_INSTANTIATE_HEURISTIC", QUANT_INSTANTIATE_HEURISTIC___debug, 3);

val QUANT_INSTANTIATE_HEURISTIC___print_term_length = ref 2000;
val _ = register_trace("QUANT_INSTANTIATE_HEURISTIC___print_term_length", QUANT_INSTANTIATE_HEURISTIC___print_term_length, 2000);


(*******************************************************
 * Some general auxiliary functions
 *******************************************************)

fun mapPartialAcc f acc [] = acc
  | mapPartialAcc f acc (x::xs) =
    let
       val r_opt = f x;
       val acc' = if isSome r_opt then (valOf r_opt)::acc else acc;
    in
       mapPartialAcc f acc' xs
    end;

fun mapPartial f = mapPartialAcc f [];

fun say_HOL_WARNING funname warning =
    Feedback.HOL_WARNING "quantHeuristicsBasicLib" funname warning

fun genvar_RULE thm =
let
   val fvL = free_vars (concl thm)
   val s = map (fn v => (v |-> genvar (type_of v))) fvL

   val type_vL = type_vars_in_term (concl thm)
   val ts = map (fn v => (v |-> gen_tyvar ())) type_vL
in
   INST_TYPE ts (INST s thm)
end;



(*******************************************************
 * Datatype for guesses and some general functions on
 * these guesses
 *******************************************************)


(*Heuristics can come up with guessed instantiations
  of a universal or existential quantifier for different reasons.
  The datatype guess captures these guesses and the reason.

  There are 6 types of guesses with corresponding arguments as
  defined in quantHeuristicsScript.
*)

datatype guess_type =
  gty_exists_point
| gty_forall_point
| gty_exists
| gty_forall
| gty_exists_gap
| gty_forall_gap


fun qh_mk_const n =
   prim_mk_const {Name = n, Thy = "quantHeuristics"}

val GUESS_FORALL_tm = qh_mk_const "GUESS_FORALL";
val GUESS_FORALL_GAP_tm = qh_mk_const "GUESS_FORALL_GAP";
val GUESS_FORALL_POINT_tm = qh_mk_const "GUESS_FORALL_POINT";
val GUESS_EXISTS_tm = qh_mk_const "GUESS_EXISTS";
val GUESS_EXISTS_POINT_tm = qh_mk_const "GUESS_EXISTS_POINT";
val GUESS_EXISTS_GAP_tm = qh_mk_const "GUESS_EXISTS_GAP";

fun guess_type2term gty_exists_point = GUESS_EXISTS_POINT_tm
  | guess_type2term gty_forall_point = GUESS_FORALL_POINT_tm
  | guess_type2term gty_exists       = GUESS_EXISTS_tm
  | guess_type2term gty_forall       = GUESS_FORALL_tm
  | guess_type2term gty_exists_gap   = GUESS_EXISTS_GAP_tm
  | guess_type2term gty_forall_gap   = GUESS_FORALL_GAP_tm

fun guess_type2string gty_exists_point = "guess_exists_point"
  | guess_type2string gty_forall_point = "guess_forall_point"
  | guess_type2string gty_exists       = "guess_exists"
  | guess_type2string gty_forall       = "guess_forall"
  | guess_type2string gty_exists_gap   = "guess_exists_gap"
  | guess_type2string gty_forall_gap   = "guess_forall_gap";

fun guess_term2type gtm =
    if (same_const gtm GUESS_EXISTS_POINT_tm) then gty_exists_point else
    if (same_const gtm GUESS_FORALL_POINT_tm) then gty_forall_point else
    if (same_const gtm GUESS_EXISTS_tm) then gty_exists else
    if (same_const gtm GUESS_FORALL_tm) then gty_forall else
    if (same_const gtm GUESS_EXISTS_GAP_tm) then gty_exists_gap else
    if (same_const gtm GUESS_FORALL_GAP_tm) then gty_forall_gap else
       Feedback.fail();


(*
  All guesses consist of an instatiation and a list of free variables in this instatiation. There might also be
  a justification that might have been proved. The justification of a guess consists of a guess-type accompanied by either a theorem
  or a term. The term/theorem has to correspond to the ML-level information.
  Depending on the guess-type, it has to be a single guess as defined in
  quantHeuristicsScript (either GUESS_FORALL_POINT, GUESS_EXISTS_POINT, GUESS_EXISTS, GUESS_FORALL,  GUESS_EXISTS_GAP or GUESS_FORALL_GAP).
  The list of free variables is mainly used to record names. In the guess theorem/term, only a single variable is allowed.
  A simple example is

  guess_term
    (gty_forall_point,
     ``SUC (y :num) + (z :num)``,
     [``(y :num)``, ``(z :num)``],
     ``GUESS_EXISTS_POINT (λ(x :num # num). SUC (FST x) + SND x)
       (λ(x :num). (P :num -> bool) x)``)

  Look at the ML-function check_guess for a more formal description, please.
*)

datatype guess =
    (* Oracle Guesses *)
    guess_general of term * term list
  | (* formally justified guesses *)
    guess_thm  of guess_type * term * term list * thm
  | (* informally justified guesses *)
    guess_term of guess_type * term * term list * term


(* Some auxiliary functions to check type of guesses and destruct them. *)
fun is_guess_general (guess_general _) = true
  | is_guess_general _ = false;

fun is_guess_thm gty (guess_thm (gty2, _, _, _)) = (gty = gty2)
  | is_guess_thm gty _ = false;

fun is_guess_term gty (guess_term (gty2, _, _, _)) = (gty = gty2)
  | is_guess_term gty _ = false;

fun is_guess gty (guess_term (gty2, _, _, _)) = (gty = gty2)
  | is_guess gty (guess_thm (gty2, _, _, _)) = (gty = gty2)
  | is_guess gty _ = false;

fun guess_extract (guess_general (i,fvL)) = (i,fvL)
  | guess_extract (guess_thm (_,i,fvL,_)) = (i,fvL)
  | guess_extract (guess_term (_,i,fvL,_)) = (i,fvL)

fun guess_extract_thm (guess_thm (ty,i,fvL,thm)) = (ty,i,fvL,thm,true)
  | guess_extract_thm (guess_term (ty,i,fvL,tm)) = (ty,i,fvL,ASSUME tm, false)
  | guess_extract_thm _ = Feedback.fail();

fun guess2term (guess_general (_,_)) = NONE
  | guess2term (guess_thm (_,_,_,thm)) = SOME (concl thm)
  | guess2term (guess_term (_,_,_,tm)) = SOME tm

fun guess2thm (guess_thm (_,_,_,thm)) = (true, thm)
  | guess2thm (guess_term (_,_,_,tm)) = (false,  ASSUME tm)
  | guess2thm _ = Feedback.fail();

fun guess2thm_opt (guess_thm (_,_,_,thm)) = SOME thm
  | guess2thm_opt _ = NONE

fun guess_extract_type (guess_general (i,fvL)) = NONE
  | guess_extract_type (guess_thm (ty,i,fvL,_)) = SOME ty
  | guess_extract_type (guess_term (ty,i,fvL,_)) = SOME ty

fun guess_has_thm (guess_thm _) = true
  | guess_has_thm _ = false;

fun guess_has_no_free_vars guess =
    null (#2 (guess_extract guess));

fun guess_has_thm_no_free_vars guess =
    guess_has_thm guess andalso
    guess_has_no_free_vars guess;

fun guess_thm_to_guess thm_ok ifvL_opt thm =
let
    val (gtm, args) = strip_comb (concl thm);
    val _ = if (length args = 2) then () else Feedback.fail();
    val gty = guess_term2type gtm;
    val (i, fvL) = if isSome ifvL_opt then valOf ifvL_opt else
        let
           val qi_t = el 1 args
           val (_, qi_t) = if is_abs qi_t then (NONE,qi_t) else
               let
                   val fvTy = hd (snd (dest_type (type_of qi_t)));
                   val fv = genvar fvTy;
                   val qi_t' = mk_abs (fv, mk_comb(qi_t,fv));
               in
                   (SOME (GSYM (ETA_CONV qi_t')), qi_t')
               end;
           val (fv, i) = dest_abs qi_t;
       in
          (i, [fv])
       end;
in
   if thm_ok then
      guess_thm (gty, i, fvL, thm)
   else
      guess_term (gty, i, fvL, concl thm)
end;

fun dest_guess_tm t =
let
    val (gtm, args) = strip_comb t;
    val _ = if (length args = 2) then () else Feedback.fail();
    val gty = guess_term2type gtm;
    val (v_t, t_t) = dest_abs (el 2 args)
in
    (gty, (el 1 args), v_t, t_t)
end;

val is_guess_tm = can dest_guess_tm


(*******************************************************
 * Creating guesses in various ways
 *******************************************************)

(*
val v = ``x:num``
val t = ``(P (x:num)):bool``
val i = ``SUC y + z``
val fvL = [``y:num``, ``z:num``]
val base = GUESS_EXISTS_POINT_tm
val gty = gty_forall_point
*)
val unit_ty = Type `:unit`;

fun make_guess_thm_term gty v t i fvL =
let
   val base = guess_type2term gty;
   val vt = mk_abs (v, t);
   val fvL = if null fvL then [genvar unit_ty] else fvL;
   val ip = pairLib.mk_pabs (pairLib.list_mk_pair fvL, i);
   val ip_thm = (pairTools.PABS_ELIM_CONV ip) handle UNCHANGED => REFL ip;
in
   list_mk_icomb (base, [rhs (concl ip_thm), vt])
end;


(* This is the prefered way to generate a well-formed guess *)
fun mk_guess gty v t i fvL =
   guess_term (gty, i, fvL, make_guess_thm_term gty v t i fvL)

fun mk_guess_opt NONE v t i fvL = guess_general(i, fvL)
  | mk_guess_opt (SOME gty) v t i fvL = mk_guess gty v t i fvL


(* Given a guess_term the function is applied to prove the term. *)
fun make_set_guess_thm (guess_term(ty, i, fvL, tm)) proofConv =
    guess_thm (ty, i, fvL, proofConv tm)
  | make_set_guess_thm guess _ =  guess

fun guess_remove_thm v t (guess_thm(ty, i, fvL, thm)) =
    mk_guess ty v t i fvL
  | guess_remove_thm v t (guess_term(ty, i, fvL, tm)) =
    mk_guess ty v t i fvL
  | guess_remove_thm _ _ guess =  guess;

fun guess_thm2term (guess_thm(ty, i, fvL, thm)) =
    guess_term (ty, i, fvL, concl thm)
  | guess_thm2term guess =  guess;


(* A dummy version that just uses mk_thm. *)
fun make_set_guess_thm___dummy guess =
    ((say_HOL_WARNING "make_set_guess_thm_opt___dummy"
		    "mk_thm was used to create a guess");
    make_set_guess_thm guess (fn x => mk_thm ([], x)));

fun make_guess___dummy gty v t i fvL =
     make_set_guess_thm___dummy (mk_guess gty v t i fvL);

(* A dummy version that just uses assume. *)
fun make_set_guess_thm___assume guess =
    make_set_guess_thm guess ASSUME;

fun make_guess___assume gty v t i fvL =
     make_set_guess_thm___assume (mk_guess gty v t i fvL)


(* A simple version that uses the simplifier. Surprisingly, this is often sufficient. *)
fun make_set_guess_thm___simple guess =
     make_set_guess_thm guess (fn x => EQT_ELIM
        (SIMP_CONV std_ss [GUESS_REWRITES] x))

fun make_guess___simple gty v t i fvL =
     make_set_guess_thm___simple (mk_guess gty v t i fvL)


(* A simple version that uses rewrites. *)
fun GUESS_REWRITE_PROVE t =
let
   open metisLib
   val thm = SIMP_CONV std_ss [GUESS_REWRITES] t handle UNCHANGED => REFL t;
   val t2 = rhs (concl thm)
   val thm2 = if t2 = T then TRUTH else METIS_PROVE [] t2;
in
   EQ_MP (GSYM thm) thm2
end;


fun make_guess___rewrite gty v t i fvL =
     make_set_guess_thm (mk_guess gty v t i fvL) GUESS_REWRITE_PROVE


(* Other stuff *)
fun term_list_to_string [] = ""
  | term_list_to_string [t] = (term_to_string t)
  | term_list_to_string (t1::t2::ts) =
    (term_to_string t1)^", "^(term_list_to_string (t2::ts))

fun guess_to_string show_thm (guess_general (i,fvL)) =
    "guess_general (``"^(term_to_string i)^"``, ["^(term_list_to_string fvL)^"])"
  | guess_to_string show_thm (guess_thm (gty, i,fvL,thm)) =
    (guess_type2string gty) ^ " (``"^(term_to_string i)^"``, ["^(term_list_to_string fvL)^"], "^
    (if show_thm then thm_to_string thm else "X")^")"
  | guess_to_string show_thm (guess_term (gty, i,fvL,tm)) =
    (guess_type2string gty) ^ " (``"^(term_to_string i)^"``, ["^(term_list_to_string fvL)^"], ``"^
    (if show_thm then term_to_string tm else "-")^"``)";


(* Checking whether a guess is well-formed and if not try to correct it automatically. *)
fun check_guess v t (guess_general _) = true
  | check_guess v t guess =
   let
      val (i,fvL) = guess_extract guess;
      val ty = valOf (guess_extract_type guess);
      val thm_term2 = valOf (guess2term guess)
      val fvL_t = free_vars t;
      val fvL_i = free_vars i;
      val thm_term = make_guess_thm_term ty v t i fvL
   in
      (type_of v = type_of i) andalso
      (all (fn x => (mem x fvL_i)) fvL) andalso
      (aconv thm_term thm_term2)
   end handle HOL_ERR _ => false;


fun correct_guess v t guess =
   if (check_guess v t guess) then SOME guess else
   let
      val guess2 = guess_remove_thm v t guess handle HOL_ERR _ => guess;
      val still_error = not (check_guess v t guess2);

      val error_msg = if still_error then
                         ("Error in guess: "^(guess_to_string true guess)) else
                         ("Malformed theorem in guess:\n"^(guess_to_string true guess)^
                          "\nTheorem should be of form ``"^
                          (term_to_string (valOf (guess2term guess2))) ^"``.")
      val _ = say_HOL_WARNING "correct_guess" error_msg
   in
      if still_error then NONE else SOME guess2
   end;

fun correct_guess_list v t = mapPartial (correct_guess v t)



(*******************************************************
 * Try to weaken guesses to get guess_exists or guess_forall
 *******************************************************)

local

(*
val t = ``(P (x:num)):bool``
val i = ``(XXX (y:num) (z:num)):num``;
val fvL = [``y:num``,``z:num``]
val v = ``x:num``;

val guess = make_set_guess_thm_opt___dummy v t (guess_forall_gap (i, fvL, NONE));
val (_,_,thm_opt) = guess_extract guess;
val thm = valOf thm_opt

*)

fun guess_type_weaken gty_exists_point = gty_exists
  | guess_type_weaken gty_forall_point = gty_forall
  | guess_type_weaken gty_exists_gap   = gty_exists
  | guess_type_weaken gty_forall_gap   = gty_forall
  | guess_type_weaken gty_exists       = gty_exists
  | guess_type_weaken gty_forall       = gty_forall

val [weaken_thm_forall_gap, weaken_thm_forall_point,
     weaken_thm_exists_point, weaken_thm_exists_gap] = BODY_CONJUNCTS GUESSES_WEAKEN_THM

fun guess_weaken_thm gty_exists_point = weaken_thm_exists_point
  | guess_weaken_thm gty_forall_point = weaken_thm_forall_point
  | guess_weaken_thm gty_exists_gap = weaken_thm_exists_gap
  | guess_weaken_thm gty_forall_gap = weaken_thm_forall_gap
  | guess_weaken_thm _ = Feedback.fail();

in

fun guess_weaken (guess_general (i, fvL)) = guess_general (i,fvL)
  | guess_weaken (guess_term (gty, i, fvL, tm)) =
    if (gty = gty_exists) orelse (gty = gty_forall) then
       (guess_term (gty, i, fvL, tm))
    else
    let
       val gty' = guess_type_weaken gty;
       val b' = guess_type2term gty'
       val (_, args) = strip_comb tm;
       val tm' = list_mk_icomb (b', args);
    in
       (guess_term (gty', i, fvL, tm'))
    end
  | guess_weaken (guess_thm (gty, i, fvL, thm)) =
    if (gty = gty_exists) orelse (gty = gty_forall) then
       (guess_thm (gty, i, fvL, thm))
    else
    let
       val gty' = guess_type_weaken gty;
       val thm' = HO_MATCH_MP (guess_weaken_thm gty) thm;
    in
       guess_thm(gty', i, fvL, thm')
    end;

end


(*******************************************************
 * Collections of guesses
 *
 * There are usually many guesses around. Therefore, they are
 * collected in one datastructure, that separates them after their
 * type.  Moreover, this datastructures also records rewrite theorems
 * that were used to come up with these guesses. These rewrites might
 * then be used later for simplification.
 ********************************************************)

type guess_collection =
   {rewrites     : thm list,
    general      : guess list,
    exists_point : guess list,
    forall_point : guess list,
    exists       : guess list,
    forall       : guess list,
    exists_gap   : guess list,
    forall_gap   : guess list}

fun guess_collection_guess_type gty_exists_point = (#exists_point:guess_collection -> guess list)
  | guess_collection_guess_type gty_forall_point = #forall_point
  | guess_collection_guess_type gty_exists       = #exists
  | guess_collection_guess_type gty_forall       = #forall
  | guess_collection_guess_type gty_exists_gap   = #exists_gap
  | guess_collection_guess_type gty_forall_gap   = #forall_gap

val empty_guess_collection =
   {rewrites     = [],
    general      = [],
    exists_point = [],
    forall_point = [],
    exists       = [],
    forall       = [],
    exists_gap   = [],
    forall_gap   = []}:guess_collection

fun is_empty_guess_collection (gc:guess_collection) =
   (null (#rewrites gc)) andalso
   (null (#general gc)) andalso
   (null (#exists_point gc)) andalso
   (null (#forall_point gc)) andalso
   (null (#exists gc)) andalso
   (null (#forall gc)) andalso
   (null (#exists_gap gc)) andalso
   (null (#forall_gap gc))


fun guess_collection_append (c1:guess_collection) (c2:guess_collection) =
   {rewrites     = append (#rewrites c1) (#rewrites c2),
    general      = append (#general c1) (#general c2),
    exists_point = append (#exists_point c1) (#exists_point c2),
    forall_point = append (#forall_point c1) (#forall_point c2),
    exists       = append (#exists c1) (#exists c2),
    forall       = append (#forall c1) (#forall c2),
    exists_gap   = append (#exists_gap c1) (#exists_gap c2),
    forall_gap   = append (#forall_gap c1) (#forall_gap c2)}:guess_collection


fun guess_collection_flatten [] = empty_guess_collection
  | guess_collection_flatten (NONE::L) = guess_collection_flatten L
  | guess_collection_flatten ((SOME gc)::L) =
    guess_collection_append gc (guess_collection_flatten L);



(* Create a guess-collection from a list of rewrites and a list of guesses by
   sorting the guesses in the right bucket. *)
local
fun guess_list2collection___int gp [] = gp
  | guess_list2collection___int (g1,g3,g4,g5,g6,g7,g8) (guess::gL) =
      let
         val g1 = if (is_guess_general guess) then guess::g1 else g1;
         val g3 = if (is_guess gty_exists_point guess) then guess::g3 else g3;
         val g4 = if (is_guess gty_forall_point guess) then guess::g4 else g4;
         val g5 = if (is_guess gty_exists guess) then guess::g5 else g5;
         val g6 = if (is_guess gty_forall guess) then guess::g6 else g6;
         val g7 = if (is_guess gty_exists_gap guess) then guess::g7 else g7;
         val g8 = if (is_guess gty_forall_gap guess) then guess::g8 else g8;
      in
         guess_list2collection___int (g1,g3,g4,g5,g6,g7,g8) gL
      end;
in
   fun guess_list2collection (rewL, gL) =
   let
      val (g1,g3,g4,g5,g6,g7,g8) = guess_list2collection___int ([],[],[],[],[],[],[]) gL;
   in
      {rewrites = rewL, general = g1, exists_point = g3, forall_point = g4, exists = g5,
       forall = g6, exists_gap = g7, forall_gap = g8}:guess_collection
   end;

end;


fun guess_collection2list (gc:guess_collection) =
  (#rewrites gc,
   flatten [#general gc, #exists_point gc, #forall_point gc, #forall gc,
            #exists gc, #forall_gap gc, #exists_gap gc]);


(*
val guess = hd (#exists gc)
val gc_ref = ref []
val gc = hd (!gc_ref)
*)

fun correct_guess_collection v t (gc:guess_collection) =
  if (!QUANT_INSTANTIATE_HEURISTIC___debug > 0) then
  let
     val gc =
     {rewrites     = #rewrites gc,
      general      = correct_guess_list v t (#general gc),
      exists_point = correct_guess_list v t (#exists_point gc),
      forall_point = correct_guess_list v t (#forall_point gc),
      forall       = correct_guess_list v t (#forall gc),
      exists       = correct_guess_list v t (#exists gc),
      forall_gap   = correct_guess_list v t (#forall_gap gc),
      exists_gap   = correct_guess_list v t (#exists_gap gc)}:guess_collection;

     val _ = if (all (is_guess gty_exists_point) (#exists_point gc)) andalso
                (all (is_guess gty_forall_point) (#forall_point gc)) andalso
                (all is_guess_general (#general gc)) andalso
                (all (is_guess gty_forall) (#forall gc)) andalso
                (all (is_guess gty_exists) (#exists gc)) andalso
                (all (is_guess gty_forall_gap) (#forall_gap gc)) andalso
                (all (is_guess gty_exists_gap) (#exists_gap gc)) then () else
                   say_HOL_WARNING "correct_guess_collection" "Guess-collection-invariant violated!"
  in
     gc
  end else gc;

fun guess_collection___get_exists_weaken (c:guess_collection) =
    append (#exists_point c) (append (#exists c) (#exists_gap c));

fun guess_collection___get_forall_weaken (c:guess_collection) =
    append (#forall_point c) (append (#forall c) (#forall_gap c));



(*******************************************************
 * Cleaning a guess collecion, i.e. removing duplicate
 * guesses or guesses that can be easily derived by weakening
 * stronger ones.
 *******************************************************)

local

fun elim_double_guesses_int r [] = r
  | elim_double_guesses_int r ([]::gLL) =
    elim_double_guesses_int r gLL
  | elim_double_guesses_int r ((((i, fvL),g)::gL)::gLL) =
let
   val already_present = (fvL = [i]) orelse
      exists (fn ((i', fvL'), _) => (i = i') andalso (fvL = fvL')) r
   val r' = if already_present then r else ((i, fvL), g)::r
in
   elim_double_guesses_int r' (gL::gLL)
end;

fun elim_double_guesses gL =
let
   val gL' = map (fn g => (guess_extract g, g)) gL
   val (gL1, gL2) = partition (fn ((_,_),g) =>
               guess_has_thm g) gL';
in
   map snd (elim_double_guesses_int [] [gL1, gL2])
end;


fun clean_guess (guess_thm (gty, i, fvL, thm)) =
let
   val i' = rand (rator (concl thm));
   val thm' = if is_abs i' then thm else
      let
         val ty = hd (snd (dest_type (type_of i')))
         val v = genvar ty
         val xthm = ETA_CONV (mk_abs(v, mk_comb (i', v)));
      in
         (CONV_RULE (RATOR_CONV (RAND_CONV (K (GSYM xthm)))) thm)
      end
in
   guess_thm (gty, i, fvL, thm')
end
| clean_guess (guess_term (gty, i, fvL, tm)) =
  let
     val (b, args) = strip_comb tm;
     val i' = hd args;
     val i' = if is_abs i' then i' else
      let
         val ty = hd (snd (dest_type (type_of i')))
         val v = genvar ty
      in
         mk_abs (v, mk_comb (i', v))
      end
     val tm' = list_mk_comb (b, [i', el 2 args])
  in
     guess_term (gty, i, fvL, tm')
  end
| clean_guess guess = guess;


fun elim_clean_guesses gL =
   map clean_guess (elim_double_guesses gL);

in

fun guess_collection_clean (c:guess_collection) =
   {rewrites     = #rewrites c,
    general      = #general c,
    exists_point = elim_clean_guesses (#exists_point c),
    forall_point = elim_clean_guesses (#forall_point c),
    exists       = elim_clean_guesses (map guess_weaken (guess_collection___get_exists_weaken c)),
    forall       = elim_clean_guesses (map guess_weaken (guess_collection___get_forall_weaken c)),
    exists_gap   = elim_clean_guesses (#exists_gap c),
    forall_gap   = elim_clean_guesses (#forall_gap c)}: guess_collection

end;







(*******************************************************
 *
 * Heuristics for the common boolean operations
 *
 *******************************************************)

(* A basic quantifier heuristics gets two arguments v and t.
   It then tries to find guesses for "\v. t". *)
type quant_heuristic_base = term -> term -> guess_collection;

(* Often quantifier heuristics need to get guesses for subterms.
   Therefore, they get an additional argument that can be used
   as a system callback to get guesses for subterms. *)
type quant_heuristic = quant_heuristic_base -> quant_heuristic_base;

(* If a heuristic does not find any guesses, this exception is
   thrown *)
exception QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;


(* Dummy system callbacks that are handy for debugging.

fun dummy_term_sys v t =
let
   val i = mk_var ("i", type_of v);
   val fvL = [];
in
   {rewrites            = [],
    general             = [],
    exists_point                = [mk_guess gty_exists_point v t i fvL],
    forall_point               = [mk_guess gty_forall_point v t i fvL],
    exists              = [mk_guess gty_exists v t i fvL],
    forall              = [mk_guess gty_forall v t i fvL],
    exists_gap       = [mk_guess gty_exists_gap v t i fvL],
    forall_gap       = [mk_guess gty_forall_gap v t i fvL]}
end;

fun dummy_sys v t =
let
   val i = mk_var ("i", type_of v);
   val fvL = [];
in
   {rewrites            = [],
    general             = [],
    exists_point                = [make_guess___dummy gty_exists_point v t i fvL],
    forall_point               = [make_guess___dummy gty_forall_point v t i fvL],
    exists              = [make_guess___dummy gty_exists v t i fvL],
    forall              = [make_guess___dummy gty_forall v t i fvL],
    exists_gap       = [make_guess___dummy gty_exists_gap v t i fvL],
    forall_gap       = [make_guess___dummy gty_forall_gap v t i fvL]}
end;

*)


(*********************************
 * Simple heuristic for Booleans
 *********************************)

(*
  val t = ``x:bool``
  val v = t
*)

fun QUANT_INSTANTIATE_HEURISTIC___BOOL sys v t =
let
   val _ = if (aconv v t) then () else raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;
in
  {rewrites     = [],
   general      = [],
   exists_point = [make_guess___simple gty_exists_point v t T []],
   forall_point = [make_guess___simple gty_forall_point v t F []],
   forall       = [],
   exists       = [],
   forall_gap   = [make_guess___simple gty_forall_gap v t F []],
   exists_gap   = [make_guess___simple gty_exists_gap v t T []]}
end;


(*********************************
 * Heuristic for equations
 *********************************)

(*
val t = ``7 + y + z = (x:num)``;
val t = ``x:'a = f y``;
val t = ``f y = x:'a``;
val t = ``x + y = x + z``;
val v = ``x:'a``
val t = ``(f (y':'b)):'a = f y``
val v = ``y':'b``
val sys = dummy_sys
*)


fun QUANT_INSTANTIATE_HEURISTIC___EQUATION sys v t =
let
   val _ = if (is_eq t) then () else raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;
   val (l,r) = dest_eq t;

   val (turn,top,i,s) = if (l = v) then (false, true, r,r) else
		        if (r = v) then (true,  true, l,l) else
		      (false, false, match_term_var v l r, r) handle HOL_ERR _ =>
		      (true,  false, match_term_var v r l, l) handle HOL_ERR _ =>
		      raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;

   val _ = if (free_in v i) then Feedback.fail () else ();
   val u_genvar = genvar unit_ty;

   val g_exists_pointL = let
      val v_l = mk_abs (v, l);
      val v_r = mk_abs (v, r);
      val g_exists_point_thm  = ISPECL [i, v_l, v_r] GUESS_RULES_EQUATION_EXISTS_POINT
      val g_exists_point_thm2 = CONV_RULE (
         RATOR_CONV (RAND_CONV (BINOP_CONV BETA_CONV)) THENC
         RAND_CONV (RAND_CONV (ALPHA_CONV v THENC (ABS_CONV ((BINOP_CONV BETA_CONV)))))) g_exists_point_thm
      val pre = (lhs o fst o dest_imp o concl) g_exists_point_thm2;
      val g_exists_point_thm3 = MP g_exists_point_thm2 (REFL pre)
      val g_exists_point_thm4 = CONV_RULE (RATOR_CONV (RAND_CONV (ALPHA_CONV u_genvar))) g_exists_point_thm3
   in
      [guess_thm (gty_exists_point, i, [], g_exists_point_thm4)]
   end

   val g_exists_gapL = if not top then [] else let
      val g_thm0 = ISPEC i GUESS_RULES_EQUATION_EXISTS_GAP;
      val g_thm1 = if turn then CONV_RULE (RAND_CONV (ABS_CONV SYM_CONV)) g_thm0 else g_thm0
      val g_thm2 = CONV_RULE (RAND_CONV (ALPHA_CONV v)) g_thm1
      val g_thm3 = CONV_RULE (RATOR_CONV (RAND_CONV (ALPHA_CONV u_genvar))) g_thm2
   in
      [guess_thm (gty_exists_gap, i, [], g_thm3)]
   end
in
  {rewrites     = [],
   general      = [],
   exists_point = g_exists_pointL,
   forall_point = [],
   forall       = [],
   exists       = [],
   forall_gap   = [],
   exists_gap   = g_exists_gapL}:guess_collection
end;


(*********************************************
 * Heuristic for monochotomies and dichotomies
 *********************************************)

fun prefix_free_vars (prefix, fvL, i) =
let
   val fvL' = map (fn x => let
     val (x_name, x_ty) = dest_var x;
     val x'_name = prefix ^ "_"^x_name;
     in
        (mk_var (x'_name, x_ty))
     end) fvL
   val i' = subst (map (fn (x,x') => (x |-> x')) (zip fvL fvL')) i;
in
   (fvL', i')
end;

(*
   val t = ``l:'a list = []``;
   val v = ``l:'a list``;
   val fv = [];
   val sys = NONE;
   val thm = TypeBase.nchotomy_of ``:'a list``;
*)

fun QUANT_INSTANTIATE_HEURISTIC___EQUATION_two_cases thm sys v t =
let
   val _ = if is_eq t then () else raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;
   val (l,r) = dest_eq t;

   val (i,turn) = if (l = v) then (r,false) else
                  if (r = v) then (l,true) else
	          raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;

   val thm' = ISPEC v thm;
   val (eeq1,eeq2) = dest_disj (concl thm');
   val left_right_flag = if ((is_eq eeq1) andalso (lhs eeq1 = v) andalso (rhs eeq1 = i)) then false else
                         if ((is_eq eeq2) andalso (lhs eeq2 = v) andalso (rhs eeq2 = i)) then true else
                         Feedback.fail ();
   val (eeq1,eeq2,thm2) = if left_right_flag then
			     (eeq2, eeq1, CONV_RULE (PART_MATCH lhs DISJ_COMM) thm') else
                             (eeq1, eeq2, thm')

   val (fvL, eeq2b) = strip_exists eeq2;
   val (v',ni) = dest_eq eeq2b;
   val _ = if (v = v') then () else raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;

   val v_name = (fst o dest_var) v
   val (fvL', ni') = prefix_free_vars (v_name, fvL, ni);

   val thm3 = GEN v (CONV_RULE (RAND_CONV (INTRO_TUPLED_QUANT_CONV THENC
                                    RAND_CONV PABS_ELIM_CONV)) thm2)
   val g_thm0 = HO_MATCH_MP GUESS_RULES_TWO_CASES thm3
   val g_thm = if not turn then g_thm0 else
                 CONV_RULE (RAND_CONV (ABS_CONV SYM_CONV)) g_thm0

   val guess = guess_thm(gty_forall_gap, ni', fvL', g_thm);
in
  {rewrites     = [],
   general      = [],
   exists_point = [],
   forall_point = [],
   forall       = [],
   exists       = [],
   forall_gap   = [guess],
   exists_gap   = []}:guess_collection
end handle UNCHANGED => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp
         | HOL_ERR _ => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp



(*
val v = ``X:('a # 'b)``
val t = ``(P (X:('a # 'b))):bool``
val thm = TypeBase.nchotomy_of (type_of v)
val sys = dummy_sys
val thm = GEN v thm0
*)

fun QUANT_INSTANTIATE_HEURISTIC___one_case thm sys v t =
let
   val (vars, v_eq_i) = (strip_exists o snd o dest_forall o concl) thm;
   val (_,i) = dest_eq v_eq_i

   val v_name = (fst o dest_var) v
   val (vars', i') = prefix_free_vars (v_name, vars, i);

   val thm2 = CONV_RULE (QUANT_CONV ((INTRO_TUPLED_QUANT_CONV THENC
                         RAND_CONV PABS_ELIM_CONV))) thm

   val g_thm0 = ISPEC (mk_abs (v, t))
                (HO_MATCH_MP GUESS_RULES_ONE_CASE___FORALL_GAP thm2)
   val g_thm1 = ISPEC (mk_abs (v, t))
                (HO_MATCH_MP GUESS_RULES_ONE_CASE___EXISTS_GAP thm2)

   val g0 = guess_thm (gty_forall_gap, i',vars', g_thm0);
   val g1 = guess_thm (gty_exists_gap, i',vars', g_thm1);

in
  {rewrites     = [],
   general      = [],
   exists_point = [],
   forall_point = [],
   forall       = [],
   exists       = [],
   forall_gap   = [g0],
   exists_gap   = [g1]}:guess_collection
end handle HOL_ERR _ => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;


local
   fun QUANT_INSTANTIATE_HEURISTIC___FAIL sys v t =
       raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;

   fun dest_ex_eq tt =
     let
        val (vars, eq) = strip_exists tt;
        val (l, r) = dest_eq eq;
     in
        (vars, l, r)
     end;

   fun is_sing_case_thm thm =
     let
        val (v, b) = dest_forall (concl thm);
        val (_, l, _) = dest_ex_eq b;
        val _ = (if (aconv v l) then () else Feedback.fail())
     in
        true
     end handle HOL_ERR _ => false;

   fun is_double_case_thm thm =
     let
        val (v, b) = dest_forall (concl thm);
        val (b1, b2) = dest_disj b;
        val (_, l1, _) = dest_ex_eq b1;
        val (_, l2, _) = dest_ex_eq b2;
        val _ = (if (aconv v l1) then () else Feedback.fail())
        val _ = (if (aconv v l2) then () else Feedback.fail())
     in
        true
     end handle HOL_ERR _ => false;
in
   fun QUANT_INSTANTIATE_HEURISTIC___cases thm =
   let
   in
      if is_sing_case_thm thm then
         QUANT_INSTANTIATE_HEURISTIC___one_case thm
      else if is_double_case_thm thm then
         QUANT_INSTANTIATE_HEURISTIC___EQUATION_two_cases thm
      else
         QUANT_INSTANTIATE_HEURISTIC___FAIL
   end;


   fun QUANT_INSTANTIATE_HEURISTIC___cases_list thmL =
   let
      val thmL1 = filter is_sing_case_thm thmL
      val thmL2 = filter is_double_case_thm thmL

      val hL1 = map QUANT_INSTANTIATE_HEURISTIC___one_case thmL1;
      val hL2 = map QUANT_INSTANTIATE_HEURISTIC___EQUATION_two_cases thmL2;
   in
      (hL1, hL2)
   end
end;



fun QUANT_INSTANTIATE_HEURISTIC___TypeBase_cases sys v t =
if not (is_eq t) then raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp else
(let
   val thm = TypeBase.nchotomy_of (type_of v)
in
   QUANT_INSTANTIATE_HEURISTIC___cases thm sys v t
end handle HOL_ERR _ => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp);


(*********************************
 * Another Heuristic for dichotomies
 *********************************)
(*
   val t = ``n = x:num``;
   val t = ``x = n:num``;
   val v = ``x:num``;
   val fv = [``x_n``];
   val sys = NONE;
   val thmL = [GSYM prim_recTheory.SUC_ID]

   val t = ``[] = l:'a list``;
   val v = ``l:'a list``
   val thmL = [rich_listTheory.NOT_CONS_NIL]

   val t = ``0 = x``
*)
fun QUANT_INSTANTIATE_HEURISTIC___EQUATION_distinct thmL sys v t =
let
   val _ = if is_eq t then () else raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;
   val (l,r) = dest_eq t;

   val (i,turn) = if (l = v) then (r,false) else
                  if (r = v) then (l,true) else
	          raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;

   val thmL' = flatten (map BODY_CONJUNCTS thmL)
   val thmL'' = append thmL' (map GSYM thmL');

   val ni_thm = tryfind (fn thm => PART_MATCH (rhs o dest_neg) thm i) thmL'';
   val ni = (lhs o dest_neg o concl) ni_thm;


   val fvL_set = HOLset.difference (FVL [ni] empty_tmset, FVL [i] empty_tmset)
   val fvL_org = HOLset.listItems fvL_set
   val v_name = (fst o dest_var) v
   val (fvL, ni) = prefix_free_vars (v_name, fvL_org, ni);
   val fvL_org = if null fvL_org then [genvar unit_ty] else fvL_org;
   val ni_thm2 = GENL fvL_org  ni_thm
   val ni_thm3 = CONV_RULE (INTRO_TUPLED_QUANT_CONV THENC
                            RAND_CONV PABS_ELIM_CONV) ni_thm2


   val g_thm = let
        val (i_v, i_b) = dest_forall (concl ni_thm3);
        val i = mk_abs (i_v, lhs (dest_neg i_b))
        val (vl, vr) = (mk_abs(v,l), mk_abs(v,r));
        val g_thm0 = ISPECL [i, if turn then vr else vl, if turn then vl else vr] GUESS_RULES_EQUATION_FORALL_POINT
        val g_thm1 = BETA_RULE g_thm0
        val g_thm2 = HO_MATCH_MP g_thm1 ni_thm3;
        val g_thm3 = CONV_RULE (RAND_CONV
                        (ALPHA_CONV v THENC
                         (if (turn) then
                            (ABS_CONV SYM_CONV)
                         else ALL_CONV))) g_thm2
     in
        g_thm3
     end
   val guess = guess_thm (gty_forall_point, ni, fvL, g_thm);
in
  {rewrites     = [ni_thm],
   general      = [],
   exists_point = [],
   forall_point = [guess],
   forall       = [],
   exists       = [],
   forall_gap   = [],
   exists_gap = []}:guess_collection
end handle HOL_ERR _ => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;


fun QUANT_INSTANTIATE_HEURISTIC___EQUATION___TypeBase_distinct sys v t =
let
   val _ = if is_eq t then () else raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;
   val thm = TypeBase.distinct_of (type_of v);
in
   QUANT_INSTANTIATE_HEURISTIC___EQUATION_distinct [thm] sys v t
end handle HOL_ERR _ => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;





(*********************************
 * Inference Collection
 *********************************)

(* Some of the heuristics are able to use general theorems to generate guesses.
   These theorems should be of the form

   ``pre ==> GUESS_TYPE i P``

   For efficiency, it is convient to collect these inference theorems
   depending on the type of the conclusion. That is what an inference collection
   does.
*)

type inference_collection =
   {exists_point : thm list,
    forall_point : thm list,
    exists       : thm list,
    forall       : thm list,
    exists_gap   : thm list,
    forall_gap   : thm list};


val empty_inference_collection =
   {exists_point = [],
    forall_point = [],
    exists       = [],
    forall       = [],
    exists_gap   = [],
    forall_gap   = []}:inference_collection;


fun GUESS_THM_list2collection inference_thmL =
let
    val L0 = flatten (map BODY_CONJUNCTS inference_thmL)
    val L1 = map (SIMP_RULE std_ss [combinTheory.K_DEF]) L0;
    fun sort_fun (thm, (l1,l2,l3,l4,l5,l6)) =
    let
       val gtm = (fst o strip_comb o snd o dest_imp o concl) thm
    in
       if (same_const gtm GUESS_EXISTS_POINT_tm)then
          (thm::l1, l2, l3, l4, l5, l6) else
       if (same_const gtm GUESS_FORALL_POINT_tm) then
          (l1, thm::l2, l3, l4, l5, l6) else
       if (same_const gtm GUESS_EXISTS_tm) then
          (l1, l2, thm::l3, l4, l5, l6) else
       if (same_const gtm GUESS_FORALL_tm) then
          (l1, l2, l3, thm::l4, l5, l6) else
       if (same_const gtm GUESS_EXISTS_GAP_tm) then
          (l1, l2, l3, l4, thm::l5, l6) else
       if (same_const gtm GUESS_FORALL_GAP_tm) then
          (l1, l2, l3, l4, l5, thm::l6) else
          (l1, l2, l3, l4, l5, l6)
    end handle HOL_ERR _ => (l1,l2,l3,l4,l5,l6)

    val (l1,l2,l3,l4,l5,l6) = foldl sort_fun ([],[],[],[],[],[]) L1;
in
   {exists_point = l1,
    forall_point = l2,
    exists       = l3,
    forall       = l4,
    exists_gap   = l5,
    forall_gap   = l6 }:inference_collection
end;



(*********************************
 * Heuristics for Quantifiers
 *********************************)

(*
val t = ``!x. P x /\ (y = 2 + x) /\ Q y``
val t = ``?x. P x /\ (y = 2) /\ Q y``
val v = ``y:num``

val t = ``?y:'b. x:'a = f y``
val v = ``x:'a``
val sys = dummy_sys
val sys = heuristic
*)


local
   fun col (L1,L2,L3) =
      (GUESS_THM_list2collection [L1],
       GUESS_THM_list2collection [L2],
       GUESS_THM_list2collection [L3]);


   val f_icL     = col (GUESS_RULES_FORALL, GUESS_RULES_FORALL___NEW_FV, GUESS_RULES_FORALL___NEW_FV_1);
   val e_icL     = col (GUESS_RULES_EXISTS, GUESS_RULES_EXISTS___NEW_FV, GUESS_RULES_EXISTS___NEW_FV_1);
   val u_icL     = col (GUESS_RULES_EXISTS_UNIQUE, TRUTH, TRUTH);
in

fun QUANT_INSTANTIATE_HEURISTIC___QUANT sys (v:term) t =
let
   val ((ic, ic_fv, ic_fv_1), (v2, b)) =
       (f_icL, dest_forall t) handle HOL_ERR _ =>
       (e_icL, dest_exists t) handle HOL_ERR _ =>
       (u_icL, dest_exists1 t) handle HOL_ERR _ => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;

   val gc:guess_collection = sys v b

   fun apply_inference inf guess =
   let
       val (_, i, fvL, gthm0, was_thm) = guess_extract_thm guess;
       val gthm = GEN_ASSUM v2 gthm0;
       val new_fv = free_in v2 i
       val use_ic = if new_fv then (if null fvL then ic_fv_1 else ic_fv) else ic;
       val inf_thm = hd (inf use_ic) handle Empty => Feedback.fail();
       val xthm2 = HO_MATCH_MP inf_thm gthm
   in
       SOME (guess_thm_to_guess was_thm (SOME (i, if new_fv then v2::fvL else fvL)) xthm2)
   end handle HOL_ERR _ => NONE;

  val results = flatten (map (fn (s1, s2) => mapPartial (apply_inference s2) (s1 gc)) [
      (#exists_point, #exists_point),
      (#forall_point, #forall_point),
      (#exists, #exists),
      (#forall, #forall),
      (#exists_gap, #exists_gap),
      (#forall_gap, #forall_gap)])
in
   guess_list2collection ([], results)
end;

end


(******************************************************************************)
(* General heuristic for moving guesses over structure                        *)
(******************************************************************************)

fun process_simple_guess_thm thm =
let
    val (pre, ant) = dest_imp (concl thm);
    val (gty, i, v, t) = dest_guess_tm ant;

    val i_ok = is_var i orelse
               let
                  val (i_v, i_b) = dest_abs i
               in (type_of i_v = unit_ty) andalso (is_var i_b) end
    val _ = if (i_ok) then () else Feedback.fail();
    val (_, tL) = strip_comb t
    val tL_simple = all (fn tx => is_var tx orelse
               let val (tx_b, tx_v) = dest_comb tx
               in (tx_v = v) andalso (is_var tx_b) end) tL

    val preL = strip_conj pre
    fun check_internal pre_tm =
    let
       val (gty', i', v', t') = dest_guess_tm pre_tm;
       val _ = if (aconv i i') andalso (v = v') then () else Feedback.fail();
       val index_opt = SOME (index (fn t'' => aconv t' t'') tL) handle HOL_ERR _ => NONE;
    in
       (gty', index_opt)
    end;

    val pre_checkL = map check_internal preL;
    val thm' = CONV_RULE AND_IMP_ELIM_CONV thm

    val pre_checkL_opt = if not tL_simple then NONE else SOME (map (fn (ty, index_opt) => (ty, valOf index_opt)) pre_checkL) handle Option => NONE

in
    SOME (thm', pre_checkL_opt, mk_abs (v, t), i, gty)
end handle HOL_ERR _ => NONE;

fun process_simple_guess_thm_warn thm =
let
   val r_opt = process_simple_guess_thm thm;
   val _ = if isSome r_opt then () else
       say_HOL_WARNING "process_simple_guess_thm"
         ("Inference theorem not well formed:\n"^(thm_to_string thm))
in
   r_opt
end;


fun mk_guess_net guesses_thmL =
let
    fun fresh_vars thm =
        SIMP_RULE std_ss [combinTheory.K_DEF] (genvar_RULE thm)

    val thmL0 = flatten (map (BODY_CONJUNCTS o fresh_vars) guesses_thmL)
    val thmL1 = mapPartial process_simple_guess_thm_warn thmL0

    val (sL, cL) = partition (fn (_, opt, _, _, _) => isSome opt) thmL1

    (* make guess_net for complex theorems *)
    fun group_thmL L [] = L
      | group_thmL L ((thm, _, P_t, _, _)::thmPL) =
        let
           val ((P_t', thmL), L') = pluck (fn (P_t', thmL) => (P_t = P_t')) L handle HOL_ERR _ =>
                       ((P_t, []), L)
        in
           group_thmL ((P_t', thm::thmL)::L') thmPL
        end
    val guess_net_complex =
       foldr (fn ((P_t, thmL), n) => Ho_Net.enter ([],P_t, (P_t, thmL)) n) Ho_Net.empty_net
          (group_thmL [] cL)


    (* make guess_net for simple theorems *)
    fun free_var_process (thm, pre_checkL_opt, v_t, i, gty) =
    let
       val (v, t) = dest_abs v_t;
       val (b_op, tL) = strip_comb t;

       val pre_checkL = valOf pre_checkL_opt
       fun remove_free_var (n, tx) = is_comb tx andalso
           all (fn (ty, n') => (not (n = n')) orelse ((ty = gty_forall) orelse (ty = gty_exists)))
               pre_checkL

       val ntL = enumerate 0 tL;
       val remove_varsL = filter remove_free_var ntL;

       fun remove_vars_combins [] = [[]]
         | remove_vars_combins (x::xs) =
              let
                 val L = remove_vars_combins xs
              in
                 (map (fn z1 => x::z1) L) @ L
              end;
       val combs = remove_vars_combins remove_varsL

       fun apply_combs cL =
       let
           val pre_checkL' = filter (fn (_,n) => all (fn (n', _) => not (n = n')) cL) pre_checkL
           fun mk_tL (sub,tL') [] = (sub, rev tL')
             | mk_tL (sub,tL') ((n, tx)::ntL) =
           let
               val do_remove = exists (fn (n', _) => n = n') cL
               val (sub', tL'') = if not do_remove then (sub, tx::tL') else
                   let
                      val (tx_b, tx_v) = dest_comb tx;
                      val tx' = genvar (type_of tx);

                   in
                      ((tx_b |-> mk_abs(tx_v, tx'))::sub, tx'::tL')
                   end;
           in
              mk_tL (sub', tL'') ntL
           end;
           val (sub, tL') = mk_tL ([], []) ntL;
           val tL'' = map (fn tx => (true, fst (dest_comb tx)) handle HOL_ERR _ => (false, tx)) tL'
           val _ = if exists fst tL'' then () else Feedback.fail();

           val xthm0 = SIMP_RULE std_ss [GUESS_RULES_CONSTANT_FORALL, GUESS_RULES_CONSTANT_EXISTS, ETA_THM] (INST sub thm)

           val (i_f, i_v) = if is_abs i then (false, snd (dest_abs i)) else (true, i)

           val xthm1 = GENL (i_v::(map snd tL'')) xthm0
       in
           SOME (b_op, (i_f, map fst tL'', pre_checkL', gty, xthm1))
       end handle HOL_ERR _ => NONE;
    in
       mapPartial apply_combs combs
    end;
    fun group_simpleL L [] = L
      | group_simpleL L ((tm, x)::tmxs) =
        let
           val ((_, xL), L') = pluck (fn (tm', _) => (same_const tm tm')) L handle HOL_ERR _ =>
                       ((tm, []), L)
        in
           group_simpleL ((tm, x::xL)::L') tmxs
        end
    val guess_net_simple = group_simpleL [] (flatten (map free_var_process sL))
in
    (guess_net_complex, guess_net_simple)
end;



(*

val guesses_thmL = inference_thmL;
val guesses_net = mk_guess_net guesses_thmL
val heuristic = QUANT_INSTANTIATE_HEURISTIC___PURE_COMBINE empty_qp (SOME (ref (mk_quant_heuristic_cache())))
val heuristic = QUANT_INSTANTIATE_HEURISTIC___PURE_COMBINE empty_qp NONE
val heuristic = QUANT_INSTANTIATE_HEURISTIC___PURE_COMBINE std_qp NONE
val sys = heuristic;


val heuristic = QUANT_INSTANTIATE_HEURISTIC___PURE_COMBINE list_qp NONE
val sys = heuristic;

val sys = dummy_sys

val v = ``x:num``
val t = ``(x = 2) ==> P x``

sys v t


val v = ``x:'a list``
val t = ``Q ==> (~((x:'a list) = []) /\ P x)``

sys v t
GUESS_RULES_IMP

val t = ``(x + (y:num) = z) \/ Q y``

val t = ``!x. (x + (y:num) = z) \/ Q y``


val t = ``~(uf (x:'a) = uf y) \/ (P y /\ Q y)``
val v = ``x:'a``
val fv = [v]
val t = b


QUANT_INSTANTIATE_HEURISTIC___debug :=

val t = ``~(uf (x:'a) = uf (SND s)) \/ (IS_SOME (e (FST s)) /\
   s IN var_res_prop___PROP f (wpb,rpb) sfb)``

val heuristic = QUANT_INSTANTIATE_HEURISTIC___PURE_COMBINE empty_qp NONE
val sys = heuristic;
QUANT_INSTANTIATE_HEURISTIC___print_term_length := 2000
*)

fun strip_comb_abs t =
  let
     val (t1, t2) = dest_comb t;
     val (_, t3) = dest_abs t1;
  in
     strip_comb_abs t3
  end handle HOL_ERR _ => t;


fun dest_comb_abs fv fb =
  let
     val (t1, t2) = dest_comb fb;
     val _ = if (t2 = fv) then () else Feedback.fail();
     val t3 = strip_comb_abs t1
     val (fv', _) = dest_abs (t3);
  in
     fv'
  end

fun get_org_name fv fb =
   dest_comb_abs fv (find_term (can (dest_comb_abs fv)) fb) handle HOL_ERR _ => fv;



fun local_cache_sys sys =
  let
   val lc_ref = ref []
  in fn v => fn t =>
  let
    val gc_opt = assoc t (!lc_ref)
  in
    if (isSome gc_opt) then valOf gc_opt else raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp
  end handle HOL_ERR _ =>
  let
     val gc_opt = SOME (sys v t) handle QUANT_INSTANTIATE_HEURISTIC___no_guess_exp => NONE
                                      | HOL_ERR _ => NONE;
     val _ = lc_ref := (t,gc_opt)::(!lc_ref);
  in
     if (isSome gc_opt) then valOf gc_opt else raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp

  end
end;



local
   fun exists_forall_CONV t =
      HO_REWR_CONV GUESS_RULES_CONSTANT_FORALL t handle HOL_ERR _ =>
      HO_REWR_CONV GUESS_RULES_CONSTANT_EXISTS t

   fun guess_rule_elim_constant_RULE v xthm0 =
   let
      val (_, t') = dest_abs (rand (rhs (concl xthm0)));
   in
      if (free_in v t') then xthm0 else
         CONV_RULE (RHS_CONV exists_forall_CONV) xthm0
   end

   fun RRAND_CONV c t =
     if is_comb t then RAND_CONV (RRAND_CONV c) t else
     c t

   fun test_thmL v_t_type tvset v t (P_t, thmL) =
   let
       val ty_m = match_type (type_of P_t) v_t_type
       val P_t' = inst ty_m P_t;
       val (v'', t'') = dest_abs P_t';
       val t''' = subst [v'' |-> v] t'';
       val (term_sub, ty_sub) = ho_match_term [] tvset t''' t
       val _ = map (fn xx => if (free_in v (#residue xx)) then Feedback.fail() else ())
                    (term_sub)

       val P_t'' = subst term_sub (inst ty_sub P_t');
       val eq_thm0 = ((ALPHA_CONV v) THENC (DEPTH_CONV BETA_CONV)) P_t'';
       val eq_thm1_opt = SOME ((DEPTH_CONV BETA_CONV) (mk_abs (v, t))) handle UNCHANGED => NONE

       val eq_thm = if isSome eq_thm1_opt then
                      TRANS eq_thm0 (GSYM (valOf eq_thm1_opt)) else eq_thm0

       val ty_sub2 = ty_m @ ty_sub;
       fun process_thm thm0 =
       let
           val xthm0 = INST_TY_TERM (term_sub, ty_sub2) thm0;
           val xthm1 = CONV_RULE (RRAND_CONV (K eq_thm)) xthm0
       in
           SOME xthm1
       end handle HOL_ERR _ => NONE

       val thmL' = mapPartial process_thm thmL
   in
      thmL'
   end handle HOL_ERR _ => [];

(*   val (thm,gthm,rthm) = el 1 resL *)

   fun GUESS_MP thm gthm =
   let
      val i  = (rand o rator o fst o dest_imp o concl) thm;
      val gi = (rand o rator o concl) gthm;
   in
      if is_var i then
        let
           val i_ty =  (hd o snd o dest_type o type_of) i
           val gi_ty = (hd o snd o dest_type o type_of) gi
           val ty_sub = [i_ty |-> gi_ty];
           val i' = inst ty_sub i;

           val xthm0 = INST_TY_TERM ([i' |-> gi], ty_sub) thm
           val xthm1 = MP xthm0 gthm
        in
           xthm1
        end
      else if (is_var (snd (dest_abs i)) handle HOL_ERR _ => false) then
        let
           val (i_v, i_b) = dest_abs i;
           val (g_v, g_b) = dest_abs gi;
           val _ = if free_in g_v g_b then Feedback.fail() else ();

           val ty_sub = [type_of i_v |-> type_of g_v];

           val xthm0 = INST_TY_TERM ([i_b |-> g_b], ty_sub) thm
           val xthm1 = MP xthm0 gthm
        in
           xthm1
        end
     else MP thm gthm
   end;


   fun try_guess ifv_opt thm_ok thm guess =
   let
       val (ty, i, fvL, gthm, was_thm) = guess_extract_thm guess;
       val (ifv_opt, nthm) = if isSome ifv_opt then
            (ifv_opt, GUESS_MP thm gthm)
           else (SOME (i, fvL), GUESS_MP thm gthm)
   in
       SOME (ifv_opt, thm_ok andalso was_thm, nthm)
   end handle HOL_ERR _ => NONE;

   fun elim_precond sys v (ifv_opt,thm_ok,thm) =
   let
       val xthm0 = CONV_RULE (RATOR_CONV (
                    (RAND_CONV (RAND_CONV (ALPHA_CONV v) THENC DEPTH_CONV BETA_CONV)))) thm

       val precond = (fst o dest_imp) (concl xthm0)
       val (gty, _, v', t') = dest_guess_tm precond;
   in
       if (free_in v' t') then
       let
          val gc:guess_collection = sys v' t';
          val gL = (guess_collection_guess_type gty) gc;
       in
          mapPartial (try_guess ifv_opt thm_ok xthm0) gL
       end else
           [(ifv_opt, thm_ok, MP (CONV_RULE (RATOR_CONV (RAND_CONV exists_forall_CONV)) xthm0) TRUTH)]
   end handle QUANT_INSTANTIATE_HEURISTIC___no_guess_exp => []
            | HOL_ERR _ => [];

   fun elim_preconds sys v doneL [] = doneL
     | elim_preconds sys v doneL (ithm::thmL) =
       if (is_imp_only (concl (#3 ithm))) then
          elim_preconds sys v doneL (append (elim_precond sys v ithm) thmL)
       else
          if (isSome (#1 ithm)) then
             elim_preconds sys v (ithm::doneL) thmL
          else
             elim_preconds sys v doneL thmL

in

fun QUANT_INSTANTIATE_HEURISTIC___THM_GENERAL_COMPLEX guesses_net_complex sys v t =
let
   val v_t = mk_abs (v, t);
   val possible_thmL = Ho_Net.lookup v_t guesses_net_complex;
   val tvset = FVL [t] empty_tmset;
   val _ = if HOLset.member (tvset, v) then () else raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;

   val current_thmL = flatten (map (test_thmL (type_of v_t) tvset v t) possible_thmL);

   val sys' = local_cache_sys sys;
   val results = elim_preconds sys' v [] (map (fn y => (NONE, true, y)) current_thmL)
in
   guess_list2collection ([], (map (fn (ifv_opt, ok, thm) => guess_thm_to_guess ok ifv_opt thm) results))
end

end;



(*

val guesses_thmL = inference_thmL;
val (guesses_net_complex, guesses_net_simple) = mk_guess_net guesses_thmL

val (guesses_net_complex, guesses_net_simple) = mk_guess_net[]

val heuristic = QUANT_INSTANTIATE_HEURISTIC___PURE_COMBINE empty_qp (SOME (ref (mk_quant_heuristic_cache())))
val heuristic = QUANT_INSTANTIATE_HEURISTIC___PURE_COMBINE empty_qp NONE
val heuristic = QUANT_INSTANTIATE_HEURISTIC___PURE_COMBINE std_qp NONE
val sys = heuristic;


val sys = dummy_sys

val v = ``z:num``
val t = ``(z = 2) ==> P z``


val v = ``z:num``
val t = ``(z = 2)``

sys v t


val v = ``x:'a list``
val t = ``Q ==> (~((x:'a list) = []) /\ P x)``

sys v t
GUESS_RULES_IMP

val t = ``(x + (y:num) = z) \/ Q y``

val t = ``!x. (x + (y:num) = z) \/ Q y``


val t = ``~(uf (x:'a) = uf y) \/ (P y /\ Q y)``
val v = ``x:'a``
val fv = [v]
val t = b
val v = ``x:num``
val t = ``if b x then ((x = 2) /\ Q x) else (Q2 x /\ (x = 2))``

QUANT_INSTANTIATE_HEURISTIC___debug :=

val t = ``~(uf (x:'a) = uf (SND s)) \/ (IS_SOME (e (FST s)) /\
   s IN var_res_prop___PROP f (wpb,rpb) sfb)``

val heuristic = QUANT_INSTANTIATE_HEURISTIC___PURE_COMBINE empty_qp NONE []
val sys = heuristic;

sys v t
sys v b

t b

val t = ``Q2 2 /\ (x = 2)``
sys v t

QUANT_INSTANTIATE_HEURISTIC___print_term_length := 2000
*)

local
   fun fL_BETA_CONV [] = ALL_CONV
     | fL_BETA_CONV (true::fL) =
          RAND_CONV BETA_CONV THENC
          RATOR_CONV (fL_BETA_CONV fL)
     | fL_BETA_CONV (false::fL) =
          RATOR_CONV (fL_BETA_CONV fL)
in

fun QUANT_INSTANTIATE_HEURISTIC___THM_GENERAL_SIMPLE guesses_net_simple sys v t =
let
   val (b_op, tL) = strip_comb t;
   val (_, infL) = first (fn (tm, _) => same_const b_op tm) guesses_net_simple;

   val fL = map (free_in v) tL
   val infL' = filter (fn (_, fL', _, _, _) => fL = fL') infL
   val _ = if null infL' then raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp else ();

   val gcL = map (fn t => sys v t handle QUANT_INSTANTIATE_HEURISTIC___no_guess_exp => empty_guess_collection
                                       | HOL_ERR _ => empty_guess_collection) tL;

   fun try_inf (i_f, _, pre_checkL, gty, inf_thm) =
   let
      val (gty1, arg_n1) = hd pre_checkL;
      val pre_checkL_tl = tl pre_checkL;
      val gL = (guess_collection_guess_type gty1) (el (arg_n1+1) gcL);

      fun process_guess guess =
      (let
         val (i, fvL) = guess_extract guess;
         val _ = if not i_f andalso not (null fvL) then Feedback.fail() else ();

         val gL' = map (fn (gty, n) =>
               first (fn g => guess_extract g = (i, fvL)) ((guess_collection_guess_type gty) (el (n+1) gcL))) pre_checkL_tl;

         val final_gL = guess::gL';
         val do_proof = all guess_has_thm final_gL;
      in
      if (not do_proof) then SOME (mk_guess gty v t i fvL) else
      let
         val gthm1 = snd (guess2thm guess);
         val i_t = (rand o rator o concl) gthm1;
         val i_tv = if i_f then i_t else snd (dest_abs i_t);
         val t_vL = map (fn (fv, ttt) => if fv then mk_abs (v, ttt) else ttt) (zip fL tL)
         val inf_thm0 = ISPECL (i_tv::t_vL) inf_thm
         val inf_thm1 = LIST_MP (map (snd o guess2thm) final_gL) inf_thm0
         val inf_thm2 = CONV_RULE (RAND_CONV (ALPHA_CONV v THENC
                         ABS_CONV (fL_BETA_CONV (rev fL)))) inf_thm1
      in
         SOME (guess_thm (gty, i, fvL, inf_thm2))
      end end) handle HOL_ERR _ => NONE
   in
      mapPartial process_guess gL
   end;

   val gL2 = flatten (map try_inf infL')
in
   guess_list2collection ([], gL2)
end handle HOL_ERR _ => empty_guess_collection;

end;


(******************************************************************************)
(* Heuristics that apply conversions                                          *)
(******************************************************************************)

(* Applying a rewrite rule to a guess *)
(*
val tref = ref NONE

val (v,t,thmL,guess) = valOf (!tref)
val fvL = [``x:num``, ``y:num``]
val rewrite_thm = GSYM (HO_PART_MATCH lhs (hd thmL) ((fst o dest_imp) (concl thm_org)))
val fv = []

val v = ``x:num``
val t = ``!t. (P (x:num) /\ Z t):bool``
val t' = ``!t. X t \/ (Q (x:num))``
val i = ``(i (y:num) (z:num)):num``
val fvL = [``y:num``, ``z:num``]

val rew_thm = mk_thm ([], mk_eq(t,t'))

val guess = make_set_guess_thm_opt___dummy v t' (guess_forall (i,fvL,NONE));
correct_guess fv v t (guess_rewrite_thm_opt v t rew_thm guess)
*)

fun guess_rewrite rew_thm (guess_general (i, fvL)) = guess_general (i,fvL)
  | guess_rewrite rew_thm (guess_thm (gty, i, fvL, thm)) =
      guess_thm (gty, i, fvL,
         CONV_RULE (RAND_CONV (ABS_CONV (K (GSYM rew_thm)))) thm)
  | guess_rewrite rew_thm (guess_term (gty, i, fvL, tm)) =
      guess_term (gty, i, fvL,
         (rhs o concl) (RAND_CONV (ABS_CONV (K (GSYM rew_thm))) tm))


fun QUANT_INSTANTIATE_HEURISTIC___REWRITE sys (v:term) rew_thm =
let
   val (lt,rt) = dest_eq (concl rew_thm);
   val gc1:guess_collection = sys v rt

   val f = guess_rewrite rew_thm;
   val gc2 =
  {rewrites     = #rewrites gc1,
   general      = [],
   exists_point = map f (#exists_point gc1),
   forall_point = map f (#forall_point gc1),
   forall       = map f (#forall gc1),
   exists       = map f (#exists gc1),
   forall_gap   = map f (#forall_gap gc1),
   exists_gap   = map f (#exists_gap gc1)}:guess_collection
in
   gc2
end;


fun QUANT_INSTANTIATE_HEURISTIC___CONV conv sys v t =
let
   val thm_opt = SOME (QCHANGED_CONV (CHANGED_CONV conv) t) handle HOL_ERR _ =>  NONE
in
   if not (isSome thm_opt) then raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp else
   QUANT_INSTANTIATE_HEURISTIC___REWRITE sys v (valOf thm_opt)
end;


fun QUANT_INSTANTIATE_HEURISTIC___EQUATION___TypeBase_one_one sys v t =
let
   val (l,_) = dest_eq t;
   val thm = TOP_ONCE_REWRITE_CONV [TypeBase.one_one_of (type_of l)] t
in
   QUANT_INSTANTIATE_HEURISTIC___REWRITE sys v thm
end handle UNCHANGED => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp
         | HOL_ERR _ => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;



(******************************************************************************)
(* Heuristic tho rewrite the current term using an implication                *)
(******************************************************************************)

(* Applying a rewrite rule to a guess *)
(*
val v = ``x:num``
val ctx = []
val t  = ``(P (x:num)):bool``
val t2 = ``(x:num) = 2``
val thm = mk_thm ([], mk_imp(t, t2))
val thm2 = mk_thm ([], mk_imp(t2, t))
val thms = [thm, thm2]
val thms = [thm]
val ctx = thms
val heuristic = QUANT_INSTANTIATE_HEURISTIC___PURE_COMBINE empty_qp NONE []
val sys = heuristic;

*)

local
(*
   val inf_thm = GUESS_RULES_WEAKEN_FORALL_POINT
   val pre_thm = thm1
   val gL = (#forall_point gc)
   val ithm = inf_thm3
   val g = hd gL
*)
   fun process_guess ithm g =
   let
      val (gty, i, fvL, gthm, _) = guess_extract_thm g;
      val gthm' = MATCH_MP ithm gthm
   in
      guess_thm(gty, i, fvL, gthm')
   end;


   fun process_guess_list pre_thm v t t' inf_thm gL =
   let
      val vt = mk_abs(v, t)
      val vt' = mk_abs(v, t')
      val inf_thm1 = ISPECL [vt', vt] inf_thm
      val inf_thm2 = CONV_RULE ((RATOR_CONV o RAND_CONV o QUANT_CONV o BINOP_CONV) BETA_CONV) inf_thm1
      val inf_thm3 = MP inf_thm2 pre_thm
      val gL' = map (process_guess inf_thm3) gL
   in
      gL'
   end handle HOL_ERR _ => [];


   fun try_single_thm sys v t thm =
   let
      val _ = if (is_imp_only (concl thm)) then () else fail();
      val (thm0, strengthen) = (PART_MATCH (rand o rator) thm t, true) handle HOL_ERR _ =>
                               (PART_MATCH rand thm t, false);

      val pre_thm = GEN v thm0
      val t' = if strengthen then (rand (concl thm0)) else (rand (rator (concl thm0)))

      val gfun = process_guess_list pre_thm v t t'

      val gc1:guess_collection = sys v t' handle QUANT_INSTANTIATE_HEURISTIC___no_guess_exp => fail()


      val gc2 =  {rewrites     = #rewrites gc1,
                  general      = #general gc1,
                  exists_point =  gfun GUESS_RULES_STRENGTHEN_EXISTS_POINT (#exists_point gc1),
                  forall_point =  gfun GUESS_RULES_WEAKEN_FORALL_POINT (#forall_point gc1),
                  forall       = [],
                  exists       = [],
                  exists_gap =  gfun GUESS_RULES_WEAKEN_EXISTS_GAP (#exists_gap gc1),
                  forall_gap =  gfun GUESS_RULES_STRENGTHEN_FORALL_GAP (#forall_gap gc1)}:guess_collection
   in SOME gc2 end handle HOL_ERR _ => NONE
                        | UNCHANGED => NONE
in

fun QUANT_INSTANTIATE_HEURISTIC___STRENGTHEN_WEAKEN thms sys (v:term) t =
let
   val thmL = flatten (map BODY_CONJUNCTS thms);
   val gcL = mapfilter (try_single_thm sys v t) thmL
   val gc = guess_collection_flatten gcL
in
   gc
end handle HOL_ERR _ => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;

end


(******************************************************************************)
(* Heuristic that uses the precondition for direct matching                   *)
(******************************************************************************)

(*
val v = ``x:'a``

val t = ``(P (x:'a)):bool``
val thm = ASSUME t

val t = ``(P (x:'a)):bool``
val thm = ASSUME (mk_neg t)

val t = ``(P (x:'a)):bool``
val thm = ASSUME t
val t = mk_neg t

val thms = [thm];
QUANT_INSTANTIATE_HEURISTIC___GIVEN_INSTANTIATION thms () (v:term) t

   val v' = genvar (type_of v);
   val t' = subst [v |-> v'] t;


val thms = [thm]

val v = ``n:num``
val t = ``n < SUC m``
val thm = hd thms
val SOME (thms, v, t) = !xxx

*)

local
   fun get_implication_gc sys v t neg dneg i P thm = let
      val _ = if neg then () else fail();
      val ithm1 = ISPECL [P, i, v] IMP_NEG_CONTRA;

      val c0 = RATOR_CONV o RAND_CONV
      val (c2, c1) = (RAND_CONV BETA_CONV, BETA_CONV)
      val ithm2 = CONV_RULE (c0 c2) ithm1;
      val ithm3 = if dneg then CONV_RULE (c0 NEG_NEG_ELIM_CONV) ithm2 else ithm2
      val ithm4 = MP ithm3 thm
      val ithm5 = CONV_RULE (c0 c1) ithm4;
      val gc = QUANT_INSTANTIATE_HEURISTIC___STRENGTHEN_WEAKEN [ithm5] sys (v:term) t
                  handle QUANT_INSTANTIATE_HEURISTIC___no_guess_exp => empty_guess_collection;
   in gc end handle HOL_ERR _ => empty_guess_collection;


   fun get_direct_matches_gc neg dneg i P thm = let
      val gthm0 = if neg then GUESS_RULES_TRIVIAL_FORALL_POINT else GUESS_RULES_TRIVIAL_EXISTS_POINT
      val gthm1 = ISPECL [i, P] gthm0

      val c0 = if neg then (RAND_CONV BETA_CONV) else BETA_CONV
      val c1 = if dneg then c0 THENC NEG_NEG_ELIM_CONV else c0
      val gthm2 = CONV_RULE (RATOR_CONV (RAND_CONV c1)) gthm1
      val gthm = MP gthm2 thm;
      val gc = {rewrites     = [],
                general      = [],
                exists_point = if neg then [] else [guess_thm (gty_exists_point, i, [], gthm)],
                forall_point = if neg then [guess_thm (gty_forall_point, i, [], gthm)] else [],
                forall       = [],
                exists       = [],
                exists_gap   = [],
                forall_gap   = []}:guess_collection
   in gc end;

   fun try_single_thm sys vset v t v' t' thm =
   let
      val (vs, _) = strip_forall (concl thm);
      val vs' = map (fn v => genvar (type_of v)) vs
      val thm' = SPECL vs' thm

      val consts = HOLset.listItems (FVL [concl thm] vset)
      val (s, neg, dneg) = (Unify.simp_unify_terms consts t' (concl thm'), false, false) handle HOL_ERR _ =>
                           (Unify.simp_unify_terms consts (mk_neg t') (concl thm'), true, false) handle HOL_ERR _ =>
                           (Unify.simp_unify_terms consts t' (mk_neg (concl thm')), true, true) handle HOL_ERR _ =>
                     fail();
      val i = Unify.deref_tmenv s v';
      val P = mk_abs (v, t)
      val thm'' = INST s thm';
      val gc1 = get_direct_matches_gc neg dneg i P thm'';
      val gc2 = get_implication_gc sys v t neg dneg i P thm'';
   in SOME (guess_collection_append gc1 gc2) end handle HOL_ERR _ => NONE;
in

fun QUANT_INSTANTIATE_HEURISTIC___GIVEN_INSTANTIATION thms sys (v:term) t =
let
   val v' = genvar (type_of v);
   val t' = subst [v |-> v'] t;
   val thmL = flatten (map CONJUNCTS thms);
   val vset = HOLset.delete (FVL [t] empty_tmset, v) handle HOLset.NotFound =>
                raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;

   val gc = guess_collection_flatten (map (try_single_thm sys vset v t v' t') thmL)
in
   gc
end handle HOL_ERR _ => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;

end

(******************************************************************************)
(******************************************************************************)
(*                                                                            *)
(* Put everything together                                                    *)
(* Combine Heuristics / Caching etc                                           *)
(*                                                                            *)
(******************************************************************************)
(******************************************************************************)


(******************************************************************************)
(* Quantifier Heuristics Parameters                                           *)
(******************************************************************************)

(* One needs to collect all the heuristics, theorems etc used during guess search.
   The following datastructures achieves this. *)

type quant_param =
{distinct_thms      : thm list, (* Dichotomy theorems showing distinctiness *)
 cases_thms         : thm list, (* Dichotomy theorems showing case completeness *)
 rewrite_thms       : thm list, (* Theorems used for rewrites *)
 instantiation_thms : thm list, (* Theorems used for direct instantiations *)
 imp_thms           : thm list, (* Theorems used for weakening and strengthening *)
 context_thms       : thm list, (* additional context *)
 inference_thms     : thm list, (* Theorems used as inference rules to derive guesses from guesses for subterms. *)
 convs              : conv list, (* Conversions used *)
 filter             : (term -> term -> bool) list, (* Getting a free variable and a term, these ML functions decide, whether to try and find a guess *)
 top_heuristics     : quant_heuristic list, (* Heuristics that should only be applied at top level *)
 context_heuristics : (thm list -> quant_heuristic) list, (* Heuristics that may use the context of the given theorems *)
 heuristics         : quant_heuristic list, (* Heuristics that should be applied for all subterms *)
 final_rewrite_thms : thm list (* Rewrites used for cleaning up after instantiations. *) };


fun combine_qp
   ({distinct_thms      = l11,
     rewrite_thms       = l12,
     cases_thms         = l13,
     convs              = l14,
     heuristics         = l15,
     filter             = l19,
     top_heuristics     = l18,
     context_heuristics = l1A,
     imp_thms           = l1B,
     instantiation_thms = l1C,
     context_thms       = l1D,
     inference_thms     = l17,
     final_rewrite_thms = l16}:quant_param)
   ({distinct_thms      = l21,
     rewrite_thms       = l22,
     cases_thms         = l23,
     convs              = l24,
     heuristics         = l25,
     filter             = l29,
     top_heuristics     = l28,
     context_heuristics = l2A,
     imp_thms           = l2B,
     instantiation_thms = l2C,
     context_thms       = l2D,
     inference_thms     = l27,
     final_rewrite_thms = l26}:quant_param) =

   ({distinct_thms      = (append l11 l21),
     rewrite_thms       = (append l12 l22),
     cases_thms         = (append l13 l23),
     convs              = (append l14 l24),
     filter             = (append l19 l29),
     top_heuristics     = (append l18 l28),
     context_heuristics = (append l1A l2A),
     imp_thms           = (append l1B l2B),
     instantiation_thms = (append l1C l2C),
     context_thms       = (append l1D l2D),
     heuristics         = (append l15 l25),
     inference_thms     = (append l17 l27),
     final_rewrite_thms = (append l16 l26)}:quant_param)


val empty_qp =
   ({distinct_thms      = [],
     rewrite_thms       = [],
     cases_thms         = [],
     convs              = [],
     heuristics         = [],
     filter             = [],
     top_heuristics     = [],
     context_heuristics = [] ,
     imp_thms           = [],
     instantiation_thms = [],
     context_thms       = [],
     inference_thms     = [],
     final_rewrite_thms = []}:quant_param)

fun combine_qps L =
    foldl (fn (a1,a2) => combine_qp a1 a2) empty_qp L;


fun distinct_qp thmL =
   {distinct_thms=thmL,
    rewrite_thms=[],
    cases_thms=[],
    filter=[],
    top_heuristics=[],
    context_heuristics=[],
    inference_thms=[],
    imp_thms = [],
    instantiation_thms = [],
    context_thms = [],
    convs=[],heuristics=[],
    final_rewrite_thms=[]}:quant_param;


fun rewrite_qp thmL =
   {distinct_thms=[],
    rewrite_thms=thmL,
    cases_thms=[],
    filter=[],
    top_heuristics=[],
    context_heuristics=[],
    inference_thms=[],
    imp_thms = [],
    instantiation_thms = [],
    context_thms = [],
    convs=[],heuristics=[],
    final_rewrite_thms=[]}:quant_param;

fun fixed_context_qp thmL =
   {distinct_thms=[],
    rewrite_thms=[],
    cases_thms=[],
    filter=[],
    top_heuristics=[],
    context_heuristics=[],
    inference_thms=[],
    imp_thms = [],
    instantiation_thms = [],
    context_thms = thmL,
    convs=[],heuristics=[],
    final_rewrite_thms=[]}:quant_param;

fun imp_qp thmL =
   {distinct_thms=[],
    rewrite_thms=[],
    cases_thms=[],
    filter=[],
    top_heuristics=[],
    context_heuristics=[],
    inference_thms=[],
    imp_thms = thmL,
    instantiation_thms = [],
    context_thms = [],
    convs=[],heuristics=[],
    final_rewrite_thms=[]}:quant_param;

fun instantiation_qp thmL =
   {distinct_thms=[],
    rewrite_thms=[],
    cases_thms=[],
    filter=[],
    top_heuristics=[],
    context_heuristics=[],
    inference_thms=[],
    imp_thms = [],
    instantiation_thms = thmL,
    context_thms = [],
    convs=[],heuristics=[],
    final_rewrite_thms=[]}:quant_param;

fun final_rewrite_qp thmL =
   {distinct_thms=[],
    rewrite_thms=[],
    cases_thms=[],
    filter=[],
    top_heuristics=[],
    context_heuristics=[],
    inference_thms=[],
    imp_thms = [],
    instantiation_thms = [],
    context_thms = [],
    convs=[],heuristics=[],
    final_rewrite_thms=thmL}:quant_param;


fun cases_qp thmL =
   {distinct_thms=[],
    rewrite_thms=[],
    cases_thms=thmL,
    filter=[],
    top_heuristics=[],
    context_heuristics=[],
    inference_thms=[],
    convs=[],heuristics=[],
    imp_thms = [],
    instantiation_thms = [],
    context_thms = [],
    final_rewrite_thms=[]}:quant_param;

fun inference_qp thmL =
   {distinct_thms=[],
    rewrite_thms=[],
    cases_thms=[],
    filter=[],
    top_heuristics=[],
    context_heuristics=[],
    inference_thms=thmL,
    convs=[],heuristics=[],
    imp_thms = [],
    instantiation_thms = [],
    context_thms = [],
    final_rewrite_thms=[]}:quant_param;

fun convs_qp cL =
   {distinct_thms=[],
    rewrite_thms=[],
    cases_thms=[],
    filter=[],
    top_heuristics=[],
    context_heuristics=[],
    inference_thms=[],
    convs=cL,heuristics=[],
    imp_thms = [],
    instantiation_thms = [],
    context_thms = [],
    final_rewrite_thms=[]}:quant_param;

fun heuristics_qp hL =
   {distinct_thms=[],
    rewrite_thms=[],
    cases_thms=[],
    filter=[],
    top_heuristics=[],
    context_heuristics=[],
    inference_thms=[],
    convs=[],heuristics=hL,
    imp_thms = [],
    instantiation_thms = [],
    context_thms = [],
    final_rewrite_thms=[]}:quant_param;


fun top_heuristics_qp hL =
   {distinct_thms=[],
    rewrite_thms=[],
    cases_thms=[],
    filter=[],
    top_heuristics=hL,
    context_heuristics=[],
    inference_thms=[],
    convs=[],heuristics=[],
    imp_thms = [],
    instantiation_thms = [],
    context_thms = [],
    final_rewrite_thms=[]}:quant_param;

fun context_heuristics_qp chL =
   {distinct_thms=[],
    rewrite_thms=[],
    cases_thms=[],
    filter=[],
    top_heuristics=[],
    context_heuristics=chL,
    inference_thms=[],
    imp_thms = [],
    instantiation_thms = [],
    context_thms = [],
    convs=[],heuristics=[],
    final_rewrite_thms=[]}:quant_param;

fun filter_qp fL =
   {distinct_thms=[],
    rewrite_thms=[],
    cases_thms=[],
    filter=fL,
    top_heuristics=[],
    context_heuristics=[],
    inference_thms=[],
    imp_thms = [],
    instantiation_thms = [],
    context_thms = [],
    convs=[],heuristics=[],
    final_rewrite_thms=[]}:quant_param;



(******************************************************************************)
(* Combining multiple heuristics and other stuff into one big one that        *)
(* calls itself recursively, uses caches and provides debugging information   *)
(******************************************************************************)


(* Cache *)

(*
   val heuristicL = [QUANT_INSTANTIATE_HEURISTIC___EQUATION];
   val v = ``x:num``
   val t = ``x:num = 9``
*)

type quant_heuristic_cache =  (Term.term, (Term.term, guess_collection) Redblackmap.dict) Redblackmap.dict
fun mk_quant_heuristic_cache () = (Redblackmap.mkDict Term.compare):quant_heuristic_cache

(*
val cache = mk_quant_heuristic_cache ()
val t = T
val v = T
val fv = [T]
val gc = SOME empty_guess_collection
*)

fun quant_heuristic_cache___insert (cache:quant_heuristic_cache) (v:term) (t:term) (gc:guess_collection) =
let
   val t_cache_opt = Redblackmap.peek (cache,t)
   val t_cache = if isSome t_cache_opt then valOf t_cache_opt else
		 (Redblackmap.mkDict Term.compare);

   val t_cache' = Redblackmap.insert (t_cache, v, gc)
   val cache' = Redblackmap.insert (cache, t, t_cache')
in
   cache':quant_heuristic_cache
end;



fun quant_heuristic_cache___peek (cache:quant_heuristic_cache) (v:term) (t:term) =
let
   val t_cache = Redblackmap.find (cache,t)
   val gc = Redblackmap.find (t_cache,v);
in
   SOME gc
end handle Redblackmap.NotFound => NONE;




(* Auxiliary functions *)

fun cut_term_to_string t =
    let
       val n = !QUANT_INSTANTIATE_HEURISTIC___print_term_length;
       val st = term_to_string t;
       val st' = if (String.size st > n) then
		     (substring (st,0,n)^"...") else st
    in
       st'
    end;


fun COMBINE_HEURISTIC_FUNS L =
let
   val gcL = map (fn h =>
	    ((SOME (h ())
              handle QUANT_INSTANTIATE_HEURISTIC___no_guess_exp => NONE
	           | HOL_ERR _ => NONE
                   | UNCHANGED => NONE
            ))) L;
   val gc = guess_collection_flatten gcL;
in
   gc
end;

fun prefix_string 0 = ""
  | prefix_string n = "  "^(prefix_string (n-1));


(*

val heuristic = QUANT_INSTANTIATE_HEURISTIC___PURE_COMBINE empty_qp NONE
val sys = heuristic;


val heuristicL =
    [QUANT_INSTANTIATE_HEURISTIC___EQUATION,
     QUANT_INSTANTIATE_HEURISTIC___BOOL,
     QUANT_INSTANTIATE_HEURISTIC___THM_GENERAL
               (mk_guess_net inference_thmL)]

val t = ``(x = 7) \/ Q x``
val v = ``x:num``

sys v t
QUANT_INSTANTIATE_HEURISTIC___EQUATION sys v t
val t = ``!x y. P x y (z:'a)``
val v = ``z:'a``
val fv = [v]

val n = 0;
val cache_ref_opt = SOME (ref (mk_quant_heuristic_cache ()))
val heuristicL = hL
*)

(* The main function with an explicit recursion depth argument, and a list of already visited arguments. The arguments are:

   n              - recurion depth
   tL             - stack of terms for which instantiation is searched. Needed to detect cycles and abort.
   filterL        - a list of ML-functions that say which variable / term combinations to skip
   top_heuristicL - a list of heuristics that should just be tried at top-level but not used for recursive calls
   heuristicL     - the list of heuristics to combine
   ctx_heuristicL - context heuristics to combine. In contrast to heuristicL they get an extra context argument as input and their result is
      not cached, because it may depend on the context.
   cache_ref_opt  - a reference to a cache, if NONE is passed, a new cache is created internally
   ctx            - context theorems that might be used
   v              - the variable
   t              - the term
*)

fun BOUNDED_QUANT_INSTANTIATE_HEURISTIC___COMBINE n tL
    filterL top_heuristicL heuristicL ctx_heuristicL cache_ref_opt (ctx:thm list) (v:term) (t:term) =
if (n >= !QUANT_INSTANTIATE_HEURISTIC___max_rec_depth) then
   ((say_HOL_WARNING "BOUNDED_QUANT_INSTANTIATE_HEURISTIC___COMBINE" "Maximal recursion depth reached!");
   empty_guess_collection)
else let
   val _ = if exists (aconv t) tL then raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp else ();
   val _ = if (all (fn filter => (filter v t)) filterL) andalso (free_in v t) then () else raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;
   val cache_ref = if isSome cache_ref_opt then valOf cache_ref_opt else
                   (ref (mk_quant_heuristic_cache ()));
   val gc_opt = quant_heuristic_cache___peek (!cache_ref) v t
   val cache_found = isSome gc_opt;

   val _ = if (!QUANT_INSTANTIATE_HEURISTIC___debug > 0) then
	       say ((prefix_string n)^"searching guesses for ``"^
	           (term_to_string v)^"`` in ``"^(cut_term_to_string t)^"``\n")
           else ();

   val sys = BOUNDED_QUANT_INSTANTIATE_HEURISTIC___COMBINE (n+1) (t :: tL) filterL [] heuristicL ctx_heuristicL (SOME cache_ref) ctx;
   val gc = if (isSome gc_opt) then valOf gc_opt else
	    let
               val hL  = map (fn h => (fn () => (h sys v t))) (top_heuristicL @ heuristicL);
               val gc  = COMBINE_HEURISTIC_FUNS hL;
	       val _   = let
                 	    val c = quant_heuristic_cache___insert (!cache_ref) v t gc;
		            val _ = cache_ref := c
			 in
	 		      ()
  		         end;
	    in
	       gc
	    end;

   val gc_context = let
               val hLc = map (fn h => (fn () => (h ctx sys v t))) ctx_heuristicL;
               val gc  = COMBINE_HEURISTIC_FUNS (hLc);
	    in
	       gc
	    end;
   val gc  = correct_guess_collection v t (guess_collection_clean (guess_collection_append gc gc_context));


   val _ = if (!QUANT_INSTANTIATE_HEURISTIC___debug > 0) then
               let
                  val gL = (snd (guess_collection2list gc));
		  val prefix = prefix_string n;
                  val guesses_found_string = if null gL then "no" else Int.toString (length gL);
                  val _ = say (prefix^guesses_found_string^" guesses found for ``"^
	           (term_to_string v)^"`` in ``"^(cut_term_to_string t)^"``\n")

	          val show_thm = (!QUANT_INSTANTIATE_HEURISTIC___debug > 1);
                  fun say_guess guess = say (prefix^" - "^
	           (guess_to_string show_thm guess)^"\n")
		  val _ = foldl (fn (guess,_) => say_guess guess) () (snd (guess_collection2list gc))
               in
                  ()
               end
           else ()
   val _ = if (is_empty_guess_collection gc) then raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp else ();
in
   gc
end;



(* The finial top level function *)
val QUANT_INSTANTIATE_HEURISTIC___COMBINE =
    BOUNDED_QUANT_INSTANTIATE_HEURISTIC___COMBINE 0 [];




(******************************************************************
 * creating heuristics from a quantifier parameter
 ******************************************************************)

local
  val inference_thmL = [GUESS_RULES_DISJ, GUESS_RULES_CONJ,
                      GUESS_RULES_IMP, GUESS_RULES_EQUIV,
                      GUESS_RULES_COND, GUESS_RULES_NEG];
  val (guesses_net_complex, guesses_net_simple) = mk_guess_net inference_thmL;

  val BASIC_QUANT_INSTANTIATE_HEURISTICS =
    [QUANT_INSTANTIATE_HEURISTIC___EQUATION,
     QUANT_INSTANTIATE_HEURISTIC___BOOL,
     QUANT_INSTANTIATE_HEURISTIC___THM_GENERAL_SIMPLE guesses_net_simple,
     QUANT_INSTANTIATE_HEURISTIC___THM_GENERAL_COMPLEX guesses_net_complex,
     QUANT_INSTANTIATE_HEURISTIC___QUANT,
     QUANT_INSTANTIATE_HEURISTIC___CONV (markerLib.DEST_LABEL_CONV),
     QUANT_INSTANTIATE_HEURISTIC___CONV (asm_marker_ELIM_CONV)
   ]
in

  (* The most basic heuristics that should always be turned on *)
  val basic_qp = combine_qps [
        heuristics_qp BASIC_QUANT_INSTANTIATE_HEURISTICS,
        context_heuristics_qp[QUANT_INSTANTIATE_HEURISTIC___GIVEN_INSTANTIATION, QUANT_INSTANTIATE_HEURISTIC___STRENGTHEN_WEAKEN]]
end



fun qp_to_heuristic
    ({distinct_thms = distinct_thmL,
     cases_thms = cases_thmL,
     rewrite_thms = rewrite_thmL,
     inference_thms = inference_thmL2,
     convs = convL,
     filter = filterF,
     top_heuristics = top_heuristicL,
     context_heuristics=context_heuristicL,
     heuristics = heuristicL,
     imp_thms = imp_thmL,
     instantiation_thms = instantiation_thmL,
     context_thms = ctx_thmL,
     final_rewrite_thms = final_rewrite_thmL}:quant_param) =
    let
       val (hcL1, hcL2) = QUANT_INSTANTIATE_HEURISTIC___cases_list cases_thmL;
       val (guesses_net_complex, guesses_net_simple) = mk_guess_net inference_thmL2;

       val top_heuristicL = (hcL1 @ top_heuristicL);
       val heuristicL_1 = [QUANT_INSTANTIATE_HEURISTIC___EQUATION_distinct distinct_thmL,
                           QUANT_INSTANTIATE_HEURISTIC___THM_GENERAL_SIMPLE guesses_net_simple,
                           QUANT_INSTANTIATE_HEURISTIC___THM_GENERAL_COMPLEX guesses_net_complex,
                           QUANT_INSTANTIATE_HEURISTIC___STRENGTHEN_WEAKEN imp_thmL,
                           QUANT_INSTANTIATE_HEURISTIC___GIVEN_INSTANTIATION instantiation_thmL]
       val heuristicL_2 = map QUANT_INSTANTIATE_HEURISTIC___CONV ((TOP_ONCE_REWRITE_CONV rewrite_thmL)::convL)
       val heuristicL_final = flatten [heuristicL_1, heuristicL_2, hcL2, heuristicL]
    in
       fn cache_ref_opt => fn ctx =>
          (QUANT_INSTANTIATE_HEURISTIC___COMBINE filterF top_heuristicL heuristicL_final
        context_heuristicL cache_ref_opt (append ctx ctx_thmL))
    end;

(* very simple system callback for debugging *)
val debug_sys = qp_to_heuristic empty_qp NONE []

(******************************************************************
 * a stateful heuristic and quant_param
 ******************************************************************)

val quant_param_ref = ref empty_qp;
fun clear_stateful_qp () = (quant_param_ref := empty_qp);


fun stateful_qp___add_combine_arguments args =
   (quant_param_ref :=
     combine_qps ((!quant_param_ref)::args));


val TypeBase_qp = heuristics_qp [
       QUANT_INSTANTIATE_HEURISTIC___EQUATION___TypeBase_one_one,
       QUANT_INSTANTIATE_HEURISTIC___EQUATION___TypeBase_distinct,
       QUANT_INSTANTIATE_HEURISTIC___TypeBase_cases];


fun pure_stateful_qp () = (!quant_param_ref)

fun stateful_qp () = combine_qp TypeBase_qp (pure_stateful_qp ());

fun get_qp___for_types typeL =
       {distinct_thms = map TypeBase.distinct_of typeL,
        cases_thms = map TypeBase.nchotomy_of typeL,
        rewrite_thms = map TypeBase.one_one_of typeL,
        top_heuristics=[], context_heuristics=[], filter=[],
        final_rewrite_thms = [],
        inference_thms = [],
        imp_thms = [],
        instantiation_thms = [],
        context_thms = [],
        convs=[],heuristics=[]}:quant_param;



(******************************************************************
 * The main stuff
 ******************************************************************)

(*
val only_eq = false;
val try_eq = true;
val expand_eq = false;
val heuristic = QUANT_INSTANTIATE_HEURISTIC___PURE_COMBINE neg_heuL [];
val dir = CONSEQ_CONV_UNKNOWN_direction;
val t = ``!t:num. (t = 5) ==> X``
val t = ``!z t q. ((t = z2) ==> X z) /\ (z = 8 + t)``
*)


fun move_exists_to_end t =
let
   val thm1 = SWAP_EXISTS_CONV t;

   val (top_var, r_term) = dest_exists (rhs (concl thm1));
   val thm2 = move_exists_to_end r_term;
   val thm3 = EQ_EXISTS_INTRO (top_var, thm2);
in
   TRANS thm1 thm3
end handle HOL_ERR _ => REFL t;


(*
val BOOL_SIMP_CONV_cs = (computeLib.bool_compset());
val _ = computeLib.add_conv (boolSyntax.universal,1,QCONV QUANT_SIMP_CONV) BOOL_SIMP_CONV_cs;
val _ = computeLib.add_conv (boolSyntax.existential,1,QCONV QUANT_SIMP_CONV) BOOL_SIMP_CONV_cs;
val BOOL_SIMP_CONV = WEAK_CBV_CONV BOOL_SIMP_CONV_cs;
*)

fun BOOL_SIMP_CONV rwL (gc:guess_collection) =
let
   val conv = REWRITE_CONV (append rwL (#rewrites gc));
in
   fn t => conv t handle UNCHANGED => REFL t
end;


(*
val t = ``?x. (x = 2) /\ P x``;
val t = ``?x. (x = 2) \/ P x``;
val t = ``?x. (7 + z = x) /\ P x``;

val t = ``?x. !z. ~(~(7 = x) \/ P x z)``;
val t = ``?l. ~(l = [])``

val t = ``?x a b. P /\ (f x = f 2) /\ Q (f x)``
val t = ``?p1 p2. (p1 = 7) /\ Q p1 p2``
val t = ``?p1. (p1 = 7) /\ Q p1``
val t = ``?x:'a. (!y2:'b y:'b y3:'b. (x = f y y2 y3)) /\ P x``
val t = ``?x. ~(Q3 x \/ Q x \/ Q2 x \/ ~(x = 2))``

val only_eq = true;
val try_eq = true;
val expand_eq = false;
val heuristic = QUANT_INSTANTIATE_HEURISTIC___PURE_COMBINE empty_qp NONE
val sys = heuristic;
val dir = CONSEQ_CONV_UNKNOWN_direction
val min_var_occs = true;
val rwL = []

val t = mk_exists (v, t
val t = ``!x. x = []``

heuristic ``l:'a list`` ``l:'a list = []``
*)


fun QUANT_INSTANTIATE_HEURISTIC_STEP_CONSEQ_CONV (only_eq,try_eq,expand_eq) min_var_occs heuristic rwL (ctx:thm list) dir t =
if (not (is_exists t)) andalso (not (is_forall t)) andalso (not (is_exists1 t)) then raise UNCHANGED else
let
   val (v,b) = dest_abs (rand t);
in
  (if not (free_in v b) then
     ((if is_exists t then EXISTS_SIMP_CONV else
         if is_forall t then FORALL_SIMP_CONV else
            (HO_PART_MATCH lhs UEXISTS_SIMP)) t)
   else
   if is_exists t then
   let
      val (v,qb) = dest_exists t;
      val (qvL, b0) = strip_exists qb;

      val b_thm = if min_var_occs then
                      min_var_occur_CONV v b0 handle UNCHANGED => REFL b0
                  else REFL b0;
      val b = rhs (concl b_thm);

      val guessC = correct_guess_collection v b
		       (heuristic ctx v b)
                   handle QUANT_INSTANTIATE_HEURISTIC___no_guess_exp => raise UNCHANGED;

      val exists_pointL = #exists_point guessC;
      val existsL = append (#exists guessC)
                                  (map guess_weaken (#exists_gap guessC))

      val guess = first guess_has_thm exists_pointL handle HOL_ERR _ =>
                  first guess_has_thm_no_free_vars existsL handle HOL_ERR _ =>
                  first guess_has_thm existsL handle HOL_ERR _ =>
                  first (K true) exists_pointL handle HOL_ERR _ =>
                  first (K true) existsL handle HOL_ERR _ =>
                  first (K true) (#general guessC) handle HOL_ERR _ =>
                  raise UNCHANGED;

      val (i,fvL) = guess_extract guess;
      val proof_opt = guess2thm_opt guess;
      val need_eq = (only_eq orelse (dir = CONSEQ_CONV_WEAKEN_direction));
      val try_proof_eq = isSome proof_opt andalso try_eq andalso need_eq;

      val thm_opt = if not try_proof_eq then NONE else
          if (is_guess_thm gty_exists_point guess) then
             let
                val proof = valOf proof_opt;
                val xthm0 = MATCH_MP GUESS_EXISTS_POINT_THM proof
             in
                SOME xthm0
  	     end
          else (*exists*)
             let
                val proof = (valOf proof_opt);
                val i_t = rand (rator (concl proof))
                val xthm0 = ISPEC i_t GUESS_EXISTS_THM
                val new_part = (rhs o rand o snd o dest_forall o concl) xthm0
                val new_part_CONV1 = if null fvL then ALL_CONV else
                                     TRY_CONV (SPLIT_QUANT_CONV (pairSyntax.list_mk_pair fvL))
                val new_part_thm = (new_part_CONV1 THENC SIMP_CONV std_ss []) new_part;
                val xthm1 = CONV_RULE (QUANT_CONV (RAND_CONV (RHS_CONV (K new_part_thm)))) xthm0
                val xthm2 = MATCH_MP xthm1 proof
                val xthm3 = CONV_RULE (RHS_CONV (DEPTH_CONV BETA_CONV)) xthm2
             in
                SOME xthm3
             end;
      val thm = if isSome thm_opt then valOf thm_opt else
                if need_eq then
                   if not expand_eq then raise UNCHANGED else
		   let
                      val thm0 = HO_PART_MATCH lhs (ISPEC i quantHeuristicsTheory.UNWIND_EXISTS_THM) (mk_exists (v,b))

                      val thm1 = foldl (fn (fv,th) =>
                          let
                             val thm2 = AP_TERM (inst [alpha |-> type_of fv] boolSyntax.existential) (ABS fv th);
		             val thm3 = CONV_RULE (LHS_CONV QUANT_SIMP_CONV) thm2
    		             val thm4 = CONV_RULE (RHS_CONV (HO_PART_MATCH lhs quantHeuristicsTheory.MOVE_EXISTS_IMP_THM)) thm3
                          in
                             thm4
			  end) thm0 fvL;
                   in
                      thm1
                   end
                else
                   let
                      val vL = free_vars b;
                      val (fvL', sub) = list_variant vL fvL;
                      val i' = subst sub i;
                      val ib = subst [v |-> i'] b;
                      val ib_thm = ASSUME ib
                      val thm0 = EXISTS ((mk_exists (v,b)),i') ib_thm
                      val thm1 = foldr (fn (v,th) => SIMPLE_CHOOSE v th)
				 thm0 fvL';
                      val thm2 = DISCH_ALL thm1
                   in
                      thm2
                   end;

      val b_thm_conv = QUANT_CONV (REWR_CONV (GSYM b_thm))
      val thm2 = if is_eq (concl thm) then
                   CONV_RULE (LHS_CONV b_thm_conv) thm
                 else
                   CONV_RULE (RAND_CONV b_thm_conv) thm

      val thm3 = if (null qvL) then thm2 else
		 let
		    val EXISTS_INTRO_FUN =
                       if is_eq (concl thm2) then
                          EQ_EXISTS_INTRO else IMP_EXISTS_INTRO;
		    val thm3 = foldr EXISTS_INTRO_FUN thm2 qvL;
	            val ex_move_thm = move_exists_to_end t;
		 in
		    THEN_CONSEQ_CONV___combine ex_move_thm thm3 t
		 end;

      val thm4 = CONSEQ_CONV___APPLY_CONV_RULE thm3 t (BOOL_SIMP_CONV rwL guessC)
   in
      thm4
   end else if is_forall t then
   let
      val neg_t = let
          val (vL, body) = strip_forall t;
          val n_body = mk_neg body
          in
             list_mk_exists (vL, n_body) end

      val thm = QUANT_INSTANTIATE_HEURISTIC_STEP_CONSEQ_CONV (only_eq,try_eq,expand_eq) min_var_occs heuristic rwL ctx (CONSEQ_CONV_DIRECTION_NEGATE dir) (neg_t)

      val neg_t_thm = NOT_FORALL_LIST_CONV (mk_neg t)
      val new_conv = TRY_CONV NOT_EXISTS_LIST_CONV THENC (BOOL_SIMP_CONV rwL empty_guess_collection)

      val thm2 = if is_eq (concl thm) then
                    let
                       val thm3 = TRANS neg_t_thm thm;
		       val thm4 = AP_TERM boolSyntax.negation thm3;
                       val thm5 = CONV_RULE (LHS_CONV NEG_NEG_ELIM_CONV) thm4
		       val thm6 = CONV_RULE (RHS_CONV new_conv) thm5;
                    in
                       thm6
                    end
		 else if (rand (rator (concl thm))) = neg_t then
                    let
                       val thm3 = IMP_TRANS (fst (EQ_IMP_RULE neg_t_thm)) thm;
		       val thm4 = CONTRAPOS thm3;
                       val thm5 = CONV_RULE (RAND_CONV NEG_NEG_ELIM_CONV) thm4
		       val thm6 = CONV_RULE (RATOR_CONV (RAND_CONV new_conv)) thm5
                    in
                       thm6
                    end
                 else if (rand (concl thm)) = neg_t then
                    let
                       val thm3 = IMP_TRANS thm (snd (EQ_IMP_RULE neg_t_thm));
		       val thm4 = CONTRAPOS thm3;
                       val thm5 = CONV_RULE (RATOR_CONV (RAND_CONV NEG_NEG_ELIM_CONV)) thm4
		       val thm6 = CONV_RULE (RAND_CONV new_conv) thm5
                    in
                       thm6
                    end
                 else raise UNCHANGED;
   in
      thm2
   end else if is_exists1 t then
   let
      val (v,qb) = dest_exists1 t;

      val guessC = correct_guess_collection v qb
		       (heuristic ctx v qb);

      val guess = first guess_has_thm_no_free_vars (#exists_gap guessC) handle HOL_ERR _ =>
                  first guess_has_thm_no_free_vars (#exists_point guessC) handle HOL_ERR _ =>
                  first guess_has_thm_no_free_vars (#exists guessC) handle HOL_ERR _ =>
                  raise UNCHANGED;

      val (_, proof) = guess2thm guess
      val thm = if is_guess_thm gty_exists_gap guess then
                   HO_MATCH_MP GUESSES_UEXISTS_THM2 proof
                else if is_guess_thm gty_exists_point guess then
                   HO_MATCH_MP GUESSES_UEXISTS_THM3 proof
                else if is_guess_thm gty_exists guess then
                   HO_MATCH_MP GUESSES_UEXISTS_THM1 proof
                else Feedback.fail()
      val thm2 = CONV_RULE (RHS_CONV (BOOL_SIMP_CONV rwL guessC)) thm
   in
      thm2
   end else raise UNCHANGED)
     handle QUANT_INSTANTIATE_HEURISTIC___no_guess_exp =>
            raise UNCHANGED
end;



fun HEURISTIC_QUANT_INSTANTIATE_CONV re min_occs heuristic expand_eq rwL ctx =
    (if re then REDEPTH_CONV else DEPTH_CONV)
(CHANGED_CONV (QUANT_INSTANTIATE_HEURISTIC_STEP_CONSEQ_CONV (true,true,expand_eq) min_occs heuristic rwL ctx CONSEQ_CONV_UNKNOWN_direction)) THENC
REWRITE_CONV rwL;




(********************************************************)
(* Provide High level interfaces                        *)
(********************************************************)

(*****************************************************
 * One of the most basic conversions.
 *
 * It get's the following arguments:
 *
 * - cache_ref_opt
 *     a possible reference to a cache which stores
 *     previously found guesses. A new cache can be
 *     created using mk_quant_heuristic_cache
 *
 * - re : bool
 *     redescent into a term some intantiation has been found?
 *     similar to DEPTH_CONV and REDEPTH_CONV
 *
 * - min_occs
 *     should occurences of the variable be tried to be removed in
 *     a preprocessing step?
 *
 * - expand_eq : bool
 *     all build in heuristics provide proofs with all guesses
 *     if no proof is provided by user defined heuristics this
 *     argument can be set to true to do a case split instead
 *
 * - args
 *     a list of quant_params
 *****************************************************)

fun EXTENSIBLE_QUANT_INSTANTIATE_CONV cache_ref_opt re min_occs expand_eq ctx bqp args =
    let val arg = (combine_qps (bqp::args)) in
    HEURISTIC_QUANT_INSTANTIATE_CONV re min_occs (qp_to_heuristic arg cache_ref_opt) expand_eq (#final_rewrite_thms arg) ctx
    end

(*
val hL = QUANT_INSTANTIATE_HEURISTIC___PURE_COMBINE arg

(el 9 hL) dummy_sys v t

QUANT_INSTANTIATE_HEURISTIC___COMBINE hL NONE v t

(QUANT_INSTANTIATE_HEURISTIC___PURE_COMBINE arg NONE) v t

val (cache_ref_opt, re,   filter,   min_occs, expand_eq, args) =
    (NONE,          true, (K true), true,     false,     [pair_default_qp])
*)




(******************************************************************
 * A simpler interface, here just the quant_params list is needed
 ******************************************************************)
val QUANT_INSTANTIATE_CONV =
    EXTENSIBLE_QUANT_INSTANTIATE_CONV NONE true true false [] basic_qp

val NORE_QUANT_INSTANTIATE_CONV =
    EXTENSIBLE_QUANT_INSTANTIATE_CONV NONE false true false [] basic_qp

val FAST_QUANT_INSTANTIATE_CONV =
    EXTENSIBLE_QUANT_INSTANTIATE_CONV NONE false false false [] basic_qp

val EXPAND_QUANT_INSTANTIATE_CONV =
    EXTENSIBLE_QUANT_INSTANTIATE_CONV NONE true true true [] basic_qp

val NORE_EXPAND_QUANT_INSTANTIATE_CONV =
    EXTENSIBLE_QUANT_INSTANTIATE_CONV NONE false true true [] basic_qp

val FAST_EXPAND_QUANT_INSTANTIATE_CONV =
    EXTENSIBLE_QUANT_INSTANTIATE_CONV NONE false false true [] basic_qp


fun QUANT_INSTANTIATE_REDUCER cache_ref_opt re min_occs expand_eq bqp qpL =
  let exception FACTDB of thm list;
      fun get_db e = (raise e) handle FACTDB thms => thms
  in Traverse.REDUCER
    {name=SOME"QUANT_INSTANTIATE",
     initial =  FACTDB [],
     apply=(fn r => fn t =>
       let
         val thms = get_db (#context r);
         val res = EXTENSIBLE_QUANT_INSTANTIATE_CONV cache_ref_opt re min_occs expand_eq thms bqp qpL t;
       in
         res
       end handle UNCHANGED => fail()),
     addcontext=(fn (ctxt,thms) => (FACTDB (thms @ (get_db ctxt))))}
  end;

fun EXTENSIBLE_QUANT_INST_ss cache_ref_opt re min_occs expand_eq bqp qpL =
   simpLib.dproc_ss (QUANT_INSTANTIATE_REDUCER cache_ref_opt re min_occs expand_eq bqp qpL)

fun QUANT_INST_ss qpL        = EXTENSIBLE_QUANT_INST_ss NONE false true  false basic_qp qpL
fun EXPAND_QUANT_INST_ss qpL = EXTENSIBLE_QUANT_INST_ss NONE false true  true  basic_qp qpL
fun FAST_QUANT_INST_ss qpL   = EXTENSIBLE_QUANT_INST_ss NONE false false false basic_qp qpL

fun QUANT_INSTANTIATE_TAC L =  CONV_TAC (QUANT_INSTANTIATE_CONV L);
fun FAST_QUANT_INSTANTIATE_TAC L = CONV_TAC (FAST_QUANT_INSTANTIATE_CONV L);
fun ASM_QUANT_INSTANTIATE_TAC L =  DISCH_ASM_CONV_TAC (QUANT_INSTANTIATE_CONV L);
fun FAST_ASM_QUANT_INSTANTIATE_TAC L = DISCH_ASM_CONV_TAC (FAST_QUANT_INSTANTIATE_CONV L);


(******************************************************************
 * Interfaces for consequence conversions
 ******************************************************************)

fun HEURISTIC_QUANT_INSTANTIATE_CONSEQ_CONV re min_occs heuristic rwL dir =
THEN_CONSEQ_CONV
((if re then CONTEXT_REDEPTH_CONSEQ_CONV else CONTEXT_DEPTH_CONSEQ_CONV) CONSEQ_CONV_IMP_CONTEXT
   (QUANT_INSTANTIATE_HEURISTIC_STEP_CONSEQ_CONV (false,true,false) min_occs heuristic rwL) dir)
(REWRITE_CONV rwL);

fun EXTENSIBLE_QUANT_INSTANTIATE_CONSEQ_CONV cache_ref_opt re min_occs bqp args =
    let val arg = (combine_qps (bqp::args)) in
    HEURISTIC_QUANT_INSTANTIATE_CONSEQ_CONV re min_occs (qp_to_heuristic
       arg cache_ref_opt) (#final_rewrite_thms arg) end;

fun EXTENSIBLE_QUANT_INSTANTIATE_STEP_CONSEQ_CONV cache_ref_opt min_occs bqp args =
    let val arg = (combine_qps (bqp::args)) in
    (QUANT_INSTANTIATE_HEURISTIC_STEP_CONSEQ_CONV (false,true,false) min_occs
          (qp_to_heuristic arg cache_ref_opt)
            (#final_rewrite_thms arg) []) end;

val NORE_QUANT_INSTANTIATE_CONSEQ_CONV =
    EXTENSIBLE_QUANT_INSTANTIATE_CONSEQ_CONV NONE false false basic_qp

val QUANT_INSTANTIATE_CONSEQ_CONV =
    EXTENSIBLE_QUANT_INSTANTIATE_CONSEQ_CONV NONE true true basic_qp

val FAST_QUANT_INSTANTIATE_CONSEQ_CONV =
    EXTENSIBLE_QUANT_INSTANTIATE_CONSEQ_CONV NONE false false basic_qp

fun QUANT_INSTANTIATE_CONSEQ_TAC L =
    DISCH_ASM_CONSEQ_CONV_TAC (QUANT_INSTANTIATE_CONSEQ_CONV L);


(*********************************************************************
 * Oracle heuristic
 *
 * This heuristic produces unjustified guesses. If explicitly asked,
 * guesses are tried to be justified by METIS
 **********************************************************************)
fun QUANT_INSTANTIATE_HEURISTIC___ORACLE try_proof ml_callback sys v t =
let
  val res_opt = ml_callback v t;
  val (i, fvL) = if isSome res_opt then valOf res_opt else raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;
in
  if not try_proof then
  {rewrites     = [],
   general      = [guess_general (i,fvL)],
   exists_point = [],
   forall_point = [],
   forall       = [],
   exists       = [],
   forall_gap   = [],
   exists_gap   = []}
  else
  {rewrites     = [],
   general      = [],
   exists_point = [],
   forall_point = [],
   forall       = [make_guess___rewrite gty_forall v t i fvL] handle HOL_ERR _ => [],
   exists       = [make_guess___rewrite gty_exists v t i fvL] handle HOL_ERR _ => [],
   forall_gap   = [],
   exists_gap   = []}
end handle HOL_ERR _ => raise QUANT_INSTANTIATE_HEURISTIC___no_guess_exp;

fun oracle_qp ml_callback = top_heuristics_qp [
  QUANT_INSTANTIATE_HEURISTIC___ORACLE false ml_callback]

(*********************************************************************
 * Instantiate quantifiers by explicitly given guesses
 *
 * QUANT_INST_TAC / QUANT_INST_CONV are able to
 * instantiate quantifiers at subpositions.
 * They get a list of trible consisting of
 * (name_of_var, instantiation, list of free variables instantiation).
 * They then try to (partially) instantiate the named variables
 * with the given instantiations.
 **********************************************************************)

(*
val t = ``t = 0``
val v = ``x:num``
val ctxt = []
val try_proof = false;
val L = [("x", `0`, []), ("t", `xxx n`:term frag list, ["n"])]
val L = [("pdata'", `idata_h::pdata22`:term frag list, [`pdata22`]),
	   ("idata'", `idata_t`, [])]
*)


fun QUANT_INSTANTIATE_HEURISTIC___LIST_callback ctxt L v t =
let
   val (v_name, v_type) = dest_var v
   val (_,i_quot,free_vars_quot) = first (fn (p,_,_) => (p = v_name)) L;

   val i_quot' = QUOTE "(" :: (i_quot @ [QUOTE "):", ANTIQUOTE(ty_antiq v_type), QUOTE ""]);

   val ctxt = append (Term.free_vars t) ctxt;
   val i = Parse.parse_in_context ctxt i_quot';
   val ctxt = append (Term.free_vars i) ctxt;

   val fvL = map (fn s => Parse.parse_in_context ctxt s) free_vars_quot;
in
  SOME (i, fvL)
end;


fun QUANT_INSTANTIATE_HEURISTIC___LIST ctxt try_proof L v t =
    QUANT_INSTANTIATE_HEURISTIC___ORACLE try_proof (QUANT_INSTANTIATE_HEURISTIC___LIST_callback ctxt L) () v t

fun QUANT_TAC L (asm,t) =
  let
     val ctxt = HOLset.listItems (FVL (t::asm) empty_tmset);
  in
    REDEPTH_CONSEQ_CONV_TAC
      (QUANT_INSTANTIATE_HEURISTIC_STEP_CONSEQ_CONV (false,false,false)
         false (K (QUANT_INSTANTIATE_HEURISTIC___LIST ctxt false L)) [] [])
    (asm,t)
  end;


fun INST_QUANT_CONV L t =
  let
     val ctxt = HOLset.listItems (FVL [t] empty_tmset);
  in
    DEPTH_CONV
      (QUANT_INSTANTIATE_HEURISTIC_STEP_CONSEQ_CONV (true,true,false)
         false (K (QUANT_INSTANTIATE_HEURISTIC___LIST ctxt true L)) [] [] CONSEQ_CONV_UNKNOWN_direction)
    t
  end;

end
