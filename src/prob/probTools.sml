(* ========================================================================= *)
(* PROB UTILITY FUNCTIONS                                                    *)
(* Joe Hurd, 28 March 2000                                                   *)
(* ========================================================================= *)

structure probTools :> probTools =
struct

open HolKernel Parse Hol_pp boolLib;

infixr 0 THEN THENL ORELSE THENC;
infix 1 THEN1;

(* ------------------------------------------------------------------------- *)
(* Error handling.                                                           *)
(* ------------------------------------------------------------------------- *)

fun ERROR f s = HOL_ERR{origin_structure = "probUtil",
                        origin_function = f, message = s};
fun assert_false f s = raise ERROR f s;
fun assert b f s = if b then () else assert_false f s;

(* ------------------------------------------------------------------------- *)
(* Basic ML functions.                                                       *)
(* ------------------------------------------------------------------------- *)

fun grab (SOME x) = x | grab NONE = assert_false "grab" "NONE";
fun total f x = SOME (f x) handle Interrupt => raise Interrupt | _ => NONE;
fun curry f x y = f(x,y)
fun uncurry f (x,y) = f x y
infix 3 ##
fun (f ## g) (x,y) = (f x, g y)
fun I x = x;
fun D x = (x, x);
fun Df f = f ## f;
fun K x y = x;
fun N 0 _ x = x | N 1 f x = f x | N n f x = N (n - 1) f (f x);
fun index x = total (Lib.index (Lib.equal x));
fun cart al bl = foldl (fn (a,l) => foldl (fn (b,l') => (a,b)::l') l bl) [] al;
val map_partial = List.mapPartial;
fun cart_map_partial f (al, bl)
  = foldl (fn (a, res) => map_partial (curry f a) bl @ res) [] al;
fun assoc x [] = NONE
  | assoc x ((x', y')::xl) = if x = x' then SOME y' else assoc x xl;

(* --------------------------------------------------------------------- *)
(* Guaranteed new integers.                                              *)
(* --------------------------------------------------------------------- *)

local
  val counter = ref 0
in
  fun new_int ()
    = let val c = !counter
          val _ = counter := c + 1
      in c end
end;

(* --------------------------------------------------------------------- *)
(* Sort a list into order.                                               *)
(* --------------------------------------------------------------------- *)

local
  fun split res [] = res
    | split (al1, al2) (a::al) = split (a::al2, al1) al
  fun merge f ([], al') = al'
    | merge f (al, []) = al
    | merge f (a::al, a'::al')
      = if f (a, a') then a::(merge f (al, a'::al'))
	else a'::(merge f (a::al, al'))
in
  fun sort f l
    = if length l < 2 then l
      else (merge f o Df (sort f) o split ([], [])) l
end;

fun top_sort f [] = []
  | top_sort f l
    = let val m = (case List.find (fn x => List.all (fn y => f (x, y)) l) l
		   of SOME s => s
		   | NONE => assert_false "top_sort" "no minimal element")
	  val n = grab (index m l)
      in (List.nth (l, n))::(top_sort f (List.take (l, n)))
      end;

(* --------------------------------------------------------------------- *)
(* Randomly permute a list.                                              *)
(* --------------------------------------------------------------------- *)

fun permute [] [] = []
  | permute (i::is) l
  = let val rot_i = List.drop (l, i) @ List.take (l, i)
    in (case rot_i of h::t => h::(permute is t)
        | [] => assert_false "permute" "panic")
    end
  | permute _ _ = assert_false "permute" "bad arguments (different lengths?)";

local
  val rng = Random.newgen ()
  fun random_perm 0 = []
    | random_perm n
    = (Random.range (0, n) rng)::(random_perm (n - 1))
in
  fun permute_random l = permute (random_perm (length l)) l
end;

(* --------------------------------------------------------------------- *)
(* hol-specific functions.                                               *)
(* --------------------------------------------------------------------- *)

type term = Term.term
type sequent = term list * term
type tactic = Abbrev.tactic
type conv = Abbrev.conv

(* --------------------------------------------------------------------- *)
(* Redefinitions of standard hol functions.                              *)
(* --------------------------------------------------------------------- *)

fun is_imp t = is_comb t
  andalso (fn t' => is_comb t' andalso (fst (dest_comb t')) = ``$==>``)
    (fst (dest_comb t));

(* --------------------------------------------------------------------- *)
(* A profile function counting both time and primitive inferences.       *)
(* --------------------------------------------------------------------- *)

fun profile f a
  = let val m = Count.mk_meter ()
        val i = #prims(Count.read m)
        val t = Time.now ()
        val res = f a
        val t' = Time.now ()
        val i' = #prims(Count.read m)
        val _ = print ("Time taken: " ^ Time.toString (Time.-(t', t)) ^ ".\n"
          ^ "Primitive inferences: " ^ Int.toString (i' - i) ^ ".\n")
      in res
      end;

(* --------------------------------------------------------------------- *)
(* A folding operation on terms and types.                               *)
(* --------------------------------------------------------------------- *)

fun type_fold tv tt ty s
  = if is_vartype ty then tv (dest_vartype ty, s)
    else tt (((I ## map (type_fold tv tt)) o dest_type) ty, s);

fun term_fold tc tv ta tl t s
  = if is_const t then tc (dest_const t, s)
    else if is_var t then tv (dest_var t, s)
    else if is_comb t then
      ta ((Df (term_fold tc tv ta tl) o dest_comb) t, s)
    else if is_abs t then
      tl ((Df (term_fold tc tv ta tl) o dest_abs) t, s)
    else assert_false "term_fold_state" "weird term";

(* --------------------------------------------------------------------- *)
(* Parsing in the context of a goal, a la the Q library.                 *)
(* --------------------------------------------------------------------- *)

fun parse_with_goal t (al, g)
  = let val ctxt = free_varsl (g::al)
    in Parse.parse_in_context ctxt t
    end;

(* --------------------------------------------------------------------- *)
(* A conversional like DEPTH_CONV, but applies the argument conversion   *)
(* at most once to each subterm                                          *)
(* --------------------------------------------------------------------- *)

fun DEPTH_ONCE_CONV c tm
  = ((if is_abs tm then ABS_CONV (DEPTH_ONCE_CONV c)
      else if is_comb tm then
	RATOR_CONV (DEPTH_ONCE_CONV c) THENC RAND_CONV (DEPTH_ONCE_CONV c)
      else ALL_CONV)
     THENC (TRY_CONV c)) tm;

(*---------------------------------------------------------------------------
 * tac1 THEN1 tac2: A tactical like THEN that applies tac2 only to the
 *                  first subgoal of tac1
 *---------------------------------------------------------------------------*)

fun op THEN1 (tac1, tac2) g
  = let val (gl, jf) = tac1 g
    in (case gl of []
	  => assert_false "THEN1" "goal completely solved by first tactic"
	| (h::t)
	  => let val (h_gl, h_jf) = tac2 h
                 val h_gl_n = length h_gl
                 val h_jf' = fn thl => h_jf (List.take (thl, h_gl_n))
                 val join_l = fn thl => (h_jf' thl)::(List.drop (thl, h_gl_n))
             in (h_gl @ t, jf o join_l)
             end)
    end
    handle HOL_ERR{origin_structure,origin_function,message}
    => assert_false "THEN1" (origin_structure^"."^origin_function^": "^message);

(*---------------------------------------------------------------------------
 * REVERSE tac: A tactical that reverses the list of subgoals of tac.
 *              Intended for use with THEN1 to pick the `easy' subgoal, e.g.:
 *              - CONJ_TAC THEN1 SIMP_TAC
 *                  if the first conjunct is easily dispatched
 *              - REVERSE CONJ_TAC THEN1 SIMP_TAC
 *                  if it is the second conjunct that yields.
 *---------------------------------------------------------------------------*)

fun REVERSE tac g
  = let val (gl, jf) = tac g
    in (rev gl, jf o rev)
    end
    handle HOL_ERR{origin_structure,origin_function,message}
    => assert_false "REVERSE" (origin_structure^"."^origin_function^": "^message);

(* --------------------------------------------------------------------- *)
(* Assumption tactics.                                                   *)
(* --------------------------------------------------------------------- *)

fun UNDISCH_ALL_TAC ([], c) = ALL_TAC ([], c)
  | UNDISCH_ALL_TAC (a::al, c)
  = (UNDISCH_TAC a THEN UNDISCH_ALL_TAC) (a::al, c)

val KILL_ALL_TAC = POP_ASSUM_LIST (fn l => ALL_TAC)

(* --------------------------------------------------------------------- *)
(* Midpoint tactics.                                                     *)
(* --------------------------------------------------------------------- *)

fun SUFF_TAC t (al, c)
  = let val tm = parse_with_goal t (al, c)
    in ([(al, mk_imp (tm, c)), (al, tm)],
	fn [th1, th2] => MP th1 th2
	 | _ => assert_false "SUFF_TAC" "panic")
    end;

fun KNOW_TAC t = REVERSE (SUFF_TAC t THEN1 STRIP_TAC);

end; (* probTools *)
