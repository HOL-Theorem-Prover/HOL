(* ========================================================================= *)
(* HIGHER-ORDER UTILITY FUNCTIONS                                            *)
(* Joe Hurd, 10 June 2001                                                    *)
(* Updated by Chun Tian, 23 August 2018                                      *)
(* ========================================================================= *)

structure hurdUtils :> hurdUtils =
struct

open Susp HolKernel Parse Hol_pp boolLib metisLib bossLib BasicProvers;
open pairTheory res_quanTools pred_setTheory; (* for RESQ_STRIP_TAC *)

infixr 0 oo THENR ORELSER ## thenf orelsef;

(* obsoleted:
infix 1 >> |->;
val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
 *)

structure Parse = struct
  open Parse
  val (Type,Term) =
      pred_setTheory.pred_set_grammars
        |> apsnd ParseExtras.grammar_loose_equality
        |> parse_from_grammars
end
open Parse

(* ------------------------------------------------------------------------- *)
(* Basic ML datatypes/functions.                                             *)
(* ------------------------------------------------------------------------- *)

type 'a thunk = unit -> 'a;
type 'a susp = 'a Susp.susp
type ('a, 'b) maplet = {redex : 'a, residue : 'b}
type ('a, 'b) subst = ('a, 'b) Lib.subst

(* Error handling *)

exception BUG_EXN of
  {origin_structure : string, origin_function : string, message : string};

val ERR = mk_HOL_ERR "hurdUtils"

(* old definition:
fun ERR f s = HOL_ERR
  {origin_structure = "hurdUtils", origin_function = f, message = s};
 *)

fun BUG f s = BUG_EXN
  {origin_structure = "hurdUtils", origin_function = f, message = s};

fun BUG_to_string (BUG_EXN {origin_structure, origin_function, message}) =
  ("\nBUG discovered by " ^ origin_structure ^ " at " ^
   origin_function ^ ":\n" ^ message ^ "\n")
  | BUG_to_string _ = raise BUG "print_BUG" "not a BUG_EXN";

fun err_BUG s (h as HOL_ERR _) =
  (print (exn_to_string h); BUG s "should never fail")
  | err_BUG s _ =
  raise BUG "err_BUG" ("not a HOL_ERR (called from " ^ s ^ ")");

(* Success and failure *)

fun assert b e = if b then () else raise e;
fun try f a = f a
  handle (h as HOL_ERR _) => (print (exn_to_string h); raise h)
       | (b as BUG_EXN _) => (print (BUG_to_string b); raise b)
       | e => (print "\ntry: strange exception raised\n"; raise e);
fun total f x = SOME (f x) handle HOL_ERR _ => NONE;
fun can f = Option.isSome o total f;
fun partial (e as HOL_ERR _) f x = (case f x of SOME y => y | NONE => raise e)
  | partial _ _ _ = raise BUG "partial" "must take a HOL_ERR";

(* Exception combinators *)

fun nof x = raise ERR "nof" "never succeeds";
fun allf x = x;
fun op thenf (f, g) x = g (f x);
fun op orelsef (f, g) x = f x handle HOL_ERR _ => g x;
fun tryf f = f orelsef allf;
fun repeatf f x = ((f thenf repeatf f) orelsef allf) x;
fun repeatplusf f = f thenf repeatf f;
fun firstf [] _ = raise ERR "firstf" "out of combinators"
  | firstf (f :: rest) x = (f orelsef firstf rest) x;

(* Combinators *)

fun A f x = f x;
fun N 0 _ x = x | N 1 f x = f x | N n f x = N (n - 1) f (f x);
fun f oo g = fn x => f o (g x);

(* Pairs *)

infix 3 ##
fun (f ## g) (x, y) = (f x, g y);
fun D x = (x, x);
fun Df f = f ## f;
fun add_fst x y = (x, y);
fun add_snd x y = (y, x);
fun equal x y = (x = y);

fun pair_to_string fst_to_string snd_to_string (a, b) =
  "(" ^ fst_to_string a ^ ", " ^ snd_to_string b ^ ")";

(* Ints *)

val plus = curry op+;
val multiply = curry op*;
val succ = plus 1;

(* Strings *)

val concat = curry op^;
val int_to_string = Int.toString;
val string_to_int =
  partial (ERR "string_to_int" "couldn't convert string") Int.fromString;

fun mk_string_fn name args = name ^ String.concat (map (concat "_") args);
fun dest_string_fn name s =
  (case String.tokens (fn #"_" => true | _ => false) s of []
     => raise ERR "pure_dest_fn" "empty string"
   | f::args => (assert (f = name) (ERR "dest_fn" "wrong name"); args));
fun is_string_fn name = can (dest_string_fn name);

(* --------------------------------------------------------------------- *)
(* Tools for debugging.                                                  *)
(* --------------------------------------------------------------------- *)

(* Timing *)

local
  fun iterate f a 0 = ()
    | iterate f a n = (f a; iterate f a (n - 1))
in
  fun time_n n f a = time (iterate f a) n
end;

(* Test cases *)

fun tt f = (time o try) f;
fun tt2 f = tt o f;
fun tt3 f = tt2 o f;
fun tt4 f = tt3 o f;

fun ff f =
  try
  (fn x =>
   case (time o total o try) f x of NONE => ()
   | SOME _ => raise ERR "ff" "f should not have succeeded!");
fun ff2 f = ff o f;
fun ff3 f = ff2 o f;
fun ff4 f = ff3 o f;

(* --------------------------------------------------------------------- *)
(* Useful imperative features.                                           *)
(* --------------------------------------------------------------------- *)

(* Fresh integers *)

local
  val counter = ref 0
in
  fun new_int ()
    = let val c = !counter
          val _ = counter := c + 1
      in c end
end;

(* Random numbers *)

val random_generator = Random.newgen ();
fun random_integer n = Random.range (0, n) random_generator;
fun random_real () = Random.random random_generator;

(* Lazy operations *)

fun pair_susp a b = delay (fn () => (force a, force b));

fun susp_map f s = delay (fn () => f (force s));

(* --------------------------------------------------------------------- *)
(* Options.                                                              *)
(* --------------------------------------------------------------------- *)

val is_some = Option.isSome;
fun grab (SOME x) = x | grab NONE = raise ERR "grab" "NONE";
fun o_pair (SOME x, y) = SOME (x, y) | o_pair _ = NONE;
fun pair_o (x, SOME y) = SOME (x, y) | pair_o _ = NONE;
fun o_pair_o (SOME x, SOME y) = SOME (x, y) | o_pair_o _ = NONE;
val app_o = Option.map;
fun o_app f = curry (app_o (uncurry A) o o_pair) f
fun o_app_o f = curry (app_o (uncurry A) o o_pair_o) f
fun partial_app_o f = Option.join o app_o f;
fun partial_o_app f = Option.join o o_app f;
fun partial_o_app_o f = Option.join o o_app_o f;
fun option_to_list NONE = [] | option_to_list (SOME s) = [s];

(* --------------------------------------------------------------------- *)
(* Lists.                                                                *)
(* --------------------------------------------------------------------- *)

fun cons x = curry op:: x;
fun append l = curry op@ l;
fun wrap a = [a];
fun unwrap [a] = a | unwrap _ = raise ERR "unwrap" "not a singleton list";
fun fold _ b [] = b | fold f b (h::t) = f h (fold f b t);
fun trans _ s [] = s | trans f s (h::t) = trans f (f h s) t;
fun partial_trans _ s [] = SOME s
  | partial_trans f s (h::t) = partial_app_o (C (partial_trans f) t) (f h s);
fun first _ [] = raise ERR "first" "no items satisfy"
  | first f (h::t) = if f h then h else first f t;
fun partial_first _ [] = NONE
  | partial_first f (h::t) = (case f h of NONE => partial_first f t | s => s);
val forall = List.all;
val exists = List.exists;
val index = Lib.index;
fun nth n l = List.nth (l, n);
val split_after = Lib.split_after;
fun assoc x = snd o first (equal x o fst);
fun rev_assoc x = fst o first (equal x o snd);

val map = List.map;
val partial_map = List.mapPartial;

fun zip_aux _ [] [] = []
  | zip_aux f (x::xs) (y::ys) = f (x, y) (zip_aux f xs ys)
  | zip_aux _ _ _ = raise ERR "zip" "lists different lengths";
fun zip xs ys = zip_aux cons xs ys;
fun zipwith f xs ys = zip_aux (cons o (uncurry f)) xs ys;
fun partial_zipwith f xs ys = zip_aux
  (fn (x, y) => case f x y of NONE => I | SOME s => cons s) xs ys;

fun cart_aux f xs ys =
  let
    val xs' = rev xs
    val ys' = rev ys
  in
    trans (fn x => C (trans (fn y => f (x, y))) ys') [] xs'
  end;
fun cart xs ys = cart_aux cons xs ys;
fun cartwith f xs ys = cart_aux (cons o uncurry f) xs ys;
fun partial_cartwith f xs ys =
  cart_aux (fn (x, y) => case f x y of NONE => I | SOME s => cons s) xs ys;

fun list_to_string _ [] = "[]"
  | list_to_string elt_to_string (h :: t) =
  trans (fn x => fn y => y ^ ", " ^ elt_to_string x)
  ("[" ^ elt_to_string h) t ^ "]";

(* --------------------------------------------------------------------- *)
(* Lists as sets.                                                        *)
(* --------------------------------------------------------------------- *)

fun subset s t = forall (C mem t) s;

fun distinct [] = true
  | distinct (x :: rest) = not (mem x rest) andalso distinct rest;

fun union2 (a, b) (c, d) = (union a c, union b d);

(* --------------------------------------------------------------------- *)
(* Rotations, permutations and sorting.                                  *)
(* --------------------------------------------------------------------- *)

(* Rotations of a list---surprisingly useful *)

local
  fun rot res _ [] = res
    | rot res seen (h :: t) = rot ((h, t @ rev seen) :: res) (h :: seen) t
in
  fun rotations l = rev (rot [] [] l)
end;

fun rotate i = nth i o rotations;

fun rotate_random l = rotate (random_integer (length l)) l;

(* Permutations of a list *)

fun permutations [] = [[]]
  | permutations l =
  (flatten o map (fn (h, t) => map (cons h) (permutations t)) o rotations) l;

fun permute [] [] = []
  | permute (i :: is) (xs as _ :: _) = (op:: o (I ## permute is) o rotate i) xs
  | permute _ _ = raise ERR "permute" "bad arguments (different lengths)";

fun permute_random [] = []
  | permute_random l = (op:: o (I ## permute_random) o rotate_random) l;

(* Finding the minimal element of a list, wrt some order. *)

local
  fun min_acc _ best [] = best
    | min_acc f best (h :: t) = min_acc f (if f best h then best else h) t
in
  fun min _ [] = raise ERR "min" "empty list"
    | min f (h :: t) = min_acc f h t
end;

(* Merge (for the following merge-sort, but generally useful too). *)

fun merge f [] al' = al'
  | merge f al [] = al
  | merge f (a::al) (a'::al') =
  if f a a' then a::(merge f al (a'::al'))
  else a'::(merge f (a::al) al');

(* Order function here should be <= for a stable sort...              *)
(* ...and I think < gives a reverse stable sort (but don't quote me). *)
fun sort f l =
  let
    val n = length l
  in
    if n < 2 then l
    else (uncurry (merge f) o Df (sort f) o split_after (n div 2)) l
  end;

local
  fun find_min _ (_, []) = raise ERR "top_min" "no minimal element!"
    | find_min f (a, x::b) =
    (assert (f x x <> SOME false) (BUG "top_min" "order function says x > x!");
     if forall (fn y => f x y <> SOME false) (a @ b) then (x, a @ b)
     else find_min f (x::a, b))
in
  fun top_min f l = find_min f ([], l)
end;

fun top_sort f [] = []
  | top_sort f l =
  let
    val (x, rest) = top_min f l
  in
    x::top_sort f rest
  end;

(* --------------------------------------------------------------------- *)
(* Sums.                                                                 *)
(* --------------------------------------------------------------------- *)

datatype ('a, 'b) sum = LEFT of 'a | RIGHT of 'b;

(* --------------------------------------------------------------------- *)
(* Streams.                                                              *)
(* --------------------------------------------------------------------- *)

datatype ('a) stream = STREAM_NIL | STREAM_CONS of ('a * 'a stream thunk);

fun stream_null STREAM_NIL = true
  | stream_null (STREAM_CONS _) = false;

fun dest_stream_cons STREAM_NIL = raise ERR "dest_stream_cons" "stream is nil"
  | dest_stream_cons (STREAM_CONS c) = c;

fun stream_hd s = fst (dest_stream_cons s);
fun stream_tl s = snd (dest_stream_cons s);

local
  fun to_list res STREAM_NIL = res
    | to_list res (STREAM_CONS (a, thk)) = to_list (a :: res) (thk ())
in
  fun stream_to_list s = rev (to_list [] s)
end;

fun stream_append s1 s2 () =
  (case s1 () of STREAM_NIL => s2 ()
   | STREAM_CONS (a, thk) => STREAM_CONS (a, stream_append thk s2));

fun stream_concat ss = trans (C stream_append) (K STREAM_NIL) ss;

(* --------------------------------------------------------------------- *)
(* A generic tree type.                                                  *)
(* --------------------------------------------------------------------- *)

datatype ('a, 'b) tree = BRANCH of 'a * ('a, 'b) tree list | LEAF of 'b;

fun tree_size (LEAF _) = 1
  | tree_size (BRANCH (_, t)) = trans (plus o tree_size) 0 t;

fun tree_fold f_b f_l (LEAF l) = f_l l
  | tree_fold f_b f_l (BRANCH (p, s)) = f_b p (map (tree_fold f_b f_l) s);

fun tree_trans f_b f_l state (LEAF l) = [f_l l state]
  | tree_trans f_b f_l state (BRANCH (p, s)) =
  flatten (map (tree_trans f_b f_l (f_b p state)) s);

fun tree_partial_trans f_b f_l state (LEAF l) = option_to_list (f_l l state)
  | tree_partial_trans f_b f_l state (BRANCH (p, s)) =
  (case f_b p state of NONE => []
   | SOME state' => flatten (map (tree_partial_trans f_b f_l state') s));

(* --------------------------------------------------------------------- *)
(* Pretty-printing helper-functions.                                     *)
(* --------------------------------------------------------------------- *)

fun pp_map f pp_a x = pp_a (f x);

val pp_string = PP.add_string

fun pp_unknown _ = pp_string "_";

fun pp_int i = pp_string (int_to_string i);

open PP
fun pp_pair pp1 pp2 =
  fn (a, b) => block CONSISTENT 1 [
                add_string "(", pp1 a, add_string ",",
                add_break (1, 0), pp2 b, add_string ")"
              ]

fun pp_list pp =
    fn l => block INCONSISTENT 1 (
             add_string "[" ::
             pr_list pp [add_string ",", add_break(1,0)] l @
             [add_string "]"]
           )

(* --------------------------------------------------------------------- *)
(* Substitution operations.                                              *)
(* --------------------------------------------------------------------- *)

fun redex {redex, residue = _} = redex;
fun residue {redex = _, residue} = residue;
fun find_redex r = first (fn rr as {redex, residue} => r = redex);
fun tfind_redex r = first (fn rr as {redex, residue} => r ~~ redex);
fun clean_subst s = filter (fn {redex, residue} => redex <> residue) s;
fun clean_tsubst s = filter (fn {redex, residue} => redex !~ residue) s;
fun subst_vars sub = map redex sub;
fun maplet_map (redf, resf) {redex, residue} = (redf redex |-> resf residue);
fun subst_map fg = map (maplet_map fg);
fun redex_map f = subst_map (f, I);
fun residue_map f = subst_map (I, f);

fun tdistinct tml = HOLset.numItems(listset tml) = length tml

fun is_renaming_tsubst vars sub =
  let
    val residues = map residue sub
  in
    forall (C tmem vars) residues andalso tdistinct residues
  end;

fun is_renaming_subst vars sub =
  let
    val residues = map residue sub
  in
    forall (C mem vars) residues andalso distinct residues
  end;

fun invert_renaming_subst vars sub =
  let
    val _ =
      assert (is_renaming_subst vars sub)
      (ERR "invert_renaming_subst" "not a renaming subst, so not invertible")
    fun inv {redex, residue} = residue |-> redex
  in
    map inv sub
  end;

(* --------------------------------------------------------------------- *)
(* HOL-specific functions.                                               *)
(* --------------------------------------------------------------------- *)

type hol_type = Type.hol_type
type term = Term.term
type thm = Thm.thm
type goal = term list * term
type conv = term -> thm
type rule = thm -> thm
type validation = thm list -> thm
type tactic = goal -> goal list * validation
type thm_tactic = thm -> tactic
type vars = term list * hol_type list
type vterm = vars * term
type vthm = vars * thm
type type_subst = (hol_type, hol_type) subst
type term_subst = (term, term) subst
type substitution = (term, term) subst * (hol_type, hol_type) subst
type ho_substitution = substitution * thm thunk
type raw_substitution = (term_subst * term set) * (type_subst * hol_type list)
type ho_raw_substitution = raw_substitution * thm thunk

(* --------------------------------------------------------------------- *)
(* General                                                               *)
(* --------------------------------------------------------------------- *)

(* A profile function counting both time and primitive inferences. *)

fun profile f a =
  let
    val m = Count.mk_meter ()
    val i = #prims(Count.read m)
    val t = Time.now ()
    val res = f a
    val t' = Time.now ()
    val i' = #prims(Count.read m)
    val _ = print ("Time taken: " ^ Time.toString (Time.-(t', t)) ^ ".\n"
                   ^ "Primitive inferences: " ^ Int.toString (i' - i) ^ ".\n")
  in
    res
  end;

(* Parsing in the context of a goal, a la the Q library. *)

fun parse_with_goal t (asms, g) =
  let
    val ctxt = free_varsl (g::asms)
  in
    Parse.parse_in_context ctxt t
  end;

val PARSE_TAC = fn tac => fn q => W (tac o parse_with_goal q);

(* --------------------------------------------------------------------- *)
(* Term/type substitutions.                                              *)
(* --------------------------------------------------------------------- *)

val empty_subst = ([], []) : substitution;

val type_inst = type_subst;
val inst_ty = inst;
fun pinst (tm_sub, ty_sub) = subst tm_sub o inst_ty ty_sub;

fun type_subst_vars_in_set (sub : type_subst) vars =
  subset (subst_vars sub) vars;

fun subst_vars_in_set ((tm_sub, ty_sub) : substitution) (tm_vars, ty_vars) =
  type_subst_vars_in_set ty_sub ty_vars andalso
  HOLset.isSubset (listset (subst_vars tm_sub),
                   listset (map (inst_ty ty_sub) tm_vars));

(* Note: cyclic substitutions are right out! *)
fun type_refine_subst ty1 ty2 : (hol_type, hol_type) subst =
  ty2 @ (clean_subst o residue_map (type_inst ty2)) ty1;

fun refine_subst (tm1, ty1) (tm2, ty2) =
  (tm2 @ (clean_tsubst o subst_map (inst_ty ty2, pinst (tm2, ty2))) tm1,
   type_refine_subst ty1 ty2);

(*
refine_subst
([(``x:'b list`` |-> ``CONS (y:'b list) []``)],
 [(``:'a`` |-> ``:'b list``)])
([(``y:real list`` |-> ``[0:real]``)],
 [(``:'b`` |-> ``:real``)]);

refine_subst
([(``x:'b list`` |-> ``[y : 'b]``)],
 [(``:'a`` |-> ``:'b``)])
([(``y:'a`` |-> ``z:'a``)],
 [(``:'b`` |-> ``:'a``)]);
*)

fun type_vars_after_subst vars (sub : (hol_type, hol_type) subst) =
  subtract vars (subst_vars sub);

fun vars_after_subst (tm_vars, ty_vars) (tm_sub, ty_sub) =
  (op_set_diff aconv (map (inst_ty ty_sub) tm_vars) (subst_vars tm_sub),
   type_vars_after_subst ty_vars ty_sub);

fun type_invert_subst vars (sub : (hol_type, hol_type) subst) =
  invert_renaming_subst vars sub;

fun invert_subst (tm_vars, ty_vars) (tm_sub, ty_sub) =
  let
    val _ =
      assert (is_renaming_tsubst tm_vars tm_sub)
      (ERR "invert_subst" "not a renaming term subst")
    val ty_sub' = type_invert_subst ty_vars ty_sub
    fun inv {redex, residue} =
      inst_ty ty_sub' residue |-> inst_ty ty_sub' redex
  in
    (map inv tm_sub, ty_sub')
  end;

(* --------------------------------------------------------------------- *)
(* Logic variables.                                                      *)
(* --------------------------------------------------------------------- *)

val empty_vars = ([], []) : vars;
fun is_tyvar ((_, tyvars) : vars) ty = is_vartype ty andalso mem ty tyvars;
fun is_tmvar ((tmvars, _) : vars) tm = is_var tm andalso tmem tm tmvars;

fun type_new_vars (vars : hol_type list) =
  let
    val gvars = map (fn _ => gen_tyvar ()) vars
    val old_to_new = zipwith (curry op|->) vars gvars
    val new_to_old = zipwith (curry op|->) gvars vars
  in
    (gvars, (old_to_new, new_to_old))
  end;

fun term_new_vars vars =
  let
    val gvars = map (genvar o type_of) vars
    val old_to_new = zipwith (curry op|->) vars gvars
    val new_to_old = zipwith (curry op|->) gvars vars
  in
    (gvars, (old_to_new, new_to_old))
  end;

fun new_vars (tm_vars, ty_vars) =
  let
    val (ty_gvars, (ty_old_to_new, ty_new_to_old)) = type_new_vars ty_vars
    val (tm_gvars, (tm_old_to_new, tm_new_to_old)) = term_new_vars tm_vars
    val old_to_new = refine_subst (tm_old_to_new, []) ([], ty_old_to_new)
    val new_to_old = (tm_new_to_old, ty_new_to_old)
  in
    ((map (inst_ty ty_old_to_new) tm_gvars, ty_gvars), (old_to_new, new_to_old))
  end;

val vars_eq : vars eqf = pair_eq tml_eq equal
fun vars_union (tml1, tyl1) (tml2, tyl2) =
  (tunion tml1 tml2, union tyl1 tyl2)

(* ------------------------------------------------------------------------- *)
(* Bound variables.                                                          *)
(* ------------------------------------------------------------------------- *)

fun dest_bv bvs tm =
  let
    val _ = assert (is_var tm) (ERR "dest_bv" "not a var")
  in
    index (aconv tm) bvs
  end;
fun is_bv bvs = can (dest_bv bvs);
fun mk_bv bvs n : term = nth n bvs;

(* --------------------------------------------------------------------- *)
(* Types.                                                                *)
(* --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* Terms.                                                                *)
(* --------------------------------------------------------------------- *)

val type_vars_in_terms = trans (union o type_vars_in_term) [];

local
  fun dest (tm, args) =
    let
      val (a, b) = dest_comb tm
    in
      (a, b::args)
    end
in
  fun list_dest_comb tm = repeat dest (tm, [])
end;

fun conjuncts tm =
  if is_conj tm then
    let
      val (a, b) = dest_conj tm
    in
      a::(conjuncts b)
    end
  else [tm];

fun dest_unaryop c tm =
  let
    val (a, b) = dest_comb tm
    val _ = assert (fst (dest_const a) = c)
      (ERR "dest_unaryop" "different const")
  in
    b
  end;
fun is_unaryop c = can (dest_unaryop c);

fun dest_binop c tm =
  let
    val (a, b) = dest_comb tm
  in
    (dest_unaryop c a, b)
  end;
fun is_binop c = can (dest_binop c);

val dest_imp = dest_binop "==>";
val is_imp = can dest_imp;

local
  fun dest (vs, tm) = (C cons vs ## I) (dest_forall tm)
in
  val dest_foralls = repeat dest o add_fst []
end;
val mk_foralls = uncurry (C (trans (curry mk_forall)));

fun spec s tm =
  let
    val (v, body) = dest_forall tm
  in
    subst [v |-> s] body
  end;

val specl = C (trans spec);

fun var_match vars tm tm' =
  let
    val sub = match_term tm tm'
    val _ = assert (subst_vars_in_set sub vars)
      (ERR "var_match" "subst vars not contained in set")
  in
    sub
  end;

(* --------------------------------------------------------------------- *)
(* Thms.                                                                 *)
(* --------------------------------------------------------------------- *)

(* |- !f g. f = g <=> !x. f x = g x *)
val FUN_EQ = FUN_EQ_THM;

val SET_EQ = prove (“!s t :'a -> bool. (s = t) <=> (!x. x IN s <=> x IN t)”,
                    SIMP_TAC std_ss [IN_DEF, FUN_EQ_THM]);

val hyps = foldl (fn (h,t) => tunion (hyp h) t) [];

val LHS = lhs o concl;
val RHS = rhs o concl;

local
  fun fake_asm_op r th =
    let
      val h = rev (hyp th)
    in
      (N (length h) UNDISCH o r o C (foldl (uncurry DISCH)) h) th
    end
in
  val INST_TY = fake_asm_op o INST_TYPE;
  val PINST = fake_asm_op o INST_TY_TERM;
end;

(* --------------------------------------------------------------------- *)
(* Conversions.                                                          *)
(* --------------------------------------------------------------------- *)

(* Conversionals *)

fun FIRSTC [] tm = raise ERR "FIRSTC" "ran out of convs"
  | FIRSTC (c::cs) tm = (c ORELSEC FIRSTC cs) tm;

fun TRYC c = QCONV (c ORELSEC ALL_CONV);

fun REPEATPLUSC c = c THENC REPEATC c;

fun REPEATC_CUTOFF 0 _ _ = raise ERR "REPEATC_CUTOFF" "cut-off reached"
  | REPEATC_CUTOFF n c tm =
  (case (SOME (QCONV c tm) handle HOL_ERR _ => NONE) of NONE
     => QCONV ALL_CONV tm
   | SOME eq_th => TRANS eq_th (REPEATC_CUTOFF (n - 1) c (RHS eq_th)));

(* A conversional like DEPTH_CONV, but applies the argument conversion   *)
(* at most once to each subterm                                          *)

fun DEPTH_ONCE_CONV c tm = QCONV (SUB_CONV (DEPTH_ONCE_CONV c) THENC TRYC c) tm;

fun FORALLS_CONV c tm =
  QCONV (if is_forall tm then RAND_CONV (ABS_CONV (FORALLS_CONV c)) else c) tm;

fun CONJUNCT_CONV c tm =
  QCONV
  (if is_conj tm then RATOR_CONV (RAND_CONV c) THENC RAND_CONV (CONJUNCT_CONV c)
   else c) tm;

(* Conversions *)

fun EXACT_CONV exact tm = QCONV (if tm ~~ exact then ALL_CONV else NO_CONV) tm;

val NEGNEG_CONV = REWR_CONV (CONJUNCT1 NOT_CLAUSES);

val FUN_EQ_CONV = REWR_CONV FUN_EQ;
val SET_EQ_CONV = REWR_CONV SET_EQ;

fun N_BETA_CONV 0 = QCONV ALL_CONV
  | N_BETA_CONV n = RATOR_CONV (N_BETA_CONV (n - 1)) THENC TRYC BETA_CONV;

local
  val EQ_NEG_T = DECIDE ``!a. (~a = T) <=> (a = F)``
  val EQ_NEG_F = DECIDE ``!a. (~a = F) <=> (a = T)``
  val EQ_NEG_T_CONV = REWR_CONV EQ_NEG_T
  val EQ_NEG_F_CONV = REWR_CONV EQ_NEG_F
in
  val EQ_NEG_BOOL_CONV = QCONV (EQ_NEG_T_CONV ORELSEC EQ_NEG_F_CONV);
end;

val GENVAR_ALPHA_CONV = W (ALPHA_CONV o genvar o type_of o bvar);
val GENVAR_BVARS_CONV = DEPTH_ONCE_CONV GENVAR_ALPHA_CONV;

fun ETA_EXPAND_CONV v tm = SYM (ETA_CONV (mk_abs (v, mk_comb (tm, v))));
val GENVAR_ETA_EXPAND_CONV =
  W (ETA_EXPAND_CONV o genvar o fst o dom_rng o type_of);

(* --------------------------------------------------------------------- *)
(* Rules.                                                                *)
(* --------------------------------------------------------------------- *)

fun op THENR (r1, r2) (th:thm) :thm = r2 (r1 th:thm);
fun REPEATR r (th:thm) = REPEATR r (r th) handle HOL_ERR _ => th;
fun op ORELSER (r1, r2) (th:thm):thm = r1 th handle HOL_ERR _ => r2 th;
fun TRYR r = r ORELSER I;
val ALL_RULE : rule = I;

fun EVERYR [] = ALL_RULE
  | EVERYR (r::rest) = r THENR EVERYR rest;

val FORALL_IMP = HO_MATCH_MP MONO_EXISTS;

val EQ_BOOL_INTRO = EQT_INTRO THENR CONV_RULE (REPEATC EQ_NEG_BOOL_CONV);

val GENVAR_BVARS = CONV_RULE GENVAR_BVARS_CONV;

val GENVAR_SPEC =
  CONV_RULE (RAND_CONV GENVAR_ALPHA_CONV) THENR (snd o SPEC_VAR);

val GENVAR_SPEC_ALL = REPEATR GENVAR_SPEC;

local
  fun mk th [] = th
    | mk th (c :: rest) = mk (CONJ c th) rest
    handle HOL_ERR _ => raise BUG "REV_CONJUNCTS" "panic"
in
  fun REV_CONJUNCTS [] = raise ERR "REV_CONJUNCTS" "empty list"
    | REV_CONJUNCTS (th :: rest) = mk th rest
end;

fun REORDER_ASMS asms th0 =
  let
    val th1 = foldr (fn (h,t) => DISCH h t) th0 asms
    val th2 = funpow (length asms) UNDISCH th1
  in
    th2
  end;

local
  fun dest_c tm =
    if is_comb tm then
      let
        val (a, b) = dest_comb tm
      in
        (I ## cons b) (dest_c a)
      end
    else (tm, [])

  fun comb_beta eq_th x =
    CONV_RULE (RAND_CONV BETA_CONV) (MK_COMB (eq_th, REFL x))
in
  fun NEW_CONST_RULE cvar_lvars th =
    let
      val (cvar, lvars) = (I ## rev) (dest_c cvar_lvars)
      val sel_th =
        CONV_RULE (RATOR_CONV (REWR_CONV EXISTS_DEF) THENC BETA_CONV) th
      val pred = rator (concl sel_th)
      val def_tm = list_mk_abs (lvars, rand (concl sel_th))
      val def_th = ASSUME (mk_eq (cvar, def_tm))
      val eq_th = MK_COMB (REFL pred, trans (C comb_beta) def_th lvars)
    in
      CONV_RULE BETA_CONV (EQ_MP (SYM eq_th) sel_th)
    end
end;

val GENVAR_CONST_RULE =
  W (NEW_CONST_RULE o genvar o type_of o bvar o rand o concl);

local
  fun zap _ _ [] = raise ERR "zap" "fresh out of asms"
    | zap th checked (asm::rest) =
    if is_eq asm then
      let
        val (v, def) = dest_eq asm
      in
        if is_var v andalso all (not o free_in v) (checked @ rest) then
          MP (SPEC def (GEN v (DISCH asm th))) (REFL def)
        else zap th (asm::checked) rest
      end
    else zap th (asm::checked) rest
in
  val ZAP_CONSTS_RULE = repeat (fn th => zap th [concl th] (hyp th))
end;

(* ------------------------------------------------------------------------- *)
(* vthm operations                                                           *)
(* ------------------------------------------------------------------------- *)

fun thm_to_vthm th =
  let
    val tm = concl th

    val c_tyvars = type_vars_in_term tm
    val h_tyvars = type_vars_in_terms (hyp th)
    val f_tyvars = subtract c_tyvars h_tyvars
    val (f_tmvars, _) = dest_foralls tm
    val f_vars = (f_tmvars, f_tyvars)

    val (vars, (sub, _)) = new_vars f_vars
  in
    (vars, PINST sub (REPEATR (snd o SPEC_VAR) th))
  end;

fun vthm_to_thm (((vars, _), th) : vthm) = GENL vars th;

fun clean_vthm ((tm_vars, ty_vars), th) =
  let
    val tms = concl th :: hyp th
    val ty_vars' = intersect (type_vars_in_terms tms) ty_vars
    val tm_vars' = op_intersect aconv (free_varsl tms) tm_vars
  in
    ((tm_vars', ty_vars'), ZAP_CONSTS_RULE th)
  end;

fun var_GENVAR_SPEC ((tm_vars, ty_vars), th) : vthm =
  let
    val v = (genvar o type_of o fst o dest_forall o concl) th
  in
    ((v :: tm_vars, ty_vars), SPEC v th)
  end;

fun var_CONJUNCTS (vars, th) : vthm list =
  map (add_fst vars) (CONJUNCTS th);

fun var_MATCH_MP th : vthm -> vthm = (I ## MATCH_MP th);

(* --------------------------------------------------------------------- *)
(* Discharging assumptions on to the lhs of an implication:              *)
(* DISCH_CONJ a : [a] UNION A |- P ==> Q   |->   A |- a /\ P ==> Q       *)
(* UNDISCH_CONJ : A |- a /\ P ==> Q        |->   [a] UNION A |- P ==> Q  *)
(* --------------------------------------------------------------------- *)

val DISCH_CONJ_CONV = REWR_CONV AND_IMP_INTRO;
fun DISCH_CONJ a th = CONV_RULE DISCH_CONJ_CONV (DISCH a th);
fun DISCH_CONJUNCTS [] _ = raise ERR "DISCH_CONJ" "no assumptions!"
  | DISCH_CONJUNCTS (a::al) th = foldl (uncurry DISCH_CONJ) (DISCH a th) al;
fun DISCH_CONJUNCTS_ALL th = DISCH_CONJUNCTS (hyp th) th;
fun DISCH_CONJUNCTS_FILTER f th = DISCH_CONJUNCTS (filter f (hyp th)) th;
fun UNDISCH_CONJ_TAC a = UNDISCH_TAC a >> CONV_TAC DISCH_CONJ_CONV;
val UNDISCH_CONJUNCTS_TAC =
  POP_ASSUM MP_TAC >> REPEAT (POP_ASSUM MP_TAC >> CONV_TAC DISCH_CONJ_CONV);

val UNDISCH_CONJ_CONV = REWR_CONV (GSYM AND_IMP_INTRO)
val UNDISCH_CONJ = CONV_RULE UNDISCH_CONJ_CONV THENR UNDISCH
val UNDISCH_CONJUNCTS = REPEATR UNDISCH_CONJ THENR UNDISCH
val DISCH_CONJ_TAC = CONV_TAC UNDISCH_CONJ_CONV >> DISCH_TAC
val DISCH_CONJUNCTS_TAC = REPEAT DISCH_CONJ_TAC >> DISCH_TAC

(* --------------------------------------------------------------------- *)
(* Tacticals.                                                            *)
(* --------------------------------------------------------------------- *)

fun PURE_CONV_TAC conv :tactic = fn (asms,g) =>
   let
     val eq_th = QCONV conv g
   in
     ([(asms, RHS eq_th)], EQ_MP (SYM eq_th) o hd)
   end;

fun ASMLIST_CASES (t1:tactic) _ (g as ([], _)) = t1 g
  | ASMLIST_CASES _ t2 (g as (x::_, _)) = t2 x g;

fun POP_ASSUM_TAC tac =
  ASMLIST_CASES tac
  (K (UNDISCH_CONJUNCTS_TAC
      >> tac
      >> TRY (DISCH_THEN (EVERY o map ASSUME_TAC o CONJUNCTS))));

(* --------------------------------------------------------------------- *)
(* Tactics.                                                              *)
(* --------------------------------------------------------------------- *)

val TRUTH_TAC = ACCEPT_TAC TRUTH;

val S_TAC = rpt (POP_ASSUM MP_TAC) >> rpt RESQ_STRIP_TAC;
val Strip = S_TAC;

fun K_TAC _ = ALL_TAC;

val KILL_TAC = POP_ASSUM_LIST K_TAC;

val FUN_EQ_TAC = CONV_TAC (CHANGED_CONV (ONCE_DEPTH_CONV FUN_EQ_CONV));
val SET_EQ_TAC = CONV_TAC (CHANGED_CONV (ONCE_DEPTH_CONV SET_EQ_CONV));

val Rewr  = DISCH_THEN (REWRITE_TAC o wrap);
val Rewr' = DISCH_THEN (ONCE_REWRITE_TAC o wrap);
val POP_ORW = POP_ASSUM (ONCE_REWRITE_TAC o wrap);

(* --------------------------------------------------------------------- *)
(* STRONG_CONJ_TAC : tactic                                              *)
(*                                                                       *)
(* If the goal is (asms, A /\ B) then the tactic returns two subgoals of *)
(* the form (asms, A) and (asms, A ==> B)                                *)
(* --------------------------------------------------------------------- *)

local
  val th = DECIDE ``!a b. a /\ (a ==> b) ==> a /\ b``;
in
  val STRONG_CONJ_TAC :tactic = MATCH_MP_TAC th >> CONJ_TAC
end;

(* --------------------------------------------------------------------- *)
(* STRONG_DISJ_TAC : tactic                                              *)
(*                                                                       *)
(* If the goal is (asms, ~A \/ B) then the tactic returns a new goal of  *)
(* the form (asms UNION {A}, B). (It's "stronger" than DISJ2_TAC in that *)
(* A is not completely abandoned and thus still useful in proving B.)    *)
(*                                                                       *)
(* By using ONCE_REWRITE_TAC[DISJ_COMM] first, a similar stronger tactic *)
(* than DISJ1_TAC can be obtained.                                       *)
(*                                                                       *)
(* cf. LEFT_DISJ_TAC & RIGHT_DISJ_TAC (schneiderUtils)                   *)
(* --------------------------------------------------------------------- *)

val STRONG_DISJ_TAC :tactic =
    CONV_TAC (REWR_CONV (GSYM IMP_DISJ_THM)) >> STRIP_TAC;

(* --------------------------------------------------------------------- *)
(* FORWARD_TAC : (thm list -> thm list) -> tactic                        *)
(*                                                                       *)
(* Here is what happens when                                             *)
(*   FORWARD_TAC f                                                       *)
(* is applied to the goal                                                *)
(*   (asms, g).                                                          *)
(*                                                                       *)
(* 1. It calls the supplied inference function with the assumptions      *)
(*    to obtain a list of theorems.                                      *)
(*      ths = f (map ASSUME asms)                                        *)
(*    IMPORTANT: The assumptions of the theorems in ths must be either   *)
(*               in asms, or `definitions' of the form `new_var = body`. *)
(*                                                                       *)
(* 2. It returns one subgoal with the following form:                    *)
(*      (map concl ths, g)                                               *)
(*    i.e., the same goal, and a new assumption list that logically      *)
(*    follows from asms.                                                 *)
(*                                                                       *)
(* --------------------------------------------------------------------- *)

fun forward_just ths th0 =
  let
    val th1 = foldr (fn (h,t) => DISCH (concl h) t) th0 ths
    val th2 = foldl (fn (h,t) => MP t h) th1 ths
  in
    th2
  end

fun FORWARD_TAC f (asms, g:term) =
  let
    val ths = f (map ASSUME asms)
  in
    ([(map concl ths, g)],
       fn [th] => (REORDER_ASMS asms o ZAP_CONSTS_RULE o forward_just ths) th
        | _ => raise BUG "FORWARD_TAC" "justification function panic")
  end;

val Know = Q_TAC KNOW_TAC
val Suff = Q_TAC SUFF_TAC

(* --------------------------------------------------------------------- *)
(* A simple-minded CNF conversion.                                       *)
(* --------------------------------------------------------------------- *)

local
  open simpLib
in
  val EXPAND_COND_CONV =
    QCONV (SIMP_CONV (pureSimps.pure_ss ++ boolSimps.COND_elim_ss) [])
end

val EQ_IFF_CONV = QCONV (PURE_REWRITE_CONV [EQ_IMP_THM]);

val IMP_DISJ_CONV = QCONV (PURE_REWRITE_CONV [IMP_DISJ_THM]);

local
  val NEG_NEG = CONJUNCT1 NOT_CLAUSES
  val DE_MORGAN1
    = CONJUNCT1 (CONV_RULE (DEPTH_CONV FORALL_AND_CONV) DE_MORGAN_THM)
  val DE_MORGAN2
    = CONJUNCT2 (CONV_RULE (DEPTH_CONV FORALL_AND_CONV) DE_MORGAN_THM)
in
  val NNF_CONV = (QCONV o REPEATC o CHANGED_CONV)
    (REWRITE_CONV [NEG_NEG, DE_MORGAN1, DE_MORGAN2]
     THENC DEPTH_CONV (NOT_EXISTS_CONV ORELSEC NOT_FORALL_CONV))
end;

val EXISTS_OUT_CONV = (QCONV o REPEATC o CHANGED_CONV o DEPTH_CONV)
  (LEFT_AND_EXISTS_CONV
   ORELSEC RIGHT_AND_EXISTS_CONV
   ORELSEC LEFT_OR_EXISTS_CONV
   ORELSEC RIGHT_OR_EXISTS_CONV
   ORELSEC CHANGED_CONV SKOLEM_CONV);

val ANDS_OUT_CONV = (QCONV o REPEATC o CHANGED_CONV o DEPTH_CONV)
  (FORALL_AND_CONV
   ORELSEC REWR_CONV LEFT_OR_OVER_AND
   ORELSEC REWR_CONV RIGHT_OR_OVER_AND)

val FORALLS_OUT_CONV = (QCONV o REPEATC o CHANGED_CONV o DEPTH_CONV)
  (LEFT_OR_FORALL_CONV
   ORELSEC RIGHT_OR_FORALL_CONV);

val CNF_CONV =
 QCONV
 (DEPTH_CONV BETA_CONV
  THENC EXPAND_COND_CONV
  THENC EQ_IFF_CONV
  THENC IMP_DISJ_CONV
  THENC NNF_CONV
  THENC EXISTS_OUT_CONV
  THENC ANDS_OUT_CONV
  THENC FORALLS_OUT_CONV
  THENC REWRITE_CONV [GSYM DISJ_ASSOC, GSYM CONJ_ASSOC]);

val CNF_RULE = CONV_RULE CNF_CONV;

val CNF_EXPAND = CONJUNCTS o repeat GENVAR_CONST_RULE o CNF_RULE;

val CNF_TAC = CCONTR_TAC THEN FORWARD_TAC (flatten o map CNF_EXPAND);

(* --------------------------------------------------------------------- *)
(* ASM_MATCH_MP_TAC: adding MP-consequences to the assumption list.      *)
(* Does less than (EVERY (map ASSUME_TAC ths) >> RES_TAC).               *)
(* --------------------------------------------------------------------- *)

local
  val is_mp = is_imp o snd o dest_foralls o concl;

  fun initialize mp_th =
    let
      val (vars, (asm, body)) = ((rev ## dest_imp) o dest_foralls o concl) mp_th
      val asms = conjuncts asm
    in
      case asms of [a] => ([], [mp_th])
      | _ =>
      let
        val mp_th' = (SPEC_ALL THENR UNDISCH_CONJUNCTS) mp_th
        val rots = rotations asms
        fun f (asm, rest) =
          (DISCH_CONJUNCTS rest THENR DISCH asm THENR GENL vars) mp_th'
      in
        (map f rots, [])
      end
    end

  fun initialize_collect (m, s) th =
    let
      val (mx, sx) = initialize th
    in
      (mx @ m, sx @ s)
    end

  val initializel = trans (C initialize_collect)

  fun match1 (multi, single) th =
    let
      val do_match = partial_map (fn x => total (MATCH_MP x) th)
    in
      (do_match multi, do_match single)
    end

  fun add_thm th (concls, ths) =
    let
      val tm = concl th
    in
      if tmem tm concls then (concls, ths) else (tm :: concls, th :: ths)
    end

  fun clean_add_thms ths = snd o trans add_thm (map concl ths, ths)

  fun match 0 _ ths = ths
    | match n state ths =
    let
      val (m_res, s_res) = (Df flatten o unzip o map (match1 state)) ths
      val state' = initializel state m_res
      val s_res' = clean_add_thms ths s_res
    in
      match (n - 1) state' s_res'
    end;
in
  fun MATCH_MP_DEPTH n =
    match n o initializel ([], []) o filter is_mp
end;

fun ASM_MATCH_MP_TAC_N depth ths =
  POP_ASSUM_LIST
  (EVERY o map ASSUME_TAC o rev o MATCH_MP_DEPTH depth ths)

val ASM_MATCH_MP_TAC = ASM_MATCH_MP_TAC_N 10;

val art = ASM_REWRITE_TAC;

end; (* hurdUtils *)
