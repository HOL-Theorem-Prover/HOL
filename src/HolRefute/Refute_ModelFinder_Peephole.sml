(*  Title:      HolRefute/Refute_ModelFinder_Peephole.sml
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

Peephole optimizer for the HOL4 Refute model finder.

    Ported faithfully from Isabelle Nitpick's nitpick_peephole.ML.
*)

signature REFUTE_MODEL_FINDER_PEEPHOLE =
sig
  type n_ary_index = Refute_Forl.n_ary_index
  type formula = Refute_Forl.formula
  type int_expr = Refute_Forl.int_expr
  type rel_expr = Refute_Forl.rel_expr
  type decl = Refute_Forl.decl
  type expr_assign = Refute_Forl.expr_assign

  type name_pool =
    {rels: n_ary_index list,
     vars: n_ary_index list,
     formula_reg: int,
     rel_reg: int}

  val initial_pool : name_pool
  val not3_rel : n_ary_index
  val suc_rel : n_ary_index
  val suc_rels_base : int
  val unsigned_bit_word_sel_rel : n_ary_index
  val signed_bit_word_sel_rel : n_ary_index
  val nat_add_rel : n_ary_index
  val int_add_rel : n_ary_index
  val nat_subtract_rel : n_ary_index
  val int_subtract_rel : n_ary_index
  val nat_multiply_rel : n_ary_index
  val int_multiply_rel : n_ary_index
  val nat_divide_rel : n_ary_index
  val int_divide_rel : n_ary_index
  val nat_less_rel : n_ary_index
  val int_less_rel : n_ary_index
  val gcd_rel : n_ary_index
  val lcm_rel : n_ary_index
  val norm_frac_rel : n_ary_index
  val atom_for_bool : int -> bool -> rel_expr
  val formula_for_bool : bool -> formula
  val atom_for_nat : int * int -> int -> int
  val min_int_for_card : int -> int
  val max_int_for_card : int -> int
  val int_for_atom : int * int -> int -> int
  val atom_for_int : int * int -> int -> int
  val is_twos_complement_representable : int -> int -> bool
  val max_squeeze_card : int
  val suc_rel_for_atom_seq : (int * int) * bool -> n_ary_index
  val atom_seq_for_suc_rel : n_ary_index -> (int * int) * bool
  val inline_rel_expr : rel_expr -> bool
  val empty_n_ary_rel : int -> rel_expr
  val num_seq : int -> int -> int_expr list
  val s_and : formula -> formula -> formula

  type kodkod_constrs =
    {kk_all: decl list -> formula -> formula,
     kk_exist: decl list -> formula -> formula,
     kk_formula_let: expr_assign list -> formula -> formula,
     kk_formula_if: formula -> formula -> formula -> formula,
     kk_or: formula -> formula -> formula,
     kk_not: formula -> formula,
     kk_iff: formula -> formula -> formula,
     kk_implies: formula -> formula -> formula,
     kk_and: formula -> formula -> formula,
     kk_subset: rel_expr -> rel_expr -> formula,
     kk_rel_eq: rel_expr -> rel_expr -> formula,
     kk_no: rel_expr -> formula,
     kk_lone: rel_expr -> formula,
     kk_one: rel_expr -> formula,
     kk_some: rel_expr -> formula,
     kk_rel_let: expr_assign list -> rel_expr -> rel_expr,
     kk_rel_if: formula -> rel_expr -> rel_expr -> rel_expr,
     kk_union: rel_expr -> rel_expr -> rel_expr,
     kk_difference: rel_expr -> rel_expr -> rel_expr,
     kk_override: rel_expr -> rel_expr -> rel_expr,
     kk_intersect: rel_expr -> rel_expr -> rel_expr,
     kk_product: rel_expr -> rel_expr -> rel_expr,
     kk_join: rel_expr -> rel_expr -> rel_expr,
     kk_closure: rel_expr -> rel_expr,
     kk_reflexive_closure: rel_expr -> rel_expr,
     kk_comprehension: decl list -> formula -> rel_expr,
     kk_project: rel_expr -> int_expr list -> rel_expr,
     kk_project_seq: rel_expr -> int -> int -> rel_expr,
     kk_not3: rel_expr -> rel_expr,
     kk_nat_less: rel_expr -> rel_expr -> rel_expr,
     kk_int_less: rel_expr -> rel_expr -> rel_expr}

  val kodkod_constrs : bool -> int -> int -> int -> kodkod_constrs
end;

structure Refute_ModelFinder_Peephole
  :> REFUTE_MODEL_FINDER_PEEPHOLE =
struct

open Refute_Forl
open Refute_ModelFinder_Util

type name_pool =
  {rels: n_ary_index list,
   vars: n_ary_index list,
   formula_reg: int,
   rel_reg: int}

val initial_pool = {rels = [], vars = [], formula_reg = 10, rel_reg = 10}

val not3_rel = (2, ~1)
val unsigned_bit_word_sel_rel = (2, ~2)
val signed_bit_word_sel_rel = (2, ~3)
val suc_rel = (2, ~4)
val suc_rels_base = ~5 (* must be the last of the binary series *)
val nat_add_rel = (3, ~1)
val int_add_rel = (3, ~2)
val nat_subtract_rel = (3, ~3)
val int_subtract_rel = (3, ~4)
val nat_multiply_rel = (3, ~5)
val int_multiply_rel = (3, ~6)
val nat_divide_rel = (3, ~7)
val int_divide_rel = (3, ~8)
val nat_less_rel = (3, ~9)
val int_less_rel = (3, ~10)
val gcd_rel = (3, ~11)
val lcm_rel = (3, ~12)
val norm_frac_rel = (4, ~1)

fun atom_for_bool j0 b = Atom (j0 + int_from_bool b)
fun formula_for_bool b = if b then True else False

fun atom_for_nat (k, j0) n = if n < 0 orelse n >= k then ~1 else n + j0

fun min_int_for_card k = ~k div 2 + 1
fun max_int_for_card k = k div 2

fun int_for_atom (k, j0) j =
  let val j = j - j0 in if j <= max_int_for_card k then j else j - k end

fun atom_for_int (k, j0) n =
  if n < min_int_for_card k orelse n > max_int_for_card k then ~1
  else if n < 0 then n + k + j0
  else n + j0

(* M4-only bits-mode helper reservation. *)
fun is_twos_complement_representable bits n =
  let val max = reasonable_power 2 bits in n >= ~max andalso n < max end

val max_squeeze_card = 49

fun squeeze (m, n) =
  if n > max_squeeze_card then
    raise TOO_LARGE ("Refute_ModelFinder_Peephole.squeeze",
                     "too large cardinality (" ^ Int.toString n ^ ")")
  else
    (max_squeeze_card + 1) * m + n

fun unsqueeze p = (p div (max_squeeze_card + 1), p mod (max_squeeze_card + 1))

fun boolify (j, b) = 2 * j + (if b then 0 else 1)
fun unboolify j = (j div 2, j mod 2 = 0)

fun suc_rel_for_atom_seq (x, tabulate) =
  (2, suc_rels_base - boolify (squeeze x, tabulate))

fun atom_seq_for_suc_rel (_, j) =
  let val (index, tabulate) = unboolify (~j + suc_rels_base)
  in (unsqueeze index, tabulate) end

fun is_none_product (Product (r1, r2)) =
    is_none_product r1 orelse is_none_product r2
  | is_none_product None = true
  | is_none_product _ = false

fun is_one_rel_expr (Atom _) = true
  | is_one_rel_expr (AtomSeq (1, _)) = true
  | is_one_rel_expr (Var _) = true
  | is_one_rel_expr _ = false

fun inline_rel_expr (Product (r1, r2)) =
    inline_rel_expr r1 andalso inline_rel_expr r2
  | inline_rel_expr Iden = true
  | inline_rel_expr Ints = true
  | inline_rel_expr None = true
  | inline_rel_expr Univ = true
  | inline_rel_expr (Atom _) = true
  | inline_rel_expr (AtomSeq _) = true
  | inline_rel_expr (Rel _) = true
  | inline_rel_expr (Var _) = true
  | inline_rel_expr (RelReg _) = true
  | inline_rel_expr _ = false

fun rel_expr_equal None (Atom _) = SOME false
  | rel_expr_equal None (AtomSeq (k, _)) = SOME (k = 0)
  | rel_expr_equal (Atom _) None = SOME false
  | rel_expr_equal (AtomSeq (k, _)) None = SOME (k = 0)
  | rel_expr_equal (Atom j1) (Atom j2) = SOME (j1 = j2)
  | rel_expr_equal (Atom j) (AtomSeq (k, j0)) = SOME (j = j0 andalso k = 1)
  | rel_expr_equal (AtomSeq (k, j0)) (Atom j) = SOME (j = j0 andalso k = 1)
  | rel_expr_equal (AtomSeq x1) (AtomSeq x2) = SOME (x1 = x2)
  | rel_expr_equal r1 r2 = if r1 = r2 then SOME true else NONE

fun rel_expr_intersects (Atom j1) (Atom j2) = SOME (j1 = j2)
  | rel_expr_intersects (Atom j) (AtomSeq (k, j0)) =
    SOME (j >= j0 andalso j < j0 + k)
  | rel_expr_intersects (AtomSeq (k, j0)) (Atom j) =
    SOME (j >= j0 andalso j < j0 + k)
  | rel_expr_intersects (AtomSeq (k1, j01)) (AtomSeq (k2, j02)) =
    SOME (k1 > 0 andalso k2 > 0 andalso j01 + k1 > j02 andalso j02 + k2 > j01)
  | rel_expr_intersects r1 r2 =
    if is_none_product r1 orelse is_none_product r2 then SOME false else NONE

fun empty_n_ary_rel 0 =
      raise ARG ("Refute_ModelFinder_Peephole.empty_n_ary_rel", "0")
  | empty_n_ary_rel n =
      let
        fun build 1 = None
          | build arity = Product (None, build (arity - 1))
      in
        build n
      end

fun decl_one_set (DeclOne (_, r)) = r
  | decl_one_set _ =
    raise ARG ("Refute_ModelFinder_Peephole.decl_one_set", "not \"DeclOne\"")

fun is_Num (Num _) = true
  | is_Num _ = false

fun dest_Num (Num k) = k
  | dest_Num _ =
    raise ARG ("Refute_ModelFinder_Peephole.dest_Num", "not \"Num\"")

fun num_seq j0 n = map Num (index_seq j0 n)

fun occurs_in_union r (Union (r1, r2)) =
    occurs_in_union r r1 orelse occurs_in_union r r2
  | occurs_in_union r r' = (r = r')

fun s_and True f2 = f2
  | s_and False _ = False
  | s_and f1 True = f1
  | s_and _ False = False
  | s_and f1 f2 = And (f1, f2)

type kodkod_constrs =
  {kk_all: decl list -> formula -> formula,
   kk_exist: decl list -> formula -> formula,
   kk_formula_let: expr_assign list -> formula -> formula,
   kk_formula_if: formula -> formula -> formula -> formula,
   kk_or: formula -> formula -> formula,
   kk_not: formula -> formula,
   kk_iff: formula -> formula -> formula,
   kk_implies: formula -> formula -> formula,
   kk_and: formula -> formula -> formula,
   kk_subset: rel_expr -> rel_expr -> formula,
   kk_rel_eq: rel_expr -> rel_expr -> formula,
   kk_no: rel_expr -> formula,
   kk_lone: rel_expr -> formula,
   kk_one: rel_expr -> formula,
   kk_some: rel_expr -> formula,
   kk_rel_let: expr_assign list -> rel_expr -> rel_expr,
   kk_rel_if: formula -> rel_expr -> rel_expr -> rel_expr,
   kk_union: rel_expr -> rel_expr -> rel_expr,
   kk_difference: rel_expr -> rel_expr -> rel_expr,
   kk_override: rel_expr -> rel_expr -> rel_expr,
   kk_intersect: rel_expr -> rel_expr -> rel_expr,
   kk_product: rel_expr -> rel_expr -> rel_expr,
   kk_join: rel_expr -> rel_expr -> rel_expr,
   kk_closure: rel_expr -> rel_expr,
   kk_reflexive_closure: rel_expr -> rel_expr,
   kk_comprehension: decl list -> formula -> rel_expr,
   kk_project: rel_expr -> int_expr list -> rel_expr,
   kk_project_seq: rel_expr -> int -> int -> rel_expr,
   kk_not3: rel_expr -> rel_expr,
   kk_nat_less: rel_expr -> rel_expr -> rel_expr,
   kk_int_less: rel_expr -> rel_expr -> rel_expr}

(* We assume throughout that Kodkod variables have a "one" constraint. This is
   always the case if Kodkod's skolemization is disabled. *)
fun kodkod_constrs optim nat_card int_card main_j0 =
  let
    fun curry2 f x y = f (x, y)

    val from_bool = atom_for_bool main_j0
    fun from_nat n = Atom (n + main_j0)
    fun to_nat j = j - main_j0
    val to_int = int_for_atom (int_card, main_j0)

    val exists_empty_decl =
      List.exists (fn DeclOne (_, None) => true | _ => false)

    (* An empty declaration determines a quantified formula regardless of
       its body.  Check it before folding a constant body. *)
    fun s_all ds f =
      if exists_empty_decl ds then True
      else case f of
          True => True
        | False => False
        | All (ds', f') => s_all (ds @ ds') f'
        | _ => if null ds then f else All (ds, f)
    fun s_exist ds f =
      if exists_empty_decl ds then False
      else case f of
          True => True
        | False => False
        | Exist (ds', f') => s_exist (ds @ ds') f'
        | _ => if null ds then f else Exist (ds, f)

    fun s_formula_let _ True = True
      | s_formula_let _ False = False
      | s_formula_let assigns f = FormulaLet (assigns, f)

    fun s_not True = False
      | s_not False = True
      | s_not (All (ds, f)) = Exist (ds, s_not f)
      | s_not (Exist (ds, f)) = All (ds, s_not f)
      | s_not (Or (f1, f2)) = And (s_not f1, s_not f2)
      | s_not (Implies (f1, f2)) = And (f1, s_not f2)
      | s_not (And (f1, f2)) = Or (s_not f1, s_not f2)
      | s_not (Not f) = f
      | s_not (No r) = Some r
      | s_not (Some r) = No r
      | s_not f = Not f

    fun s_or True _ = True
      | s_or False f2 = f2
      | s_or _ True = True
      | s_or f1 False = f1
      | s_or f1 f2 = if f1 = f2 then f1 else Or (f1, f2)
    fun s_iff True f2 = f2
      | s_iff False f2 = s_not f2
      | s_iff f1 True = f1
      | s_iff f1 False = s_not f1
      | s_iff f1 f2 = if f1 = f2 then True else Iff (f1, f2)
    fun s_implies True f2 = f2
      | s_implies False _ = True
      | s_implies _ True = True
      | s_implies f1 False = s_not f1
      | s_implies f1 f2 = if f1 = f2 then True else Implies (f1, f2)

    fun s_formula_if True f2 _ = f2
      | s_formula_if False _ f3 = f3
      | s_formula_if f1 True f3 = s_or f1 f3
      | s_formula_if f1 False f3 = s_and (s_not f1) f3
      | s_formula_if f1 f2 True = s_implies f1 f2
      | s_formula_if f1 f2 False = s_and f1 f2
      | s_formula_if f f1 f2 = FormulaIf (f, f1, f2)

    fun s_project r is =
      (case r of
         Project (r1, is') =>
         if List.all is_Num is then
           s_project r1 (map (fn i => List.nth (is', dest_Num i)) is)
         else
           raise SAME ()
       | _ => raise SAME ())
      handle SAME () =>
             let val n = length is in
               if arity_of_rel_expr r = n andalso is = num_seq 0 n then r
               else Project (r, is)
             end

    fun s_xone xone r =
      if is_one_rel_expr r then
        True
      else case arity_of_rel_expr r of
        1 => xone r
      | arity => fold1 (fn f1 => fn f2 => And (f1, f2))
          (map (fn index => xone (s_project r [Num index]))
               (index_seq 0 arity))
    fun s_no None = True
      | s_no (Product (r1, r2)) = s_or (s_no r1) (s_no r2)
      | s_no (Intersect (Closure (Rel x), Iden)) = Acyclic x
      | s_no r = if is_one_rel_expr r then False else No r
    fun s_lone None = True
      | s_lone r = s_xone Lone r
    fun s_one None = False
      | s_one r = s_xone One r
    fun s_some None = False
      | s_some (Atom _) = True
      | s_some (Product (r1, r2)) = s_and (s_some r1) (s_some r2)
      | s_some r = if is_one_rel_expr r then True else Some r

    fun s_not3 (Atom j) = Atom (if j = main_j0 then j + 1 else j - 1)
      | s_not3 (r as Join (r1, r2)) =
        if r2 = Rel not3_rel then r1 else Join (r, Rel not3_rel)
      | s_not3 r = Join (r, Rel not3_rel)

    fun s_rel_eq r1 r2 =
      (case (r1, r2) of
         (Join (r11, Rel x), _) =>
         if x = not3_rel then s_rel_eq r11 (s_not3 r2) else raise SAME ()
       | (RelIf (f, r11, r12), _) =>
         if inline_rel_expr r2 then
           s_formula_if f (s_rel_eq r11 r2) (s_rel_eq r12 r2)
         else
           raise SAME ()
       | (_, RelIf (f, r21, r22)) =>
         if inline_rel_expr r1 then
           s_formula_if f (s_rel_eq r1 r21) (s_rel_eq r1 r22)
         else
           raise SAME ()
       | (RelLet (bs, r1'), Atom _) => s_formula_let bs (s_rel_eq r1' r2)
       | (Atom _, RelLet (bs, r2')) => s_formula_let bs (s_rel_eq r1 r2')
       | _ => raise SAME ())
      handle SAME () =>
             case rel_expr_equal r1 r2 of
               SOME true => True
             | SOME false => False
             | NONE =>
               case (r1, r2) of
                 (_, RelIf (f, r21, r22)) =>
                  if inline_rel_expr r1 then
                    s_formula_if f (s_rel_eq r1 r21) (s_rel_eq r1 r22)
                  else
                    RelEq (r1, r2)
               | (RelIf (f, r11, r12), _) =>
                  if inline_rel_expr r2 then
                    s_formula_if f (s_rel_eq r11 r2) (s_rel_eq r12 r2)
                  else
                    RelEq (r1, r2)
               | (_, None) => s_no r1
               | (None, _) => s_no r2
               | _ => RelEq (r1, r2)
    fun s_subset (Atom j1) (Atom j2) = formula_for_bool (j1 = j2)
      | s_subset (Atom j) (AtomSeq (k, j0)) =
        formula_for_bool (j >= j0 andalso j < j0 + k)
      | s_subset (Union (r11, r12)) r2 =
        s_and (s_subset r11 r2) (s_subset r12 r2)
      | s_subset r1 (r2 as Union (r21, r22)) =
        if is_one_rel_expr r1 then
          s_or (s_subset r1 r21) (s_subset r1 r22)
        else
          if s_subset r1 r21 = True orelse s_subset r1 r22 = True orelse
             r1 = r2 then
            True
          else
            Subset (r1, r2)
      | s_subset r1 r2 =
        if r1 = r2 orelse is_none_product r1 then True
        else if is_none_product r2 then s_no r1
        else if List.all is_one_rel_expr [r1, r2] then s_rel_eq r1 r2
        else Subset (r1, r2)

    fun s_rel_let [b as AssignRelReg (x', r')] (r as RelReg x) =
        if x = x' then r' else RelLet ([b], r)
      | s_rel_let bs r = RelLet (bs, r)

    fun s_rel_if f r1 r2 =
      (case (f, r1, r2) of
         (True, _, _) => r1
       | (False, _, _) => r2
       | (No r1', None, RelIf (One r2', r3', r4')) =>
         if r1' = r2' andalso r2' = r3' then s_rel_if (Lone r1') r1' r4'
         else raise SAME ()
       | _ => raise SAME ())
      handle SAME () => if r1 = r2 then r1 else RelIf (f, r1, r2)

    fun s_union r1 (Union (r21, r22)) = s_union (s_union r1 r21) r22
      | s_union r1 r2 =
        if is_none_product r1 then r2
        else if is_none_product r2 then r1
        else if r1 = r2 then r1
        else if occurs_in_union r2 r1 then r1
        else Union (r1, r2)
    fun s_difference r1 r2 =
      if is_none_product r1 orelse is_none_product r2 then r1
      else if r1 = r2 then empty_n_ary_rel (arity_of_rel_expr r1)
      else Difference (r1, r2)
    fun s_override r1 r2 =
      if is_none_product r2 then r1
      else if is_none_product r1 then r2
      else Override (r1, r2)
    fun s_intersect r1 r2 =
      case rel_expr_intersects r1 r2 of
        SOME true => if r1 = r2 then r1 else Intersect (r1, r2)
      | SOME false => empty_n_ary_rel (arity_of_rel_expr r1)
      | NONE => if is_none_product r1 then r1
                else if is_none_product r2 then r2
                else Intersect (r1, r2)
    fun s_product r1 r2 =
      if is_none_product r1 then
        Product (r1, empty_n_ary_rel (arity_of_rel_expr r2))
      else if is_none_product r2 then
        Product (empty_n_ary_rel (arity_of_rel_expr r1), r2)
      else
        Product (r1, r2)
    fun s_join r1 (Product (Product (r211, r212), r22)) =
        Product (s_join r1 (Product (r211, r212)), r22)
      | s_join (Product (r11, Product (r121, r122))) r2 =
        Product (r11, s_join (Product (r121, r122)) r2)
      | s_join None r = empty_n_ary_rel (arity_of_rel_expr r - 1)
      | s_join r None = empty_n_ary_rel (arity_of_rel_expr r - 1)
      | s_join (Product (None, None)) r = empty_n_ary_rel (arity_of_rel_expr r)
      | s_join r (Product (None, None)) = empty_n_ary_rel (arity_of_rel_expr r)
      | s_join Iden r2 = r2
      | s_join r1 Iden = r1
      | s_join r1 (r2 as Product (r21, r22)) =
        if arity_of_rel_expr r1 = 1 then
          case rel_expr_intersects r1 r21 of
            SOME true => r22
          | SOME false => empty_n_ary_rel (arity_of_rel_expr r2 - 1)
          | NONE => Join (r1, r2)
        else
          Join (r1, r2)
      | s_join (r1 as Product (r11, r12)) r2 =
        if arity_of_rel_expr r2 = 1 then
          case rel_expr_intersects r2 r12 of
            SOME true => r11
          | SOME false => empty_n_ary_rel (arity_of_rel_expr r1 - 1)
          | NONE => Join (r1, r2)
        else
          Join (r1, r2)
      | s_join r1 (r2 as RelIf (f, r21, r22)) =
        if inline_rel_expr r1 then s_rel_if f (s_join r1 r21) (s_join r1 r22)
        else Join (r1, r2)
      | s_join (r1 as RelIf (f, r11, r12)) r2 =
        if inline_rel_expr r2 then s_rel_if f (s_join r11 r2) (s_join r12 r2)
        else Join (r1, r2)
      | s_join (r1 as Atom j1) (r2 as Rel (x as (2, _))) =
        if x = suc_rel then
          let val n = to_nat j1 + 1 in
            if n < nat_card then from_nat n else None
          end
        else
          Join (r1, r2)
      | s_join r1 (r2 as Project (r21, Num k :: is)) =
        if k = arity_of_rel_expr r21 - 1 andalso arity_of_rel_expr r1 = 1 then
          s_project (s_join r21 r1) is
        else
          Join (r1, r2)
      | s_join r1 (Join (r21, r22 as Rel (x as (3, _)))) =
        ((if x = nat_add_rel then
            case (r21, r1) of
              (Atom j1, Atom j2) =>
              let val n = to_nat j1 + to_nat j2 in
                if n < nat_card then from_nat n else None
              end
            | (Atom j, r) =>
              (case to_nat j of
                 0 => r
               | 1 => s_join r (Rel suc_rel)
               | _ => raise SAME ())
            | (r, Atom j) =>
              (case to_nat j of
                 0 => r
               | 1 => s_join r (Rel suc_rel)
               | _ => raise SAME ())
            | _ => raise SAME ()
          else if x = nat_subtract_rel then
            case (r21, r1) of
              (Atom j1, Atom j2) => from_nat (nat_minus (to_nat j1) (to_nat j2))
            | _ => raise SAME ()
          else if x = nat_multiply_rel then
            case (r21, r1) of
              (Atom j1, Atom j2) =>
              let val n = to_nat j1 * to_nat j2 in
                if n < nat_card then from_nat n else None
              end
            | (Atom j, r) =>
              (case to_nat j of 0 => Atom j | 1 => r | _ => raise SAME ())
            | (r, Atom j) =>
              (case to_nat j of 0 => Atom j | 1 => r | _ => raise SAME ())
            | _ => raise SAME ()
          else
            raise SAME ())
         handle SAME () => List.foldr Join r22 [r1, r21])
      | s_join r1 r2 = Join (r1, r2)

    fun s_closure Iden = Iden
      | s_closure r = if is_none_product r then r else Closure r
    fun s_reflexive_closure Iden = Iden
      | s_reflexive_closure r =
        if is_none_product r then Iden else ReflexiveClosure r

    fun s_comprehension ds False = empty_n_ary_rel (length ds)
      | s_comprehension ds True = fold1 s_product (map decl_one_set ds)
      | s_comprehension [d as DeclOne ((1, j1), r)]
                        (f as RelEq (Var (1, j2), Atom j)) =
        if j1 = j2 andalso rel_expr_intersects (Atom j) r = SOME true then
          Atom j
        else
          Comprehension ([d], f)
      | s_comprehension ds f = Comprehension (ds, f)

    fun s_project_seq r =
      let
        fun aux arity r j0 n =
          if j0 = 0 andalso arity = n then
            r
          else case r of
            RelIf (f, r1, r2) =>
            s_rel_if f (aux arity r1 j0 n) (aux arity r2 j0 n)
          | Product (r1, r2) =>
            let
              val arity2 = arity_of_rel_expr r2
              val arity1 = arity - arity2
              val n1 = Int.min (nat_minus arity1 j0, n)
              val n2 = n - n1
              fun one () = aux arity1 r1 j0 n1
              fun two () = aux arity2 r2 (nat_minus j0 arity1) n2
            in
              case (n1, n2) of
                (0, _) => s_rel_if (s_some r1) (two ()) (empty_n_ary_rel n2)
              | (_, 0) => s_rel_if (s_some r2) (one ()) (empty_n_ary_rel n1)
              | _ => s_product (one ()) (two ())
            end
          | _ => s_project r (num_seq j0 n)
      in aux (arity_of_rel_expr r) r end

    fun s_nat_less (Atom j1) (Atom j2) = from_bool (j1 < j2)
      | s_nat_less r1 r2 =
        List.foldl (fn (r, result) => s_join r result)
          (Rel nat_less_rel) [r1, r2]
    fun s_int_less (Atom j1) (Atom j2) = from_bool (to_int j1 < to_int j2)
      | s_int_less r1 r2 =
        List.foldl (fn (r, result) => s_join r result)
          (Rel int_less_rel) [r1, r2]

    fun d_project_seq r j0 n = Project (r, num_seq j0 n)
    fun d_not3 r = Join (r, Rel not3_rel)
    fun d_nat_less r1 r2 = List.foldl Join (Rel nat_less_rel) [r1, r2]
    fun d_int_less r1 r2 = List.foldl Join (Rel int_less_rel) [r1, r2]
  in
    if optim then
      {kk_all = s_all, kk_exist = s_exist, kk_formula_let = s_formula_let,
       kk_formula_if = s_formula_if, kk_or = s_or, kk_not = s_not,
       kk_iff = s_iff, kk_implies = s_implies, kk_and = s_and,
       kk_subset = s_subset, kk_rel_eq = s_rel_eq, kk_no = s_no,
       kk_lone = s_lone, kk_one = s_one, kk_some = s_some,
       kk_rel_let = s_rel_let, kk_rel_if = s_rel_if, kk_union = s_union,
       kk_difference = s_difference, kk_override = s_override,
       kk_intersect = s_intersect, kk_product = s_product, kk_join = s_join,
       kk_closure = s_closure, kk_reflexive_closure = s_reflexive_closure,
       kk_comprehension = s_comprehension, kk_project = s_project,
       kk_project_seq = s_project_seq, kk_not3 = s_not3,
       kk_nat_less = s_nat_less, kk_int_less = s_int_less}
    else
      {kk_all = curry2 All, kk_exist = curry2 Exist,
       kk_formula_let = curry2 FormulaLet,
       kk_formula_if = curry3 FormulaIf,
       kk_or = curry2 Or, kk_not = Not, kk_iff = curry2 Iff,
       kk_implies = curry2 Implies, kk_and = curry2 And,
       kk_subset = curry2 Subset, kk_rel_eq = curry2 RelEq,
       kk_no = No, kk_lone = Lone, kk_one = One, kk_some = Some,
       kk_rel_let = curry2 RelLet, kk_rel_if = curry3 RelIf,
       kk_union = curry2 Union, kk_difference = curry2 Difference,
       kk_override = curry2 Override, kk_intersect = curry2 Intersect,
       kk_product = curry2 Product, kk_join = curry2 Join,
       kk_closure = Closure, kk_reflexive_closure = ReflexiveClosure,
       kk_comprehension = curry2 Comprehension,
       kk_project = curry2 Project,
       kk_project_seq = d_project_seq, kk_not3 = d_not3,
       kk_nat_less = d_nat_less, kk_int_less = d_int_less}
  end

end;
