(* ===================================================================== *)
(* FILE          : boolSyntax.sml                                        *)
(* DESCRIPTION   : Derived HOL syntax operations. Mostly translated from *)
(*                 the hol88 source.                                     *)
(*                                                                       *)
(* AUTHORS       : (c) Mike Gordon, University of Cambridge              *)
(*                     Konrad Slind, University of Calgary               *)
(* Modified      : September 1997, Ken Larsen (functor removal)          *)
(* Modified      : July 2000, Konrad Slind                               *)
(* ===================================================================== *)

structure boolSyntax :> boolSyntax =
struct

open Feedback Lib HolKernel boolTheory;

val ERR = mk_HOL_ERR "boolSyntax"

(*---------------------------------------------------------------------------
       Basic constants
 ---------------------------------------------------------------------------*)

val equality     = prim_mk_const {Name = "=",            Thy = "min"}
val implication  = prim_mk_const {Name = "==>",          Thy = "min"}
val select       = prim_mk_const {Name = "@",            Thy = "min"}
val T            = prim_mk_const {Name = "T",            Thy = "bool"}
val F            = prim_mk_const {Name = "F",            Thy = "bool"}
val universal    = prim_mk_const {Name = "!",            Thy = "bool"}
val existential  = prim_mk_const {Name = "?",            Thy = "bool"}
val exists1      = prim_mk_const {Name = "?!",           Thy = "bool"}
val conjunction  = prim_mk_const {Name = "/\\",          Thy = "bool"}
val disjunction  = prim_mk_const {Name = "\\/",          Thy = "bool"}
val negation     = prim_mk_const {Name = "~",            Thy = "bool"}
val conditional  = prim_mk_const {Name = "COND",         Thy = "bool"}
val let_tm       = prim_mk_const {Name = "LET",          Thy = "bool"}
val arb          = prim_mk_const {Name = "ARB",          Thy = "bool"}
val the_value    = prim_mk_const {Name = "the_value",    Thy = "bool"}
val bool_case    = prim_mk_const {Name = "bool_case",    Thy = "bool"}
val literal_case = prim_mk_const {Name = "literal_case", Thy = "bool"}
val bounded_tm   = prim_mk_const {Name = "BOUNDED",      Thy = "bool"}

(*---------------------------------------------------------------------------
          Derived syntax operations
 ---------------------------------------------------------------------------*)

fun mk_eq (lhs, rhs) =
   list_mk_comb (inst [alpha |-> type_of lhs] equality, [lhs, rhs])
   handle HOL_ERR _ => raise ERR "mk_eq" "lhs and rhs have different types"

fun mk_imp (ant, conseq) =
   list_mk_comb (implication, [ant, conseq])
   handle HOL_ERR _ => raise ERR "mk_imp" "Non-boolean argument"

val mk_select  = mk_binder select      "mk_select"
val mk_forall  = mk_binder universal   "mk_forall"
val mk_exists  = mk_binder existential "mk_exists"
val mk_exists1 = mk_binder exists1     "mk_exists1"

fun mk_conj (conj1, conj2) =
   list_mk_comb (conjunction, [conj1, conj2])
   handle HOL_ERR _ => raise ERR "mk_conj" "Non-boolean argument"

fun mk_disj (disj1, disj2) =
   list_mk_comb (disjunction, [disj1, disj2])
   handle HOL_ERR _ => raise ERR "mk_disj" "Non-boolean argument"

fun mk_neg M =
   with_exn mk_comb (negation, M) (ERR "mk_neg" "Non-boolean argument")

fun mk_cond (cond, larm, rarm) =
   list_mk_comb (inst [alpha |-> type_of larm] conditional, [cond, larm, rarm])
   handle HOL_ERR _ => raise ERR "mk_cond" ""

fun mk_let (func, arg) =
   let
      val (dom, rng) = dom_rng (type_of func)
   in
      list_mk_comb (inst [alpha |-> dom, beta |-> rng] let_tm, [func, arg])
   end
   handle HOL_ERR _ => raise ERR "mk_let" ""

fun mk_bool_case (a0, a1, b) =
   list_mk_comb (inst [alpha |-> type_of a0] bool_case, [a0, a1, b])
   handle HOL_ERR _ => raise ERR "mk_bool_case" ""

fun mk_literal_case (func, arg) =
   let
      val (dom, rng) = dom_rng (type_of func)
   in
      list_mk_comb
         (inst [alpha |-> dom, beta |-> rng] literal_case, [func, arg])
   end
   handle HOL_ERR _ => raise ERR "mk_literal_case" ""

fun mk_arb ty = inst [alpha |-> ty] arb

fun mk_itself ty = inst [alpha |-> ty] the_value

val mk_icomb = Lib.uncurry HolKernel.mk_monop

(*--------------------------------------------------------------------------*
 *                Destructors                                               *
 *--------------------------------------------------------------------------*)

local
   val dest_eq_ty_err   = ERR "dest_eq(_ty)"      "not an \"=\""
   val lhs_err          = ERR "lhs"               "not an \"=\""
   val rhs_err          = ERR "rhs"               "not an \"=\""
   val lhand_err        = ERR "lhand"             "not a binary comb"
   val dest_imp_err     = ERR "dest_imp"          "not an \"==>\""
   val dest_cond_err    = ERR "dest_cond"         "not a conditional"
   val bool_case_err    = ERR "dest_bool_case"    "not a \"bool_case\""
   val literal_case_err = ERR "dest_literal_case" "not a \"literal_case\""
in
   val dest_eq       = dest_binop equality dest_eq_ty_err
   fun dest_eq_ty M  = let val (l, r) = dest_eq M in (l, r, type_of l) end
   fun lhs M         = with_exn (fst o dest_eq) M lhs_err
   fun rhs M         = with_exn (snd o dest_eq) M rhs_err
   fun lhand M       = with_exn (rand o rator) M lhand_err

   val dest_neg      = dest_monop negation (ERR "dest_neg" "not a negation")
   val dest_imp_only = dest_binop implication dest_imp_err
   fun dest_imp M    = dest_imp_only M
                       handle HOL_ERR _ => (dest_neg M, F)
                       handle HOL_ERR _ => raise dest_imp_err
   val dest_select  = dest_binder select (ERR "dest_select" "not a \"@\"")
   val dest_forall  = dest_binder universal (ERR "dest_forall" "not a \"!\"")
   val dest_exists  = dest_binder existential (ERR "dest_exists" "not a \"?\"")
   val dest_exists1 = dest_binder exists1 (ERR "dest_exists1" "not a \"?!\"")
   val dest_conj = dest_binop conjunction (ERR "dest_conj"   "not a \"/\\\"")
   val dest_disj = dest_binop disjunction (ERR "dest_disj"   "not a \"\\/\"")
   val dest_let  = dest_binop let_tm      (ERR "dest_let"    "not a let term")

   fun dest_cond M =
      let
         val (Rator, t2) = with_exn dest_comb M dest_cond_err
         val (b, t1) = dest_binop conditional dest_cond_err Rator
      in
         (b, t1, t2)
      end

   fun dest_bool_case M =
      let
         val (Rator, b) = with_exn dest_comb M bool_case_err
         val (a0, a1) = dest_binop bool_case bool_case_err Rator
      in
         (a0, a1, b)
      end

   val dest_literal_case = dest_binop literal_case literal_case_err

   fun dest_arb M =
      if same_const M arb then type_of M else raise ERR "dest_arb" ""

   fun dest_itself M =
      if same_const M the_value
         then hd (snd (dest_type (type_of M)))
      else raise ERR "dest_itself" ""
end (* local *)

(*---------------------------------------------------------------------------
             Selectors
 ---------------------------------------------------------------------------*)

val is_eq           = can dest_eq
val is_imp          = can dest_imp
val is_imp_only     = can dest_imp_only
val is_select       = can dest_select
val is_forall       = can dest_forall
val is_exists       = can dest_exists
val is_exists1      = can dest_exists1
val is_conj         = can dest_conj
val is_disj         = can dest_disj
val is_neg          = can dest_neg
val is_cond         = can dest_cond
val is_let          = can dest_let
val is_bool_case    = can dest_bool_case
val is_literal_case = can dest_literal_case
val is_arb          = same_const arb
val is_the_value    = same_const the_value

(*---------------------------------------------------------------------------*
 * Construction and destruction functions that deal with SML lists           *
 *---------------------------------------------------------------------------*)

val list_mk_comb   = HolKernel.list_mk_comb
val list_mk_abs    = HolKernel.list_mk_abs

val list_mk_forall = list_mk_binder (SOME universal)
val list_mk_exists = list_mk_binder (SOME existential)
val list_mk_conj   = list_mk_rbinop (curry mk_conj)
val list_mk_disj   = list_mk_rbinop (curry mk_disj)

fun list_mk_imp (A, c) = list_mk_rbinop (curry mk_imp) (A @ [c])

fun list_mk_icomb (f, args) = List.foldl (fn (a, t) => mk_icomb (t, a)) f args

val strip_comb     = HolKernel.strip_comb
val strip_abs      = HolKernel.strip_abs
val strip_forall   = HolKernel.strip_binder (SOME universal)
val strip_exists   = HolKernel.strip_binder (SOME existential)
val strip_conj     = strip_binop (total dest_conj)
val strip_disj     = strip_binop (total dest_disj)

fun dest_strip_comb t =
   let
      val (l, r) = strip_comb t
      val {Thy = thy, Name = name, ...} = Term.dest_thy_const l
   in
      (thy ^ "$" ^ name, r)
   end

val strip_imp =
   let
      val desti = total dest_imp
      fun strip A M =
         case desti M of
            NONE => (List.rev A, M)
          | SOME (ant, conseq) => strip (ant :: A) conseq
   in
      strip []
   end

val strip_imp_only =
   let
      val desti = total dest_imp_only
      fun strip A M =
         case desti M of
            NONE => (List.rev A, M)
          | SOME (ant, conseq) => strip (ant :: A) conseq
   in
      strip []
   end

val strip_neg =
   let
      val destn = total dest_neg
      fun strip A M =
         case destn M of
            NONE => (M, A)
          | SOME N => strip (A + 1) N
   in
      strip 0
   end

fun gen_all tm = list_mk_forall (free_vars tm, tm)

(*---------------------------------------------------------------------------*
 * Construction and destruction of function types from/to lists of types     *
 * Michael Norrish - December 1999                                           *
 *---------------------------------------------------------------------------*)

val list_mk_fun = HolKernel.list_mk_fun
val strip_fun   = HolKernel.strip_fun

(*---------------------------------------------------------------------------
     Linking definitional principles and signature operations
     with grammars.
 ---------------------------------------------------------------------------*)

fun dest t =
   let
      val (lhs, rhs) = dest_eq (snd (strip_forall t))
      val (f, args) = strip_comb lhs
   in
      if all is_var args
         then (args, mk_eq (f, list_mk_abs (args, rhs)))
      else raise ERR "new_definition" "non-variable argument"
   end

fun RIGHT_BETA th = TRANS th (BETA_CONV (rhs (concl th)))

fun post (V, th) =
   let
      fun add_var v th = RIGHT_BETA (AP_THM th v)
      val cname = fst (dest_const (lhs (concl th)))
   in
      itlist GEN V (rev_itlist add_var V th)
   end

val _ = Definition.new_definition_hook := (dest, post)

open Parse

fun defname t =
   let
      val head = #1 (strip_comb (lhs (#2 (strip_forall t))))
   in
      fst (dest_var head handle HOL_ERR _ => dest_const head)
   end

fun new_infixr_definition (s, t, p) =
   Definition.new_definition (s, t) before set_fixity (defname t) (Infixr p)

fun new_infixl_definition (s, t, p) =
   Definition.new_definition (s, t) before set_fixity (defname t) (Infixl p)

fun new_binder_definition (s, t) =
   Definition.new_definition (s, t) before Parse.set_fixity (defname t) Binder

fun new_type_definition (name, inhab_thm) =
   Definition.new_type_definition (name, inhab_thm) before Parse.add_type name

fun new_infix (Name, Ty, Prec) =
   Theory.new_constant (Name, Ty)
   before Parse.add_infix (Name, Prec, Parse.RIGHT)

fun new_binder (p as (Name, _)) =
   Theory.new_constant p before set_fixity Name Binder

fun new_infix_type (x as {Name, Arity, ParseName, Prec, Assoc}) =
   let
      val _ = Arity = 2 orelse
              raise ERR "new_infix_type" "Infix types must have arity 2"
   in
      Theory.new_type (Name, Arity)
      before Parse.add_infix_type
               {Name = Name, ParseName = ParseName, Prec = Prec, Assoc = Assoc}
   end

(*---------------------------------------------------------------------------*)
(* Lifter for booleans                                                       *)
(*---------------------------------------------------------------------------*)

fun lift_bool _ true  = T
  | lift_bool _ false = F

(*--------------------------------------------------------------------------*)
(*  Some simple algebraic properties expressed at the term level.           *)
(*--------------------------------------------------------------------------*)

val (comm_tm, assoc_tm, idem_tm, ldistrib_tm, rdistrib_tm) =
   let
      val f = mk_var ("f", alpha --> alpha --> alpha)
      val g = mk_var ("g", alpha --> alpha --> alpha)
      val g1 = mk_var ("g", alpha --> alpha)
      val x = mk_var ("x", alpha)
      val y = mk_var ("y", alpha)
      val z = mk_var ("z", alpha)
   in
      (mk_eq (list_mk_comb (f, [x, y]), list_mk_comb (f, [y, x])),
       mk_eq (list_mk_comb (f, [x, list_mk_comb (f, [y, z])]),
              list_mk_comb (f, [list_mk_comb (f, [x, y]), z])),
       mk_eq (mk_comb (g1, mk_comb (g1, x)), mk_comb (g1, x)),
       mk_eq (list_mk_comb (f, [x, list_mk_comb (g, [y, z])]),
              list_mk_comb (g, [list_mk_comb (f, [x, y]),
                                list_mk_comb (f, [x, z])])),
       mk_eq (list_mk_comb (f, [list_mk_comb (g, [y, z]), x]),
              list_mk_comb (g, [list_mk_comb (f, [y, x]),
                                list_mk_comb (f, [z, x])])))
   end

(* ===================================================================== *)
(* Syntactic operations on restricted quantifications.                   *)
(* These ought to be generalised to all kinds of restrictions,           *)
(* but one thing at a time.                                              *)
(* --------------------------------------------------------------------- *)

val (mk_res_forall, mk_res_exists, mk_res_exists_unique,
     mk_res_select, mk_res_abstract) =
   let
      fun mk_res_quan cons s (x, t1, t2) =
         let
            val xty = type_of x
            val t2_ty = type_of t2
            val ty = (xty --> bool) --> (xty --> t2_ty)
                      --> (if cons = "RES_ABSTRACT"
                              then xty --> t2_ty
                           else if cons = "RES_SELECT"
                              then xty
                           else Type.bool)
         in
            mk_comb (mk_comb (mk_thy_const {Name=cons, Thy="bool", Ty=ty}, t1),
                     mk_abs (x, t2))
         end
         handle _ => raise ERR "mk_res_quan" s
    in
       (mk_res_quan "RES_FORALL"        "mk_res_forall",
        mk_res_quan "RES_EXISTS"        "mk_res_exists",
        mk_res_quan "RES_EXISTS_UNIQUE" "mk_res_exists_unique",
        mk_res_quan "RES_SELECT"        "mk_res_select",
        mk_res_quan "RES_ABSTRACT"      "mk_res_abstract")
    end

fun list_mk_res_forall (ress, body) =
   (itlist (fn (v, p) => fn b => mk_res_forall (v, p, b)) ress body)
   handle _ => raise ERR "list_mk_res_forall" ""

fun list_mk_res_exists (ress, body) =
   (itlist (fn (v, p) => fn b => mk_res_exists (v, p, b)) ress body)
   handle _ => raise ERR "list_mk_res_exists" ""

val (dest_res_forall, dest_res_exists, dest_res_exists_unique,
     dest_res_select, dest_res_abstract) =
   let
      fun dest_res_quan cons s =
         let
            val check =
               assert (fn c =>
                          let
                             val {Name, Thy, ...} = dest_thy_const c
                          in
                             Name = cons andalso Thy = "bool"
                          end)
         in
            fn tm =>
               let
                  val (op1, rand1) = dest_comb tm
                  val (op2, c1) = dest_comb op1
                  val _ = check op2
                  val (c2, c3) = dest_abs rand1
               in
                  (c2, c1, c3)
               end
         end
         handle _ => raise ERR "dest_res_quan" s
    in
       (dest_res_quan "RES_FORALL"        "dest_res_forall",
        dest_res_quan "RES_EXISTS"        "dest_res_exists",
        dest_res_quan "RES_EXISTS_UNIQUE" "dest_res_exists_unique",
        dest_res_quan "RES_SELECT"        "dest_res_select",
        dest_res_quan "RES_ABSTRACT"      "dest_res_abstract")
    end

fun strip_res_forall fm =
   let
      val (bv, pred, body) = dest_res_forall fm
      val (prs, core) = strip_res_forall body
   in
      ((bv, pred) :: prs, core)
   end
   handle _ => ([], fm)

fun strip_res_exists fm =
   let
      val (bv, pred, body) = dest_res_exists fm
      val (prs, core) = strip_res_exists body
   in
      ((bv, pred) :: prs, core)
   end
   handle _ => ([], fm)

val is_res_forall        = can dest_res_forall
val is_res_exists        = can dest_res_exists
val is_res_exists_unique = can dest_res_exists_unique
val is_res_select        = can dest_res_select
val is_res_abstract      = can dest_res_abstract

fun mk n = prim_mk_const {Name = n, Thy = "bool"}

val res_forall_tm   = mk "RES_FORALL"
val res_exists_tm   = mk "RES_EXISTS"
val res_exists1_tm  = mk "RES_EXISTS_UNIQUE"
val res_select_tm   = mk "RES_SELECT"
val res_abstract_tm = mk "RES_ABSTRACT"

end
