(* ========================================================================= *)
(* MAPPING BETWEEN HOL AND FIRST-ORDER LOGIC.                                *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

(*
app load ["tautLib", "mlibUseful", "mlibTerm", "mlibMatch", "mlibThm"];
*)

(*
*)
structure folMapping :> folMapping =
struct

open HolKernel Parse boolLib;

infix THENR ## |->;

type 'a pp    = 'a mlibUseful.pp;
type term1    = mlibTerm.term;
type formula1 = mlibTerm.formula;
type thm1     = mlibThm.thm;
type vars     = term list * hol_type list;

val assert     = mlibUseful.assert;
val wrap       = mlibUseful.wrap;
val pinst      = matchTools.pinst;
val INST_TY    = matchTools.INST_TY;
val PINST      = matchTools.PINST;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val () = mlibUseful.traces := insert "folMapping" (!mlibUseful.traces);

val chat = mlibUseful.trace "folMapping";

(* ------------------------------------------------------------------------- *)
(* Mapping parameters.                                                       *)
(* ------------------------------------------------------------------------- *)

type parameters =
  {higher_order : bool,       (* Application is a first-order function *)
   with_types   : bool};      (* First-order terms include HOL type info *)

val defaults =
  {higher_order = false,
   with_types   = false};

fun update_parm_higher_order f (parm : parameters) : parameters =
  let val {higher_order, with_types} = parm
  in {higher_order = f higher_order, with_types = with_types}
  end;

fun update_parm_with_types f (parm : parameters) : parameters =
  let val {higher_order, with_types} = parm
  in {higher_order = higher_order, with_types = f with_types}
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

val ERR = mk_HOL_ERR "folMapping";
val BUG = mlibUseful.BUG;

fun zipwith f =
  let
    fun z l [] [] = l
      | z l (x :: xs) (y :: ys) = z (f x y :: l) xs ys
      | z _ _ _ = raise ERR "zipwith" "lists different lengths";
  in
    fn xs => fn ys => rev (z [] xs ys)
  end;

fun possibly f x = case total f x of SOME y => y | NONE => x;

fun dest_prefix p =
  let
    fun check s = assert (String.isPrefix p s) (ERR "dest_prefix" "")
    val size_p = size p
  in
    fn s => (check s; String.extract (s, size_p, NONE))
  end;

fun is_prefix p = can (dest_prefix p);

fun mk_prefix p s = p ^ s;

val dest_prime = dest_prefix "'";
val is_prime   = is_prefix   "'";
val mk_prime   = mk_prefix   "'";

fun dest_const_name s =
  let val n = index (equal #".") (String.explode s)
  in (String.extract (s, 0, SOME n), String.extract (s, n + 1, NONE))
  end;
val is_const_name = can dest_const_name;
fun mk_const_name (t, c) = t ^ "." ^ c;

val type_vars_in_terms = foldl (fn (h, t) => union (type_vars_in_term h) t) [];

fun list_mk_conj' [] = T | list_mk_conj' l = list_mk_conj l;
fun list_mk_disj' [] = F | list_mk_disj' l = list_mk_disj l;

fun change_vars (tmG, tyG) (tmV, tyV) =
  let
    fun tyF v = let val g = tyG v in (g, v |-> g) end
    val (tyV', tyS) = unzip (map tyF tyV)
    fun tmF v = let val v' = inst tyS v val g = tmG v' in (g, v' |-> g) end
    val (tmV', tmS) = unzip (map tmF tmV)
  in
    ((tmV', tyV'), (tmS, tyS))
  end;

fun gen_alpha c f (varV, a) =
  let val (varW, sub) = c varV in (varW, f sub a) end;

fun gen_vfree_vars varP c a = (matchTools.vfree_vars varP (c a), a);

fun f THENR (g : rule) : rule = g o f;
fun REPEATR f : rule = repeat f;

fun terms_to_string tms =
  String.concat (map (fn x => "\n" ^ Parse.term_to_string x) tms) ^ "\n";

(* ------------------------------------------------------------------------- *)
(* "new" variables can be instantiated; everything else is a local constant. *)
(* ------------------------------------------------------------------------- *)

local
  val prefix     = "XXfolXX";
  val tag        = mk_prefix prefix;
  val untag      = dest_prefix prefix;
  val new_string = mlibUseful.int_to_string o mlibUseful.new_int;
in
  val fake_new_tyvar = mk_vartype o mk_prime o tag;
  val new_tyvar      = fake_new_tyvar o new_string;
  val is_new_tyvar   = can (untag o dest_prime o dest_vartype);
  val fake_new_var   = mk_var o (tag ## I);
  val new_var        = fake_new_var o (new_string ## I) o pair ();
  val is_new_var     = can (untag o fst o dest_var);
end;

val all_new_tyvars =
  W (inst o map (fn v => v |-> new_tyvar ()) o type_vars_in_term);

val to_gen      = (genvar       o type_of,  gen_tyvar o K ());
val to_new      = (new_var      o type_of,  new_tyvar o K ());
val to_fake_new = (fake_new_var o dest_var,
                   fake_new_tyvar o dest_prime o dest_vartype);

val new_free_vars = gen_vfree_vars (is_new_var, is_new_tyvar);

val fresh_tyvars =
  let fun f ty = if is_new_tyvar ty then SOME (ty |-> new_tyvar ()) else NONE
  in List.mapPartial f o type_vars_in_terms
  end;

fun freshen_tyvars  tm  = inst (fresh_tyvars [tm]) tm;
fun freshenl_tyvars tms = map (inst (fresh_tyvars tms)) tms;

val new_match_type  = matchTools.vmatch_type  is_new_tyvar;
val new_unify_type  = matchTools.vunify_type  is_new_tyvar;
val new_unifyl_type = matchTools.vunifyl_type is_new_tyvar;
val new_match_ty    = matchTools.vmatch       (K false, is_new_tyvar);
val new_unify_ty    = matchTools.vunify       (K false, is_new_tyvar);
val new_unifyl_ty   = matchTools.vunifyl      (K false, is_new_tyvar);
val new_match       = matchTools.vmatch       (is_new_var, is_new_tyvar);
val new_match_uty   = matchTools.vmatch_uty   (is_new_var, is_new_tyvar);
val new_unify       = matchTools.vunify       (is_new_var, is_new_tyvar);
val new_unifyl      = matchTools.vunifyl      (is_new_var, is_new_tyvar);

(* ------------------------------------------------------------------------- *)
(* Worker theorems for first-order proof translation.                        *)
(* ------------------------------------------------------------------------- *)

val HIDE_LITERAL = prove
  (``!a. a ==> ~a ==> F``,
   tautLib.TAUT_TAC);

val SHOW_LITERAL = prove
  (``!x. (~x ==> F) ==> x``,
   tautLib.TAUT_TAC);

val INITIALIZE_CLAUSE = prove
  (``!a b. a \/ b ==> ~a ==> b``,
   tautLib.TAUT_TAC);

val FINALIZE_CLAUSE = prove
  (``!a b. (~a ==> b) ==> (a \/ b)``,
   tautLib.TAUT_TAC);

val RESOLUTION = prove
  (``!a. a /\ ~a ==> F``,
   tautLib.TAUT_TAC);

val EXCLUDED_MIDDLE' = prove
  (``!t. ~t \/ t``,
   tautLib.TAUT_TAC);

(* ------------------------------------------------------------------------- *)
(* Operations on HOL literals and clauses.                                   *)
(* ------------------------------------------------------------------------- *)

(*
val negative_literal = is_neg;

val positive_literal = not o negative_literal;

fun negate_literal lit =
  if positive_literal lit then mk_neg lit else dest_neg lit;

fun literal_atom lit = if positive_literal lit then lit else negate_literal lit;
*)

val clause_literals = strip_disj o snd o strip_forall;

(* ------------------------------------------------------------------------- *)
(* Operations for accessing literals, which are kept on the assumption list. *)
(* ------------------------------------------------------------------------- *)

val hide_literal = MATCH_MP HIDE_LITERAL THENR UNDISCH;

fun show_literal lit = DISCH (mk_neg lit) THENR MATCH_MP SHOW_LITERAL;

local
  val ROTATE_DISJ = CONV_RULE (REWR_CONV (GSYM DISJ_ASSOC));
  val REMOVE_DISJ = MATCH_MP INITIALIZE_CLAUSE THENR UNDISCH;
  val INIT = REPEATR (REPEATR ROTATE_DISJ THENR REMOVE_DISJ) THENR hide_literal;
in
  fun initialize_lits th =
    if concl th = F then ([], th) else (strip_disj (concl th), INIT th);
end;

local
  fun final_lit lit = DISCH (mk_neg lit) THENR MATCH_MP FINALIZE_CLAUSE;
in
  fun finalize_lits (lits, th) =
    case rev lits of [] => th
    | lit :: rest => foldl (uncurry final_lit) (show_literal lit th) rest;
end;

(* Quick testing
val t1 = initialize_hol_thm (([], []), ASSUME ``p \/ ~q \/ ~r \/ s``);
val t2 = initialize_hol_thm (([], []), ASSUME ``((p \/ ~q) \/ ~r) \/ s``);
try finalize_hol_thm t1;
try finalize_hol_thm t2;
*)

(* ------------------------------------------------------------------------- *)
(* varconsts lump together constants and locally constant variables.         *)
(* ------------------------------------------------------------------------- *)

fun dest_varconst tm =
  case dest_term tm of VAR (s, _) => s
  | CONST {Thy, Name, Ty = _} => mk_const_name (Thy, Name)
  | _ => raise ERR "dest_varconst" (term_to_string tm ^ " is neither");

val is_varconst = can dest_varconst;

fun mk_varconst s =
  all_new_tyvars
  (if is_const_name s then
     let val (t, n) = dest_const_name s
     in prim_mk_const {Thy = t, Name = n}
     end
   else mk_var (s, alpha));

(* ------------------------------------------------------------------------- *)
(* Pretty-printing FOL formulas that have come from HOL.                     *)
(* ------------------------------------------------------------------------- *)

val print_types = ref true;

val type_op_map =
  [("fun", "->"), ("prod", "*"), ("sum", "+")];

val term_op_map =
  [("min.=", "equality"), ("min.==>", "implication"),
   ("bool.T", "truth"), ("bool.F", "falsity"), ("bool.~", "negation"),
   ("bool./\\", "conjunction"), ("bool.\\/", "disjunction"),
   ("bool.?", "existential"), ("bool.!", "universal")];

local
  fun pr_varname v = if is_prime v then "_" ^ dest_prime v else v;
  val pr_op = possibly (fn x => assoc x type_op_map);
in
  fun prettify_type (mlibTerm.Var v)     = mlibTerm.Var (pr_varname v)
    | prettify_type (mlibTerm.Fn (f, a)) = mlibTerm.Fn (pr_op f, map prettify_type a);
end;

local
  val dest = total (dest_prefix "%%genvar%%");
in
  fun prettify_varname s =
    case dest s of SOME s' => "vg" ^ s'
    | NONE => if mlibTerm.var_string s then s else "v_" ^ s;
end;

local
  local val dest = total (dest_prefix "%%genvar%%");
  in fun pr_cname s = case dest s of SOME s' => "gv" ^ s' | NONE => s;
  end;

  fun pr_op s =
    case assoc1 s term_op_map of SOME (_, s') => s'
    | NONE => if is_const_name s then snd (dest_const_name s) else pr_cname s;

  fun Var' v = mlibTerm.Var (prettify_varname v);

  fun Fn' (f, a) =
    mlibTerm.Fn
    (if mlibTerm.var_string f then (if null a then "c_" else "f_") ^ f else f, a);
in
  fun prettify_term (mlibTerm.Var v) = Var' v
    | prettify_term (mlibTerm.Fn (":", [tm, ty])) =
    if !print_types then mlibTerm.Fn (":", [prettify_term tm, prettify_type ty])
    else prettify_term tm
    | prettify_term (mlibTerm.Fn (f, a)) = Fn' (pr_op f, map prettify_term a);
end;

val prettify_formula =
  let
    open mlibTerm
    fun promote (Fn A)  = Atom A
      | promote (Var _) = raise BUG "prettify_formula" "ARGH!"
    fun pr True            = True
      | pr False           = False
      | pr (Atom A)        = promote (prettify_term (Fn A))
      | pr (Not f)         = Not (pr f)
      | pr (And (f, g))    = And (pr f, pr g)
      | pr (Or (f, g))     = Or (pr f, pr g)
      | pr (Imp (f, g))    = Imp (pr f, pr g)
      | pr (Iff (f, g))    = Iff (pr f, pr g)
      | pr (Forall (v, f)) = Forall (prettify_varname v, pr f)
      | pr (Exists (v, f)) = Exists (prettify_varname v, pr f)
  in
    pr
  end;

val pp_term1    = mlibUseful.pp_map prettify_term    mlibTerm.pp_term;
val pp_formula1 = mlibUseful.pp_map prettify_formula mlibTerm.pp_formula;

local
  (* Don't make this visible: theorems deserve better protection *)
  val prettify_thm = (mlibThm.AXIOM o map prettify_formula o mlibThm.clause);
in
  val pp_thm1 = mlibUseful.pp_map prettify_thm mlibThm.pp_thm;
end;

(* ------------------------------------------------------------------------- *)
(* Translate a HOL type to FOL, and back again.                              *)
(* ------------------------------------------------------------------------- *)

fun hol_type_to_fol tyvars =
  let
    fun ty_to_fol hol_ty =
      if is_vartype hol_ty then
        (if mem hol_ty tyvars then mlibTerm.Var else (fn s => mlibTerm.Fn (s, [])))
        (dest_vartype hol_ty)
      else
        let val (f, args) = dest_type hol_ty
        in mlibTerm.Fn (f, map ty_to_fol args)
        end
  in
    ty_to_fol
  end;

fun fol_type_to_hol (mlibTerm.Var v) = fake_new_tyvar (possibly dest_prime v)
  | fol_type_to_hol (mlibTerm.Fn (f, a)) =
  if not (is_prime f) then mk_type (f, map fol_type_to_hol a)
  else (assert (null a) (ERR "fol_type_to_hol" "bad prime"); mk_vartype f);

(* Quick testing
installPP pp_term;
val t = try hol_type_to_fol [alpha] ``:'a list -> bool # (bool + 'b) list``;
try fol_type_to_hol t;
*)

(* ------------------------------------------------------------------------- *)
(* Translate a HOL literal to FOL.                                           *)
(* ------------------------------------------------------------------------- *)

fun hol_term_to_fol (parm : parameters) (tm_vars, ty_vars) =
  let
    val {with_types, higher_order, ...} = parm
    fun tmty_to_fol tm =
      if not with_types then tm_to_fol tm
      else mlibTerm.Fn (":", [tm_to_fol tm, hol_type_to_fol ty_vars (type_of tm)])
    and tm_to_fol tm =
      if mem tm tm_vars then mlibTerm.Var (fst (dest_var tm))
      else if higher_order then
        if is_comb tm then
          let val (a, b) = dest_comb tm
          in mlibTerm.Fn ("%", [tmty_to_fol a, tmty_to_fol b])
          end
        else mlibTerm.Fn (dest_varconst tm, [])
      else
        let
          val (f, args) = strip_comb tm
          val () =
            assert (not (mem f tm_vars))
            (ERR "hol_term_to_fol" "higher-order term")
        in
          mlibTerm.Fn (dest_varconst f, map tmty_to_fol args)
        end
  in
    tmty_to_fol
  end;

fun hol_atom_to_fol parm vs tm =
  if is_eq tm then
    let val (a, b) = dest_eq tm
    in mlibTerm.Atom ("=", [hol_term_to_fol parm vs a, hol_term_to_fol parm vs b])
    end
  else if #higher_order parm then
    mlibTerm.Atom ("B", [hol_term_to_fol parm vs tm])
  else
    let
      val (r, args) = strip_comb tm
      val () =
        assert (not (mem r (fst vs)))
        (ERR "hol_term_to_fol" "higher-order atom")
    in
      mlibTerm.Atom (dest_varconst r, map (hol_term_to_fol parm vs) args)
    end;

fun hol_literal_to_fol parm vars lit =
  if is_neg lit then mlibTerm.Not (hol_atom_to_fol parm vars (dest_neg lit))
  else hol_atom_to_fol parm vars lit;

(* ------------------------------------------------------------------------- *)
(* The HOL -> FOL user interface:                                            *)
(* translation of theorems and lists of literals.                            *)
(* ------------------------------------------------------------------------- *)

fun hol_literals_to_fol parm (vars, lits) =
  map (hol_literal_to_fol parm vars) lits
  handle HOL_ERR _ => raise BUG "hol_literals_to_fol" "shouldn't fail";

fun hol_thm_to_fol parm (vars, th) =
  mlibThm.AXIOM (hol_literals_to_fol parm (vars, fst (initialize_lits th)))
  handle HOL_ERR _ => raise BUG "hol_thm_to_fol" "shouldn't fail";

(* Quick testing
installPP pp_formula;
try hol_literals_to_fol {higher_order = true, with_types = true}
  (([``v_b : 'b``], [``:'a``]),
   [``~P (c_a : 'a, v_b : 'b)``, ``0 <= LENGTH ([] : 'a list)``]);
try hol_literals_to_fol {higher_order = true, with_types = false}
  (([``v_b : 'b``], [``:'a``]),
   [``~P (c_a : 'a, v_b : 'b)``, ``0 <= LENGTH ([] : 'a list)``]);
try hol_literals_to_fol {higher_order = false, with_types = true}
  (([``v_b : 'b``], [``:'a``]),
   [``~P (c_a : 'a, v_b : 'b)``, ``0 <= LENGTH ([] : 'a list)``]);
try hol_literals_to_fol {higher_order = false, with_types = false}
  (([``v_b : 'b``], [``:'a``]),
   [``~P (c_a : 'a, v_b : 'b)``, ``0 <= LENGTH ([] : 'a list)``]);
*)

(* ------------------------------------------------------------------------- *)
(* Operations on terms with floppy type variables.                           *)
(* ------------------------------------------------------------------------- *)

local
  fun sync tyS _    []           = tyS
    | sync tyS vars (tm :: work) =
    (case dest_term tm of VAR  (s, ty) =>
       if not (is_new_var tm) then sync tyS vars work else
         (case assoc1 s vars of NONE => sync tyS ((s, ty) :: vars) work
          | SOME (_, ty') => sync (new_unifyl_type tyS [(ty, ty')]) vars work)
     | COMB  (a, b) => sync tyS vars (a :: b :: work)
     | CONST _      => sync tyS vars work
     | LAMB  _      => raise ERR "sync_vars" "lambda");
in
  fun sync_vars tms = sync [] [] tms;
end;

local
  fun app s (a, b) = new_unifyl_type s [(a, b --> new_tyvar ())];
  fun iapp b (a, s) =
    let val s = app s (a, b) in (snd (dom_rng (type_subst s a)), s) end;
in
  fun prepare_mk_comb (a, b) = app (sync_vars [a, b]) (type_of a, type_of b)
  fun prepare_list_mk_comb (f, a) =
    snd (foldl (uncurry (iapp o type_of)) (type_of f, sync_vars (f :: a)) a);
end;

fun unify_mk_comb (a, b) =
  let val i = inst (prepare_mk_comb (a, b)) in mk_comb (i a, i b) end;

fun unify_list_mk_comb (f, a) =
  let val i = inst (prepare_list_mk_comb (f, a))
  in list_mk_comb (i f, map i a)
  end;

local val eq_tm = prim_mk_const {Thy = "min", Name = "="};
in fun unify_mk_eq (a, b) = unify_list_mk_comb (all_new_tyvars eq_tm, [a, b]);
end;

val freshen_mk_comb      = freshen_tyvars o unify_mk_comb;
val freshen_list_mk_comb = freshen_tyvars o unify_list_mk_comb;

fun cast_to ty tm = inst (new_match_type (type_of tm) ty) tm;

(* Quick testing
val a = mk_varconst "list.LENGTH"; type_of a;
val b = mk_varconst "x";           type_of b;
val c = unify_mk_comb (a, b);      type_of c;
try sync_vars [``LENGTH (x:'b list) <= 0``, ``x:'a``, ``HD x = 3``];
prepare_list_mk_comb (``LENGTH``, [``[3; 4]``]);
try unify_list_mk_comb (``COND``, new_tyvars [``HD x``, ``CONS x``, ``I``]);
*)

(* ------------------------------------------------------------------------- *)
(* Translate a FOL literal to HOL.                                           *)
(* ------------------------------------------------------------------------- *)

fun fol_term_to_hol ({higher_order, with_types = true, ...} : parameters) =
  let
    fun tmty_to_hol (mlibTerm.Fn (":",[tm,ty])) = tm_to_hol (fol_type_to_hol ty) tm
      | tmty_to_hol _ = raise ERR "fol_term_to_hol" "missing type information"
    and tm_to_hol ty (mlibTerm.Var v) = fake_new_var (v, ty)
      | tm_to_hol ty (mlibTerm.Fn (fname, args)) =
      if higher_order then
        case (fname, args) of (_, []) => cast_to ty (mk_varconst fname)
        | ("%", [f, a]) => mk_comb (tmty_to_hol f, tmty_to_hol a)
        | _ => raise ERR "fol_term_to_hol" "(typed) weird higher-order term"
      else
        let
          val hol_args = map tmty_to_hol args
          val f_type   = foldr (fn (h, t) => type_of h --> t) ty hol_args
        in
          list_mk_comb (cast_to f_type (mk_varconst fname), hol_args)
        end
  in
    tmty_to_hol
  end
  | fol_term_to_hol ({higher_order, with_types = false, ...} : parameters) =
  let
    fun tm_to_hol (mlibTerm.Var v) = fake_new_var (v, new_tyvar ())
      | tm_to_hol (mlibTerm.Fn (fname, args)) =
      if higher_order then
        case (fname, args) of (_, []) => mk_varconst fname
        | ("%", [f, a]) => freshen_mk_comb (tm_to_hol f, tm_to_hol a)
        | _ => raise ERR "fol_term_to_hol" "(typeless) weird higher-order term"
      else freshen_list_mk_comb (mk_varconst fname, map tm_to_hol args)
  in
    tm_to_hol
  end;

fun fol_atom_to_hol parm (mlibTerm.Atom ("=", [x, y])) =
  unify_mk_eq (fol_term_to_hol parm x, fol_term_to_hol parm y)
  | fol_atom_to_hol parm (mlibTerm.Atom (r, args)) =
  cast_to bool
  (if #higher_order parm then
     case (r, args) of ("B", [fol_tm]) => fol_term_to_hol parm fol_tm
     | _ => raise ERR "fol_atom_to_hol" "weird higher-order atom"
   else unify_list_mk_comb (mk_varconst r, map (fol_term_to_hol parm) args))
  | fol_atom_to_hol _ _ = raise BUG "fol_atom_to_fol" "not an atom";

fun fol_literal_to_hol _ mlibTerm.True = T
  | fol_literal_to_hol _ mlibTerm.False = F
  | fol_literal_to_hol parm (mlibTerm.Not a) = mk_neg (fol_literal_to_hol parm a)
  | fol_literal_to_hol parm (a as mlibTerm.Atom _) = fol_atom_to_hol parm a
  | fol_literal_to_hol _ _ = raise ERR "fol_literal_to_hol" "not a literal";

(* Quick testing
installPP pp_formula;
val parm = {higher_order = false, with_types = true};
val lits = try hol_literals_to_fol parm
  (([``v_b : 'b``], [``:'b``]),
   [``~P (c_a : 'a list, v_b : 'b)``, ``0 <= LENGTH (c_a : 'a list)``]);
val [lit1, lit2] = lits;
try (fol_literal_to_hol parm) lit1;
try (fol_literal_to_hol parm) lit2;
*)

(* ------------------------------------------------------------------------- *)
(* Translate a FOL theorem to HOL (the tricky bit).                          *)
(* ------------------------------------------------------------------------- *)

type Axioms  = thm1 -> vars * thm;
type Pattern = vars * term list;
type Result  = vars * thm list;

fun proof_step parm prev =
  let
    open mlibTerm mlibMatch mlibThm

    fun freshen (lits, th) =
      if #with_types parm then (lits, th)
      else
        let val sub = fresh_tyvars lits
        in (map (inst sub) lits, INST_TY sub th)
        end

    fun match_lits l l' =
      (if #with_types parm then match_term else new_match_uty)
      (list_mk_disj' l) (list_mk_disj' l')

    fun step (fol_th, Axiom' _) = prev fol_th
      | step (_, Assume' fol_lit) =
      let
        val th = if positive fol_lit then EXCLUDED_MIDDLE else EXCLUDED_MIDDLE'
        val hol_atom = fol_literal_to_hol parm (literal_atom fol_lit)
      in
        initialize_lits (SPEC hol_atom th)
      end
      | step (fol_th, Inst' (_, fol_th1)) =
      let
        val (hol_lits1, hol_th1) = prev fol_th1
        val hol_lits = map (fol_literal_to_hol parm) (clause fol_th)
        val sub = match_lits hol_lits1 hol_lits
      in
        (map (pinst sub) hol_lits1, PINST sub hol_th1)
      end
      | step (_, Factor' fol_th) =
      let
        fun f uns lits [] = (new_unifyl_ty ([], []) uns, rev (map snd lits))
          | f uns lits ((fl, hl) :: rest) =
          case List.find (equal fl o fst) lits of NONE
            => f uns ((fl, hl) :: lits) rest
          | SOME (_, hl') => f ((hl, hl') :: uns) lits rest
        val (hol_lits, hol_th) = prev fol_th
        val (sub, hol_lits') = f [] [] (zip (clause fol_th) hol_lits)
      in
        (map (pinst sub) hol_lits', PINST sub hol_th)
      end
      | step (_, Resolve' (fol_lit, fol_th1, fol_th2)) =
      let
        fun res0 fth fl =
          let
            val (hls, hth) = prev fth
            val (a, b) = partition (equal fl o fst) (zip (mlibThm.clause fth) hls)
          in
            ((map snd a, map snd b), hth)
          end
        val negate_lit = if positive fol_lit then mk_neg else dest_neg
        val negate_lit' = if positive fol_lit then dest_neg else mk_neg
        val hol_lit = fol_literal_to_hol parm fol_lit
        val ((hol_ms1, hol_lits1), hol_th1) = res0 fol_th1 fol_lit
        val ((hol_ms2, hol_lits2), hol_th2) = res0 fol_th2 (negate fol_lit)
(*
        val () = chat ("resolve: hol_lits1 =\n" ^ terms_to_string hol_lits1)
        val () = chat ("resolve: hol_lits2 =\n" ^ terms_to_string hol_lits2)
        val () = chat ("resolve: hol_ms1 =\n" ^ terms_to_string hol_ms1)
        val () = chat ("resolve: hol_ms2 =\n" ^ terms_to_string hol_ms2)
*)
        val sub = new_unify_ty (hol_lit :: hol_ms1 @ map negate_lit' hol_ms2)
        val hol_lit' = pinst sub hol_lit
        val hol_th1' = show_literal hol_lit'              (PINST sub hol_th1)
        val hol_th2' = show_literal (negate_lit hol_lit') (PINST sub hol_th2)
      in
        (map (pinst sub) (hol_lits1 @ hol_lits2),
         MATCH_MP RESOLUTION
         (if positive fol_lit then CONJ hol_th1' hol_th2'
          else CONJ hol_th2' hol_th1'))
      end
      | step _ = raise BUG "fol_thm_to_hol" "weird proof step";
  in
    fn p =>
    freshen (step p)
  end;

local
  val initialize_axiom =
    initialize_lits o snd o gen_alpha (change_vars to_fake_new) PINST;

  fun previous a l x =
    case assoc1 x l of SOME (_, y) => y | NONE => initialize_axiom (a x);

  fun chat_proof_step parm prev (p as (fol_th, inf)) =
    let
      val () = chat
        ("_____________________________________________________\n" ^
         "\nfol: " ^ mlibThm.thm_to_string fol_th ^ "\n" ^
         "\ninf: " ^ mlibThm.inference_to_string inf ^ "\n")
      val res = proof_step parm prev p
      val () = chat
        ("\nhol: " ^ thm_to_string (finalize_lits res) ^ "\n")
    in
      res
    end;

  fun translate parm prev =
    let
      fun f p []       = finalize_lits (snd (hd p))
        | f p (x :: l) = f ((fst x, chat_proof_step parm (prev p) x) :: p) l
    in                              (****)
      f
    end;

  fun match_pattern pattern ths =
    let
      val pattern  = gen_alpha (change_vars to_new) (map o pinst) pattern
      val pattern  = list_mk_conj' (snd pattern)
      val ths_foot = list_mk_conj' (map concl ths)
    in
      map (PINST (new_match_uty pattern ths_foot)) ths
    end;

  val finalize_thms =
    gen_alpha (change_vars to_gen) (map o PINST) o
    new_free_vars (list_mk_conj' o map concl);
in
  fun fol_thms_to_hol parm axioms pattern ths =
    (finalize_thms o match_pattern pattern o
     map (translate parm (previous axioms) [] o rev o mlibThm.proof)) ths
    handle HOL_ERR _ => raise ERR "fol_thms_to_hol" "proof translation error";
end;

(* Quick testing
load "normalForms";
open normalForms;
installPP pp_term;
installPP pp_formula;
installPP pp_thm;
show_assums := true;
*)

end
