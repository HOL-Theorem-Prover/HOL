(* ========================================================================= *)
(* MAPPING BETWEEN HOL AND FIRST-ORDER LOGIC.                                *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

(*
loadPath := "../mlib" :: "../normalize" :: !loadPath;
app load
["tautLib", "mlibUseful", "mlibTerm", "mlibMatch", "mlibThm", "matchTools"];
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
val pinst      = matchTools.pinst;
val INST_TY    = matchTools.INST_TY;
val PINST      = matchTools.PINST;

(* ------------------------------------------------------------------------- *)
(* Chatting and error handling.                                              *)
(* ------------------------------------------------------------------------- *)

local
  open mlibUseful;
  val module = "folMapping";
in
  val () = traces := {module = module, alignment = I} :: !traces;
  fun chatting l = tracing {module = module, level = l};
  fun chat s = (trace s; true)
  val ERR = mk_HOL_ERR module;
  fun BUG f m = Bug (f ^ ": " ^ m);
end;

(* ------------------------------------------------------------------------- *)
(* Mapping parameters.                                                       *)
(* ------------------------------------------------------------------------- *)

type parameters =
  {higher_order : bool,       (* Application is a first-order function *)
   with_types   : bool};      (* First-order terms include HOL type info *)

val defaults =
  {higher_order = false,
   with_types   = false};

fun update_higher_order f (parm : parameters) : parameters =
  let val {higher_order, with_types} = parm
  in {higher_order = f higher_order, with_types = with_types}
  end;

fun update_with_types f (parm : parameters) : parameters =
  let val {higher_order, with_types} = parm
  in {higher_order = higher_order, with_types = f with_types}
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun uncurry3 f (x, y, z) = f x y z;

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

fun remove_type (mlibTerm.Fn (":", [tm, _])) = tm | remove_type tm = tm;

(* ------------------------------------------------------------------------- *)
(* "new" variables can be instantiated; everything else is a local constant. *)
(* ------------------------------------------------------------------------- *)

val FOL_PREFIX = "XXfolXX";

local
  val tag        = mk_prefix FOL_PREFIX;
  val untag      = dest_prefix FOL_PREFIX;
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

val to_gen      = (genvar       o type_of,  (fn _ : hol_type => gen_tyvar ()));
val to_new      = (new_var      o type_of,  (fn _ : hol_type => new_tyvar ()));
val to_fake_new = (fake_new_var o dest_var,
                   fake_new_tyvar o dest_prime o dest_vartype);

fun new_free_vars x = gen_vfree_vars (is_new_var, is_new_tyvar) x;

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

val EQUAL_STEP = prove
  (``!a b c. ((a ==> (b = c)) /\ b) ==> ~a \/ c``,
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

(*
local
  fun atom ({higher_order, with_types} : parameters) p
fun lit_subterm parm p lit =
  if is_neg lit then (mk_neg o cast_to
  let
    val
*)

(* ------------------------------------------------------------------------- *)
(* Operations for accessing literals, which are kept on the assumption list. *)
(* ------------------------------------------------------------------------- *)

fun hide_literal th = UNDISCH (MP (SPEC (concl th) HIDE_LITERAL) th);

fun show_literal lit =
  let val lit' = mk_neg lit
  in DISCH lit' THENR MP (SPEC lit SHOW_LITERAL)
  end;

local
  fun REMOVE_DISJ th =
    let val (a,b) = dest_disj (concl th)
    in UNDISCH (MP (SPECL [a,b] INITIALIZE_CLAUSE) th)
    end;

  val INIT =
    CONV_RULE (REPEATC (REWR_CONV (GSYM DISJ_ASSOC)))
    THENR REPEATR REMOVE_DISJ
    THENR hide_literal;
in
  fun initialize_lits th =
    if aconv (concl th) F then ([], th) else (strip_disj (concl th), INIT th);
end;

local
  fun final_lit lit =
    let val lit' = mk_neg lit
    in fn th => MP (SPECL [lit, concl th] FINALIZE_CLAUSE) (DISCH lit' th)
    end;
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
(* Prettify FOL representations of HOL terms---WILL BREAK PROOF TRANSLATION! *)
(* ------------------------------------------------------------------------- *)

val prettify_fol = ref false;

val type_op_map =
  [("fun", "->"), ("prod", "*"), ("sum", "+")];

val term_op_map =
  [("min.=", "equality"), ("min.==>", "implication"),
   ("bool.T", "truth"), ("bool.F", "falsity"), ("bool.~", "negation"),
   ("bool./\\", "conjunction"), ("bool.\\/", "disjunction"),
   ("bool.?", "existential"), ("bool.!", "universal"),
   ("arithmetic.NUMERAL", "NUMERAL"), ("arithmetic.NUMERAL_BIT1", "BIT1"),
   ("arithmetic.NUMERAL_BIT2", "BIT2"), ("arithmetic.ALT_ZERO", "ZERO")];

local
  val pr_op = possibly (fn x => assoc x type_op_map);
  fun Var' v = mlibTerm.Var (if is_prime v then "_" ^ dest_prime v else v);
  fun Fn' (f, a) = mlibTerm.Fn (f, a);
in
  fun prettify_type (mlibTerm.Var v)     = Var' v
    | prettify_type (mlibTerm.Fn (f, a)) = Fn' (pr_op f, map prettify_type a);
end;

local
  val dest = total (dest_prefix "%%genvar%%");
in
  fun prettify_varname s =
    case dest s of SOME s' => "vg" ^ s'
    | NONE => if !mlibTerm.var_string s then s else "v_" ^ s;
end;

local
  local val dest = total (dest_prefix "%%genvar%%");
  in fun pr_cname s = case dest s of SOME s' => "gv" ^ s' | NONE => s;
  end;

  fun pr_op s =
    case assoc1 s term_op_map of SOME (_, s') => s'
    | NONE => if is_const_name s then snd (dest_const_name s) else pr_cname s;

  fun pr_fn s p a = (pr_op s, p a);

  fun Var' v = mlibTerm.Var (prettify_varname v);
  fun Fn' (f, a) = mlibTerm.Fn (f, a);
in
  fun prettify_term (mlibTerm.Var v) = Var' v
    | prettify_term (mlibTerm.Fn (":", [tm, ty])) =
    mlibTerm.Fn (":", [prettify_term tm, prettify_type ty])
    | prettify_term (mlibTerm.Fn (f, a)) = Fn' (pr_fn f (map prettify_term) a);
end;

val prettify_formula =
  let
    open mlibTerm
    fun pr True            = True
      | pr False           = False
      | pr (Atom tm)       = Atom (prettify_term tm)
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

(*
val pp_term1    = mlibUseful.pp_map prettify_term    mlibTerm.pp_term;
val pp_formula1 = mlibUseful.pp_map prettify_formula mlibTerm.pp_formula;

local
  (* Don't make this visible: theorems deserve better protection *)
  val prettify_thm = (mlibThm.AXIOM o map prettify_formula o mlibThm.clause);
in
  val pp_thm1 = mlibUseful.pp_map prettify_thm mlibThm.pp_thm;
end;
*)

(* ------------------------------------------------------------------------- *)
(* Translate a HOL type to FOL, and back again.                              *)
(* ------------------------------------------------------------------------- *)

local
  fun dest_type ty =
    let
      val {Args, Thy, Tyop} = dest_thy_type ty
    in
      (Thy ^ "$" ^ Tyop, Args)
    end
  fun mk_type (nm, args) =
    let
      val (ss1, ss2) = Substring.position "$" (Substring.full nm)
      val thy = Substring.string ss1
      val nm = Substring.slice(ss2, 1, NONE) |> Substring.string
    in
      mk_thy_type {Tyop = nm, Thy = thy, Args = args}
    end
in

fun hol_type_to_fol tyV =
  let
    fun ty_to_fol hol_ty =
      if is_vartype hol_ty then
        (if mem hol_ty tyV then mlibTerm.Var else (fn s => mlibTerm.Fn (s, [])))
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
end (* local *)

val fol_bool = hol_type_to_fol [] bool;

(* Quick testing
installPP pp_term;
val t = try hol_type_to_fol [alpha] ``:'a list -> bool # (bool + 'b) list``;
try fol_type_to_hol t;
*)

(* ------------------------------------------------------------------------- *)
(* Translate a HOL literal to FOL.                                           *)
(* ------------------------------------------------------------------------- *)

fun hol_term_to_fol (parm : parameters) (tmV, tyV) =
  let
    val {with_types, higher_order, ...} = parm
    fun tmty2fol tm =
      if not with_types then tm2fol tm
      else mlibTerm.Fn (":", [tm2fol tm, hol_type_to_fol tyV (type_of tm)])
    and tm2fol tm =
      if op_mem aconv tm tmV then mlibTerm.Var (fst (dest_var tm))
      else if higher_order then
        if is_comb tm then
          let val (a, b) = dest_comb tm
          in mlibTerm.Fn ("%", [tmty2fol a, tmty2fol b])
          end
        else mlibTerm.Fn (dest_varconst tm, [])
      else
        let
          val (f, args) = strip_comb tm
          val () = assert (not (op_mem aconv f tmV))
                          (ERR "hol_term_to_fol" "ho term")
        in
          mlibTerm.Fn (dest_varconst f, map tmty2fol args)
        end
  in
    fn tm => (if !prettify_fol then prettify_term else I) (tmty2fol tm)
  end;

fun hol_atom_to_fol parm vs tm =
  mlibTerm.Atom
  (if is_eq tm then
     let val (a, b) = dest_eq tm
     in mlibTerm.Fn ("=", map (hol_term_to_fol parm vs) [a, b])
     end
   else if #higher_order parm then mlibTerm.Fn ("$", [hol_term_to_fol parm vs tm])
   else remove_type (hol_term_to_fol parm vs tm));

fun hol_literal_to_fol parm vars lit =
  if is_neg lit then mlibTerm.Not (hol_atom_to_fol parm vars (dest_neg lit))
  else hol_atom_to_fol parm vars lit;

(* ------------------------------------------------------------------------- *)
(* The HOL -> FOL user interface:                                            *)
(* translation of theorems and lists of literals.                            *)
(* ------------------------------------------------------------------------- *)

fun hol_literals_to_fol parm (vars, lits) =
  map (hol_literal_to_fol parm vars) lits;

fun hol_thm_to_fol parm (vars, th) =
  mlibThm.AXIOM (hol_literals_to_fol parm (vars, fst (initialize_lits th)));

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
(* Translate a FOL literal to HOL.                                           *)
(* ------------------------------------------------------------------------- *)

fun fol_term_to_hol' ({higher_order, with_types = true, ...} : parameters) =
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
  | fol_term_to_hol' ({higher_order, with_types = false, ...} : parameters) =
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

fun fol_term_to_hol parm fol_tm =
  if not (chatting 1) then fol_term_to_hol' parm fol_tm else
    let
      fun cmp (mlibTerm.Var v) (mlibTerm.Var w) =
        possibly dest_prime v = dest_prefix FOL_PREFIX (possibly dest_prime w)
        | cmp (mlibTerm.Fn (f, a)) (mlibTerm.Fn (g, b)) =
        f = g andalso length a = length b andalso
        List.all (uncurry cmp) (zip a b)
        | cmp _ _ = false
      val hol_tm = fol_term_to_hol' parm fol_tm
      val fol_tm' = uncurry (hol_term_to_fol parm) (new_free_vars I hol_tm)
      val () = assert (cmp fol_tm fol_tm')
        (BUG "fol_term_to_hol"
         ("not inverse:\n\noriginal fol =\n" ^ mlibTerm.term_to_string fol_tm ^
          "\n\nhol =\n" ^ term_to_string hol_tm ^
          "\n\nnew fol =\n" ^ mlibTerm.term_to_string fol_tm'))
    in
      hol_tm
    end;

fun fol_atom_to_hol parm (mlibTerm.Atom (mlibTerm.Fn ("=", [x, y]))) =
  unify_mk_eq (fol_term_to_hol parm x, fol_term_to_hol parm y)
  | fol_atom_to_hol parm fm =
  (cast_to bool o fol_term_to_hol parm)
  let
    val {higher_order, with_types} = parm
  in
    case (higher_order, with_types, fm) of
      (true,  _,     mlibTerm.Atom (mlibTerm.Fn ("$", [tm]))) => tm
    | (false, true,  mlibTerm.Atom tm) => mlibTerm.Fn (":", [tm, fol_bool])
    | (false, false, mlibTerm.Atom tm) => tm
    | _ => raise BUG "fol_atom_to_fol" "malformed atom"
  end;

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
(* Translate FOL paths to HOL.                                               *)
(* ------------------------------------------------------------------------- *)

local
  fun zeroes l [] = rev l
    | zeroes l (0 :: h :: t) = zeroes (h :: l) t
    | zeroes _ _ = raise BUG "fol_path_to_hol" "couldn't strip zeroes";

  fun hp r tm [] = (r, tm)
    | hp r tm (0 :: p) = hp (r o RATOR_CONV) (rator tm) p
    | hp r tm (1 :: p) = hp (r o RAND_CONV) (rand tm) p
    | hp _ _ _ = raise BUG "fol_path_to_hol" "bad higher-order path";

  fun fp r tm [] = (r, tm)
    | fp r tm (n :: p) =
    let
      val (_, l) = strip_comb tm
      val m = (length l - 1) - n
      val r = r o funpow m RATOR_CONV o RAND_CONV
      val tm = rand (funpow m rator tm)
    in
      fp r tm p
    end;

  fun ap {higher_order, with_types} (r, tm) p =
    uncurry3 (if higher_order then hp else fp)
    ((fn (r', tm', p') => (r', tm', if with_types then zeroes [] p' else p'))
     (if is_eq tm then
        (case p of 0 :: p => (r o LAND_CONV, lhs tm, p)
         | 1 :: p => (r o RAND_CONV, rhs tm, p)
         | _ => raise BUG "fol_path_to_hol" "bad eq path")
      else
        (r, tm,
         (if higher_order then
            (case p of 0 :: p => p
             | _ => raise BUG "fol_path_to_hol" "bad higher-order path")
          else if with_types then 0 :: p
          else p))));
in
  fun fol_path_to_hol parm p tm =
    ap parm (if is_neg tm then (RAND_CONV, dest_neg tm) else (I, tm)) p;
end;

(* Quick testing
val parm = {higher_order = false, with_types = true};
mlibUseful.try (fol_path_to_hol parm) [0, 0, 1] ``~p a b c``;
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
      | step (_, Resolve' (False, fol_th1, fol_th2)) =
      let
        val (hol_lits1, hol_th1) = prev fol_th1
        val (hol_lits2, _)       = prev fol_th2
      in
        (hol_lits1 @ hol_lits2, hol_th1)
      end
      | step (_, Resolve' (fol_lit, fol_th1, fol_th2)) =
      let
        fun res0 fth fl =
          let
            val (hls, hth) = prev fth
            val (a, b) = partition (equal fl o fst) (zip (clause fth) hls)
          in
            ((map snd a, map snd b), hth)
          end
        val (negate_lit, negate_lit') =
          if positive fol_lit then (boolSyntax.mk_neg, boolSyntax.dest_neg)
          else (boolSyntax.dest_neg, boolSyntax.mk_neg)
        val hol_lit = fol_literal_to_hol parm fol_lit
        val ((hol_ms1, hol_lits1), hol_th1) = res0 fol_th1 fol_lit
        val ((hol_ms2, hol_lits2), hol_th2) = res0 fol_th2 (negate fol_lit)
        val _ = chatting 2 andalso chat
          ("resolve: hol_lits1 =\n" ^ terms_to_string hol_lits1 ^
           "resolve: hol_lits2 =\n" ^ terms_to_string hol_lits2 ^
           "resolve: hol_ms1 =\n" ^ terms_to_string hol_ms1 ^
           "resolve: hol_ms2 =\n" ^ terms_to_string hol_ms2)
        val sub = new_unify_ty (hol_lit :: hol_ms1 @ map negate_lit' hol_ms2)
        val hol_lit'  = pinst sub hol_lit
        val hol_nlit' = negate_lit hol_lit'
        val hol_th1'  = show_literal hol_lit'  (PINST sub hol_th1)
        val hol_th2'  = show_literal hol_nlit' (PINST sub hol_th2)
      in
        (map (pinst sub) (hol_lits1 @ hol_lits2),
         if positive fol_lit then
           MP (SPEC hol_lit' RESOLUTION) (CONJ hol_th1' hol_th2')
         else
           MP (SPEC hol_nlit' RESOLUTION) (CONJ hol_th2' hol_th1'))
      end
      | step (_, Refl' fol_tm) =
      initialize_lits (Thm.REFL (fol_term_to_hol parm fol_tm))
      | step (_, Equality' (fol_lit, fol_p, fol_r, lr, fol_th)) =
      let
        val (hol_lits, hol_th) = prev fol_th
        val n = mlibUseful.index (equal fol_lit) (clause fol_th)
        val hol_lit =
          case n of NONE => fol_literal_to_hol parm fol_lit
          | SOME n => List.nth (hol_lits, n)
        val hol_r = fol_term_to_hol parm fol_r
        val sub = sync_vars [hol_lit, hol_r]
        val hol_lits = map (inst sub) hol_lits
        val hol_th = INST_TY sub hol_th
        val hol_lit = inst sub hol_lit
        val hol_r = inst sub hol_r
        val (PATH, hol_l) = fol_path_to_hol parm fol_p hol_lit
        val sub = (new_unify_type o map type_of) [hol_l, hol_r]
        val hol_lits = map (inst sub) hol_lits
        val hol_th = INST_TY sub hol_th
        val hol_lit = inst sub hol_lit
        val hol_r = inst sub hol_r
        val hol_l = inst sub hol_l
        val eq = boolSyntax.mk_eq (if lr then (hol_l,hol_r) else (hol_r,hol_l))
        val hol_eq_th = (if lr then I else Thm.SYM) (Thm.ASSUME eq)
        val hol_lit_th = (PATH (K hol_eq_th)) hol_lit
        val hol_lit' = (boolSyntax.rhs o concl) hol_lit_th
        val hol_lits' =
          mk_neg eq ::
          (case n of NONE => hol_lit' :: hol_lits
           | SOME n => mlibUseful.update_nth (K hol_lit') n hol_lits)
        val hol_lem = CONJ (DISCH eq hol_lit_th) (show_literal hol_lit hol_th)
        val equal_step = SPECL [eq, hol_lit, hol_lit'] EQUAL_STEP
      in
        (hol_lits', snd (initialize_lits (MP equal_step hol_lem)))
      end;
  in
    fn p => freshen (step p)
  end;

local
  val initialize_axiom =
    initialize_lits o snd o gen_alpha (change_vars to_fake_new) PINST;

  fun previous a l x =
    case assoc1 x l of SOME (_, y) => y | NONE => initialize_axiom (a x);

  fun chat_proof th =
    if not (chatting 1) then mlibThm.proof th else
      let
        val res = mlibThm.proof th
        val _ = chat ("\n\nProof:\n" ^ mlibThm.proof_to_string res ^ "\n\n")
      in
        res
      end;

  fun chat_proof_step parm prev (p as (fol_th, inf)) =
    if not (chatting 1) then proof_step parm prev p else
      let
        val _ = chat
          ("_____________________________________________________\n" ^
           "\nfol: " ^ mlibThm.thm_to_string fol_th ^ "\n" ^
           "\ninf: " ^ mlibThm.inference_to_string inf ^ "\n")
        val res = proof_step parm prev p
        val _ = chat ("\nhol: " ^ thm_to_string (finalize_lits res) ^ "\n")
      in
        res
      end;

  fun translate parm prev =
    let
      fun f p []       = finalize_lits (snd (hd p))
        | f p (x :: l) = f ((fst x, chat_proof_step parm (prev p) x) :: p) l
    in
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
     map (translate parm (previous axioms) [] o chat_proof)) ths
    handle HOL_ERR _ => raise ERR "fol_thms_to_hol" "proof translation error";
end;

end
