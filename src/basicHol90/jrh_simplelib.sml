local
  open HolKernel Type_def_support Rewrite Conv Drule Thm Parse
  infix |-> THEN THENC
in

val GEN_REWRITE_RULE = fn c => fn thl => GEN_REWRITE_RULE c empty_rewrites thl
val GEN_REWRITE_CONV = fn c => fn thl => GEN_REWRITE_CONV c empty_rewrites thl
val GEN_REWRITE_TAC = fn c => fn thl => GEN_REWRITE_TAC c empty_rewrites thl
val LAND_CONV = RATOR_CONV o RAND_CONV;

val lhand = rand o rator
fun repeat f x = let
  val y = f x
in
  repeat f y
end handle HOL_ERR _ => x

fun rev_assoc x l = fst(valOf (List.find (fn p => snd p = x) l))
  handle Option.Option => raise HOL_ERR {origin_function = "rev_assoc",
                                         origin_structure = "jrh_simplelib",
                                         message = "Not found"}




fun SUBS_CONV ths tm =
  if null ths then REFL tm
  else let
    val lefts = map (lhand o concl) ths
    val gvs = map (genvar o type_of) lefts
    val pat = Term.subst (map2 (curry op|->) lefts gvs) tm
    val abs = list_mk_abs(gvs,pat)
    val th =
      rev_itlist
      (fn y => fn x => CONV_RULE (RAND_CONV BETA_CONV THENC
                                  (RATOR_CONV o RAND_CONV) BETA_CONV)
       (MK_COMB(x,y))) ths (REFL abs)
  in
    if rand(concl th) = tm then REFL tm
    else th
  end

(* ------------------------------------------------------------------------- *)
(* Useful function to create stylized arguments using numbers.               *)
(* ------------------------------------------------------------------------- *)

(* from HOL Light's basics.ml *)

val make_args = let
  fun margs n s avoid tys =
    if tys = [] then []
    else let
      val v = variant avoid (mk_var{Name = s^(Int.toString n), Ty = hd tys})
    in
      v::(margs (n + 1) s (v::avoid) (tl tys))
    end
in
  fn s => fn avoid => fn tys =>
    if length tys = 1 then
      [variant avoid (mk_var{Name = s, Ty = hd tys})]
    else
      margs 0 s avoid tys
end


val conjuncts = strip_conj

fun SIMPLE_EXISTS v th = EXISTS (mk_exists{Bvar = v, Body = concl th},v) th;
fun SIMPLE_CHOOSE v th =
  CHOOSE(v,ASSUME (mk_exists{Bvar = v, Body = hd(hyp th)})) th;


val RIGHT_BETAS =
  rev_itlist (fn a => CONV_RULE (RAND_CONV BETA_CONV) o C AP_THM a);


fun F_F (f, g) (x,y) = (f x, g y)
fun mk_fun_ty dom rng = Type.-->(dom,rng)


fun new_basic_type_definition tyname (mkname, destname) thm = let
  val {Rator = pred, Rand = witness} = dest_comb(concl thm)
  val predty = type_of pred
  val dom_ty = #1 (dom_rng predty)
  val x = mk_var{Name = "x", Ty = dom_ty}
  val witness_exists =
    EXISTS (mk_exists{Bvar = x, Body = mk_comb{Rator = pred, Rand = x}},
            witness) thm
  val tyax = new_type_definition{name = tyname, pred = pred,
                                 inhab_thm = witness_exists}
  val (mk_dest, dest_mk) =
    CONJ_PAIR
    (define_new_type_bijections {name = (tyname^"_repfns"), ABS = mkname,
                                 REP = destname, tyax = tyax})
in
  (SPEC_ALL mk_dest, SPEC_ALL dest_mk)
end

fun chop_list n l =
  if n = 0 then ([], l)
  else let
    val (m,l') = chop_list (n - 1) (tl l)
  in
    (hd l :: m, l')
  end handle List.Empty => raise HOL_ERR {origin_function = "chop_list",
                                          origin_structure = "jrh_simplelib",
                                          message = "List too short"}


fun Union l = itlist union l [];

fun mk_binop op_t tm1 tm2 = list_mk_comb(op_t, [tm1, tm2])
fun mk_const (n, theta) = let
  val c = #const (const_decl n)
  val ty = type_of c
in
  Term.mk_const{Name = n, Ty = Type.type_subst theta ty}
end

(* ------------------------------------------------------------------------- *)
(* Like mk_comb, but instantiates type variables in rator if necessary.      *)
(* ------------------------------------------------------------------------- *)

fun mk_icomb(tm1,tm2) = let
  val (ty, _) = Type.dom_rng (type_of tm1)
  val tyins = Type.match_type ty (type_of tm2)
in
  mk_comb{Rator = Term.inst tyins tm1, Rand = tm2}
end

(* ------------------------------------------------------------------------- *)
(* Instantiates types for constant c and iteratively makes combination.      *)
(* ------------------------------------------------------------------------- *)

fun list_mk_icomb cname = let
  val cnst = mk_const(cname,[])
in
  fn args => rev_itlist (C (curry mk_icomb)) args cnst
end

(* ------------------------------------------------------------------------- *)
(* Gets all variables (free and/or bound) in a term.                         *)
(* ------------------------------------------------------------------------- *)

(* from ind-defs.ml *)

val variables = let
  fun vars(acc,tm) =
    if is_var tm then insert tm acc
    else if is_const tm then acc
    else if is_abs tm then let
      val {Bvar = v, Body = bod} = dest_abs tm
    in
      vars(insert v acc,bod)
    end
    else let
      val {Rator = l, Rand = r} = dest_comb tm
    in
      vars(vars(acc,l),r)
    end
in
  fn tm => vars([],tm)
end

(* from lib.ml *)
fun striplist dest = let
  fun strip x acc = let
    val (l,r) = dest x
  in
    strip l (strip r acc)
  end handle HOL_ERR _ => x::acc
in
  fn x => strip x []
end



end