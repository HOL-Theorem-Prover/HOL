structure NDatatype :> NDatatype =
struct

open NDDB Witness;
open lcsymtacs;
open combinSyntax;
open ParseDatatype;
open oneSyntax;
open combinSyntax;

val ERR = Feedback.mk_HOL_ERR "MyDatatype";

(*****************************************************************)

fun gen_tyvar _ = Type.gen_tyvar ();

(* get type variables in a pretype *)
fun pty_get_tyvars pty =
    case pty of
      dAQ _             => [ ]
    | dVartype s        => [s]
    | dTyop {Args, ...} => Lib.U (map pty_get_tyvars Args);

(* fromType : hol_type -> ParseDatatype.pretype *)
fun fromType ty =
  if is_vartype ty
  then dVartype (dest_vartype ty)
  else let val {Args, Thy, Tyop} = dest_thy_type ty
           val thy = if Thy = "" then NONE else SOME Thy
       in dTyop {Args=(map fromType Args), Thy=thy, Tyop=Tyop}
       end;

(* interleave two lists *)
fun interleave [] y = y
  | interleave x [] = x
  | interleave (x::xs) (y::ys) = x::y::(interleave xs ys);

(* functions to access dictionaries *)
fun lookup tyvar (tyvar'::tyvars, h::dict) =
    if tyvar = tyvar' then SOME h
    else lookup tyvar (tyvars, dict)
  | lookup _ _ = NONE;
fun insert (tyvar, value) ([], []) = ([tyvar], [value])
  | insert (tyvar, value) (tyvar'::tyvars, h::dict) =
    if tyvar = tyvar' then (tyvar::tyvars, value::dict)
    else let
      val (x, y) = (insert (tyvar,value) (tyvars, dict))
      in (tyvar'::x, h::y) end;

(* Constructs a 0-ary type, caring for the theory *)
fun make_type tyop  NONE      = mk_type(tyop, [])
  | make_type tyop (SOME thy) =
       mk_thy_type {Thy =thy, Tyop=tyop, Args=[]};

(* Replaces occurrences of defining types with type variables *)
fun fix_mutual_vars dict pty =
    case pty of
      dTyop {Args=[], Thy=NONE, Tyop} => (
        case lookup Tyop dict of
          SOME v => dVartype (dest_vartype v)
        | NONE => dTyop {Args=[], Thy=NONE, Tyop=Tyop}
      )
    | dTyop {Args, Thy, Tyop} => dTyop {
        Args = map (fix_mutual_vars dict) Args,
        Thy = Thy, Tyop = Tyop }
    | _ => pty;

(* Generates a new rich type variable *)
fun gen_rich_tyvar tyvar ret (map, map') (all, all') = {
  inj_pair = ASSUME(list_mk_icomb(inj_pair_tm, [map, ret])),
  ret_map  = REFL (combinSyntax.mk_o(ret, map')),
  all_tm = all,
  all_thm  = REFL (mk_comb(all, mk_var("x", tyvar))),
  all_map = REFL (combinSyntax.mk_o(all, map')),
  all_T = REFL all,
  all_mono = ASSUME (list_mk_icomb(pred_setSyntax.subset_tm, [all, all']))
}: rich_type;

(* Generates richness for a constant type *)
fun gen_rich_const ty self = let
    val func = INST_TYPE[alpha|->ty, beta|->self]
  in {
  inj_pair = func (#inj_pair  constantly_rich),
  ret_map  = func (#ret_map   constantly_rich),
  all_tm   = #all_tm    constantly_rich,
  all_thm  = func (#all_thm   constantly_rich),
  all_map  = func (#all_map   constantly_rich),
  all_T    = func (#all_T     constantly_rich),
  all_mono = func (#all_mono  constantly_rich)
}: rich_type
end;

(* A version of list_mk_icomb for theorems *)
local
   val mk_aty = list_mk_rbinop (Lib.curry Type.-->)
   val args = fst o strip_fun o Term.type_of o lhs o concl
   val LIST_MK_COMB = List.foldl (MK_COMB o swap)
in
fun LIST_MK_ICOMB fth aths =
  let
    val tyl = mk_aty (List.take (args fth, List.length aths))
    and tyr = mk_aty (List.map (Term.type_of o lhs o concl) aths)
  in
  LIST_MK_COMB (INST_TYPE (Type.match_type tyl tyr) fth) aths
  end
end;

(* Makes generalizes nesting of type constructors *)
fun nest_tyop tyop [] =
      dTyop {Args=[], Thy=SOME"one", Tyop="one"}
  | nest_tyop tyop (C::[]) = C
  | nest_tyop tyop (C::Cs) = let
      val args = [C, nest_tyop tyop Cs]
      in dTyop {Args=args, Thy=NONE, Tyop=tyop}
      end;

(* Moltiplies and sums the components of a type description
   to get just one constructor *)
fun type_descriptions ([]: ParseDatatype.AST list) = []
  | type_descriptions ((_, ParseDatatype.Constructors clist)::tl)
    = (nest_tyop "sum"
          (map ((nest_tyop "prod") o snd) clist)
       )::(type_descriptions tl)
  | type_descriptions ((_, ParseDatatype.Record _)::_)
    = raise ERR "MyDatatype"
               ("Cannot handle records for now.");

(********************* Composition Functions *********************)

(* These functions combine the theorem of the current type op
   with theorems of the parameter types to get theorems for the
   composed type *)
local
fun compose_inj_pair thm thms =
    foldl ((uncurry o C) MATCH_MP) thm thms;
fun compose_ret_map thm thms =
  let val retrieve_tm = ( fst  o strip_comb o snd  o dest_eq
                        o snd  o strip_forall o concl) thm
  in SYM (RIGHT_CONV_RULE ((REWR_CONV o DEEP_SYM) thm)
     (SYM (LIST_MK_ICOMB (REFL retrieve_tm) thms )))
end;
fun compose_all_tm tm tms = list_mk_icomb(tm, tms);
fun compose_all_mono thm thms =
    if List.length thms = 1 then MATCH_MP thm (hd thms)
    else if List.length thms = 2 then MATCH_MP thm
                          ((uncurry CONJ) (pair_of_list(thms)))
    else MATCH_MP thm (foldl (uncurry CONJ) (hd (rev thms)) (tl (rev thms)));
in
val compose_funs = {
    inj_pair = compose_inj_pair     ,
    ret_map  = compose_ret_map      ,
    all_tm   = compose_all_tm       ,
    all_thm  = (fn x=> fn y=> TRUTH), (* fixme *)
    all_map  = compose_ret_map      ,
    all_T    = (fn x=> fn y=> TRUTH), (* fixme *)
    all_mono = compose_all_mono
}
end;

(**** Main composition function! The magic occurs down here! *****)
fun compose dict self pty =
    case pty of
      dAQ ty     => gen_rich_const ty self
    | dVartype s => valOf (lookup s dict)
    | dTyop {Args, Thy, Tyop} =>
        case lookup Tyop (!types) of
          NONE => if Args = [] then
                    compose dict self (dAQ (pretypeToType pty))
                  else raise ERR "compose"
                    ("Type '"^Tyop^"' not supported.")
        | SOME this => let
           val args = map (compose dict self) Args
           in {
               inj_pair = (#inj_pair compose_funs)
                          (#inj_pair this)
                      (map #inj_pair args),
                ret_map = (#ret_map compose_funs)
                          (#ret_map this)
                      (map #ret_map args),
                all_thm = TRUTH, (* FIXME *)
                all_tm  = (#all_tm compose_funs)
                          (#all_tm this)
                      (map #all_tm args),
                all_map = (#all_map compose_funs)
                          (#all_map this)
                      (map #all_map args),
                all_T   = (#all_T   compose_funs)
                          (#all_T   this)
                      (map #all_T   args),
                all_mono= (#all_mono compose_funs)
                          (#all_mono this)
                      (map #all_mono args)
              } : rich_type
           end;

(* After the composition, we have to do some lambda abstractions
   in order to get the theorems in the right form                *)
local
fun gen_inj_pair_thm thm maps rets =
  GENL (interleave maps rets) (DISCH_ALL thm)
fun gen_ret_map_thm thm maps rets = let
  val eq = concl thm
  val (O, [r, m]) = strip_comb (lhs eq)
  val func = fn (x,l) => RIGHT_LIST_BETA (REFL (list_mk_comb(list_mk_abs(l, x), l)))
  val r' = func(r, rets)
  val m' = func(m, maps)
  val left = MK_COMB (AP_TERM O r', m')
  val os = map combinSyntax.mk_o (zip rets maps)
  val func2 = fst o dom_rng o type_of
  val subst = map op|-> (zip (map func2 rets) (map func2 maps))
  val r'' = INST_TYPE subst r'
  val rets' = map (inst subst) rets
  val repl = map op|-> (zip rets' os)
  val right = INST repl r''
  val trans = TRANS (TRANS left thm) (SYM right)
in GENL (interleave maps rets) trans
end;
fun gen_all_mono_thm thm rtcs =
  GEN_ALL (foldl (uncurry DISCH) thm
          (map (concl o #all_mono) rtcs))
  |> REWRITE_RULE [AND_IMP_INTRO];
(*  DISCH ((concl o #all_mono o hd) rtcs) thm;*)
in
fun compose_pretype pty = let
    (* 'self' type variable *)
    val  self = gen_tyvar ()
    val oself = optionSyntax.mk_option self
    (* variables *)
    val vnames = pty_get_tyvars pty
    val vars = map mk_vartype vnames
    (* generate map/retrieve functions for the base case *)
    val indices = map gen_tyvar vars
    val rets = map (fn (x,y) => genvar (x --> y --> oself))
                   (zip vars indices)
    val map_rngs = map gen_tyvar vars
    val maps = map (genvar o op-->) (zip vars map_rngs)
    (* reverse maps: for retrieve_map theorems *)
    val maps' = map (genvar o op-->) (zip map_rngs vars)
    val alls  = map (fn v => genvar (v --> bool)) vars
    val alls' = map (fn v => genvar (v --> bool)) vars
    val func = fn (w, (x, (y, z))) => gen_rich_tyvar w x y z
    val rtcs = map func
        (zip vars (zip rets (zip (zip maps maps') (zip alls alls'))))
    val dict = (vnames, rtcs)
    val comp = compose dict self pty
  in {inj_pair = gen_inj_pair_thm (#inj_pair comp) maps rets,
      ret_map  = gen_ret_map_thm (#ret_map comp) maps' rets,
      all_tm   = list_mk_abs(alls, #all_tm comp),
      all_thm  = TRUTH,
      all_map  = gen_ret_map_thm (#all_map comp) maps' alls,
      all_T    = #all_T comp,
      all_mono = gen_all_mono_thm (#all_mono comp) rtcs
     } : rich_type
end
end;


(*****************************************************************)
(* mk_constructor: takes a rich type - a composition of other    *)
(*                 types - and returns the fixpoint of that type *)
(*                 constructor with respect to the type vars     *)
(*                 that have been created by gen_tyvar.          *)
(*****************************************************************)
local
  val x = mk_var("x", alpha);
  val Jsome_tm = mk_abs(x, mk_abs(mk_var("u", one_ty),
                      optionSyntax.mk_some x));
  val Iu_tm = mk_abs(x, oneSyntax.one_tm)
  fun helper thm =
    if (is_forall o concl) thm then let
     val c = concl thm
     val (f, c') = dest_forall c
     val (g, _ ) = dest_forall c'
     val (a, a') = (dom_rng o type_of) f
     val (i, os) = (dom_rng o snd o dom_rng o type_of) g
     val self = optionSyntax.dest_option os
     val x = genvar self
     val b = is_gen_tyvar a
     val f' = if b then inst [alpha|->self] Iu_tm
                   else inst [alpha|->a   ] combinSyntax.I_tm
     val g' = if b then inst [alpha|->self] Jsome_tm
                   else inst [alpha|->a, beta|->self] J_tm
     val thm = INST_TYPE [a |-> (if b then self   else a),
                          a'|-> (if b then one_ty else a),
                          i |-> one_ty] thm
     val thm = ((SPEC g') o (SPEC f')) thm
     val t = if b then INST_TYPE [alpha|->self] some_inj_thm
                  else INST_TYPE [alpha|->a, beta|->self] k_inj_thm
    in PROVE_HYP t (helper thm)
    end else UNDISCH_ALL thm
in
fun mk_constructor (ty:rich_type) =
  let
    val thm = helper (#inj_pair ty)
    val (r, R) = (dest_comb o concl) thm
    val (_, M) =  dest_comb r
    val (_, L) =  (dom_rng  o type_of) M
    val (B, O) = (dom_rng o snd o dom_rng o type_of) R
    val self = optionSyntax.dest_option O
    val tree_ty = (listSyntax.mk_list_type B)
                --> pairSyntax.mk_prod(L, numSyntax.num)
    val thm = INST_TYPE[self|->tree_ty] thm
  in MATCH_MP inj_constr_thm thm
  end
end;

(* mk_all *)
local
 val KT = mk_abs(mk_var("x", alpha), T);
 fun helper tm dict self = if is_abs tm then
   let
     val (x, t) = dest_abs tm
     val ty = (fst o dom_rng o type_of) x
   in helper (case lookup ty dict of
        NONE   => subst [x |-> (inst [alpha|->ty] KT)] t
      | SOME s => subst [(inst [ty|->self] x)
                         |-> mk_var("ok_"^s, self-->bool)]
                         (inst [ty|->self] t)
      ) dict self
   end else tm;
 fun div_sum tm 1 = [tm]
   | div_sum tm n = let
       val (a, b) = dest_comb tm
       val (_,ab) = dest_comb a
     in b::(div_sum ab (n-1))
     end;
in
fun mk_all tm dict self =
  let
    val a = helper tm (swap dict) self
    val b = div_sum a (List.length (fst dict))
in b end;
end;


fun div_sum_vars ty f 1 = let
      val var = genvar ty
    in [(var, f var)]
    end
  | div_sum_vars ty f n = let
      val (a, b) = sumSyntax.dest_sum ty
      val var = genvar a
      val inv = sumSyntax.mk_inl(var, b)
      val f' = f o (fn x => sumSyntax.mk_inr(x, a))
    in (var, inv)::(div_sum_vars b f' (n-1))
    end;

(*****************************************************************)
(*****************************************************************)

fun Datatype q = let
    val df = ParseDatatype.hparse q
    (* sum all the types and the constructors *)
    val ty_descrs = type_descriptions df
    val pty = nest_tyop "sum" ty_descrs
    (* fixpoint variables *)
    val ty_names = map fst df
    val mut_no = List.length df
    val ty_vars = map gen_tyvar df
    (* replace fixpoint vars *)
    val dict = (ty_names, ty_vars)
    val pty = fix_mutual_vars dict pty
  (* old: my_wit *)
  val rich_comp = compose_pretype pty
  val ty_names = fst dict
  val inj_Co = mk_constructor rich_comp
  val Co = (snd o dest_comb o concl) inj_Co;
  val (dom, rng) = (dom_rng o type_of) Co;
  (* predicate names for representation predicates *)
  val no = List.length ty_names
  val oks = map (fn s=>mk_var("ok_"^s, rng-->bool)) ty_names
  val vars = div_sum_vars dom I no
  (**)
  val all_tm = #all_tm rich_comp
  val tmp = gen_tyvar ()
  val alls = rev (map (inst [tmp|->rng]) (mk_all all_tm dict tmp))
  (**)
  val Hyps = map mk_comb (zip alls (map fst vars))
  val Cs = map (curry mk_comb Co) (map snd vars)
  val Cons = map mk_comb (zip oks Cs)
  val rules = map mk_imp (zip Hyps Cons)
  val genl = map mk_forall (zip (map fst vars) rules)
  val def_tm = list_mk_conj genl
  (**)
  val mythm = prove(``!P Q. (P SUBSET Q) = (!x. P x ==> Q x)``,
        simp[pred_setTheory.SUBSET_DEF, boolTheory.IN_DEF])
  val mono = PURE_REWRITE_RULE [mythm] (#all_mono rich_comp)
  val func = fn x =>  (PURE_REWRITE_RULE [mythm] x
                      |> SIMP_RULE bool_ss [PULL_FORALL]
                      |> SPEC_ALL)
  val monoset = map (fn x =>
           ((fst o dest_const o #all_tm) x, func (#all_mono x)))
                (snd (!NDDB.types))
  val (rules, ind, cases) =
      InductiveDefinition.new_inductive_definition
      ((!IndDefLib.the_monoset)@monoset) "stem" (def_tm, [])
  (* witnesses *)
  val ws = List.tabulate(no, K (NONE:Thm.thm option))
  val constrs = map GEN_ALL (BODY_CONJUNCTS rules) (* fixme *)
  val goal = map
             (fst o dest_imp o snd o strip_forall o concl) constrs
  val gthms = map ASSUME goal
  val wits = Witness.find_inductive_witnesses gthms ws constrs
  (**)
  val tyaxs = map new_type_definition (zip ty_names wits)
  val func = fn (s,ax) => define_new_type_bijections
    {name = s^"_absrep", ABS = s^"_abs", REP = s^"_rep", tyax = ax}
in map func (zip ty_names tyaxs)
end;

(* tests: *)
val q = `X = C Y | C X ; Y = C ('b option option option) | C 'a`
val it = Datatype q
(*val repabss = map extract_abs_rep it*)

end;

(*
fun extract_abs_rep thm = let
  val tmp = thm |> concl |> dest_conj |> fst |> dest_forall |> snd |> dest_eq |> fst |> dest_comb
  in ((fst o dest_comb o snd) tmp, fst tmp)
end;


fun mk_constructors absreps = let
  (* Ci' = absi o C o INi o (map rep1 .. repn) *)
  Hyps
Cs
val abs = map snd repabss
val reps = map fst repabss
val map_tm = (hd o tl o snd o strip_comb o fst o dest_eq
             o snd o strip_forall o concl o #all_map) rich_comp
list_mk_icomb(map_tm, )
free_vars map_tm
val map_reps_tm = list_mk_comb(map_tm,
list_mk_icomb(combinSyntax.o_tm, [Co, ]
  val

(* RUBBISH *)
(*
    MyDatatype.wit_test `X = C X 'a X 'b | C 'a ; Y = C Y | C 'a`
    test2 `X = C (X+(X#X))`
*)(*
val xxx = mk_thm([], ``(!x. sette x ==> nove x) ==>
     (sum_all sette
          (prod_all sette otto )) x ==>
       (sum_all nove
          (prod_all nove zero )) x``);
*)


*)
