(* ========================================================================= *)
(* FILE          : mleLib.sml                                                *)
(* DESCRIPTION   : Useful functions for the experiments                      *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mleLib :> mleLib =
struct

open HolKernel Abbrev boolLib aiLib numTheory arithmeticTheory

val ERR = mk_HOL_ERR "mleLib"

(* -------------------------------------------------------------------------
   Terms
   ------------------------------------------------------------------------- *)

fun list_mk_binop binop l = case l of
    [] => raise ERR "" ""
  | [a] => a
  | a :: m => list_mk_comb  (binop, [a, list_mk_binop binop m])

fun arity_of t = length (fst (strip_type (type_of t)))

(* -------------------------------------------------------------------------
   Arithmetic
   ------------------------------------------------------------------------- *)

fun mk_suc x = mk_comb (``SUC``,x);
fun mk_add (a,b) = list_mk_comb (``$+``,[a,b]);
val zero = ``0:num``;
fun mk_sucn n = funpow n mk_suc zero;
fun mk_mult (a,b) = list_mk_comb (``$*``,[a,b]);

fun dest_suc x =
  let val (a,b) = dest_comb x in
    if not (term_eq  a ``SUC``) then raise ERR "" "" else b
  end

fun dest_add tm =
  let val (oper,argl) = strip_comb tm in
    if not (term_eq oper ``$+``) then raise ERR "" "" else pair_of_list argl
  end

fun is_suc_only tm =
  if term_eq tm zero then true else
  (is_suc_only (dest_suc tm)  handle HOL_ERR _ => false)

fun eval_numtm tm =
  (string_to_int o term_to_string o rhs o concl o computeLib.EVAL_CONV) tm

(* -------------------------------------------------------------------------
   Position
   ------------------------------------------------------------------------- *)

type pos = int list

fun subst_pos (tm,pos) res =
  if null pos then res else
  let
    val (oper,argl) = strip_comb tm
    fun f i x = if i = hd pos then subst_pos (x,tl pos) res else x
    val newargl = mapi f argl
  in
    list_mk_comb (oper,newargl)
  end

fun find_subtm (tm,pos) =
  if null pos then tm else
  let val (oper,argl) = strip_comb tm in
    find_subtm (List.nth (argl,hd pos), tl pos)
  end

fun narg_ge n (tm,pos) =
  let val (_,argl) = strip_comb (find_subtm (tm,pos)) in length argl >= n end

fun all_pos tm =
  let
    val (oper,argl) = strip_comb tm
    fun f i arg = map (fn x => i :: x) (all_pos arg)
  in
    [] :: List.concat (mapi f argl)
  end

(* -------------------------------------------------------------------------
   Equality
   ------------------------------------------------------------------------- *)

fun sym x = mk_eq (swap (dest_eq x))

fun unify a b = Unify.simp_unify_terms [] a b

fun paramod_ground eq (tm,pos) =
  let
    val (eql,eqr) = dest_eq eq
    val subtm = find_subtm (tm,pos)
    val sigma = unify eql subtm
    val eqrsig = subst sigma eqr
    val tmsig = subst sigma tm
    val result = subst_pos (tmsig,pos) eqrsig
  in
    if term_eq result tm orelse length (free_vars_lr result) > 0
    then NONE
    else SOME result
  end
  handle Interrupt => raise Interrupt | _ => NONE

(* -------------------------------------------------------------------------
   Arithmetical proof using left outer most strategy
   ------------------------------------------------------------------------- *)

val robinson_eq_list =
 [``x + 0 = x``,``x + SUC y = SUC (x + y)``,``x * 0 = 0``,
   ``x * SUC y = x * y + x``]

val robinson_eq_vect = Vector.fromList robinson_eq_list

fun trySome f l = case l of
    [] => NONE
  | a :: m => (case f a of NONE => trySome f m | SOME b => SOME b)

fun lo_rwpos tm =
  let
    fun f pos =
      let fun test x = isSome (paramod_ground x (tm,pos)) in
        exists test robinson_eq_list
      end
  in
    List.find f (all_pos tm)
  end

fun lo_trace nmax toptm =
  let
    val l = ref []
    val acc = ref 0
    fun loop tm =
      if is_suc_only tm then (SOME (rev (!l),!acc))
      else if !acc > nmax then NONE else
    let
      val pos = valOf (lo_rwpos tm)
      val tm' = valOf (trySome (C paramod_ground (tm,pos)) robinson_eq_list)
    in
      (l := (tm,pos) :: !l; acc := length pos + 1 + !acc; loop tm')
    end
  in
    loop toptm
  end

fun lo_prooflength n tm = snd (valOf (lo_trace n tm))



end (* struct *)

