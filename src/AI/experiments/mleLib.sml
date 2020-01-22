(* ========================================================================= *)
(* FILE          : mleLib.sml                                                *)
(* DESCRIPTION   : Useful functions for the experiments                      *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure mleLib :> mleLib =
struct

open HolKernel Abbrev boolLib aiLib numTheory arithmeticTheory psTermGen

val ERR = mk_HOL_ERR "mleLib"

fun compare_third cmp ((_,_,a),(_,_,b)) = cmp (a,b)

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

fun string_of_pos pos = String.concatWith " " (map its pos)
fun pos_of_string s = map string_to_int (String.tokens Char.isSpace s)

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

fun all_subtmpos tm =
  let
    val (oper,argl) = strip_comb tm
    fun f i arg = map_snd (fn x => i :: x) (all_subtmpos arg)
  in
    (tm,[]) :: List.concat (mapi f argl)
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

(* -------------------------------------------------------------------------
   Combinators
   ------------------------------------------------------------------------- *)

val cI = mk_var ("cI",alpha)
val cK = mk_var ("cK",alpha)
val cS = mk_var ("cS",alpha)
val cX = mk_var ("cX",alpha)
val cY = mk_var ("cY",alpha)
val cZ = mk_var ("cZ",alpha)
val cA = mk_var ("cA",``:'a -> 'a -> 'a``)
val cT = mk_var ("cT",``:'a -> 'a``)
val cE = mk_var ("cE", ``:'a -> 'a -> 'a``)
val vf = mk_var ("vf",alpha)
val vg = mk_var ("vg",alpha)
val vy = mk_var ("vy",alpha)
val vx = mk_var ("vx",alpha)
val cX = mk_var ("cX",alpha)
val cV1 = mk_var ("cV1",alpha)
val cV2 = mk_var ("cV2",alpha)
val cV3 = mk_var ("cV3",alpha)

fun mk_cE (a,b) = list_mk_comb (cE,[a,b])
fun tag x = mk_comb (cT,x)

infix oo
fun op oo (a,b) = list_mk_comb (cA,[a,b])

val s_thm = mk_eq (cS oo vf oo vg oo vx, (vf oo vx) oo (vg oo vx))
val k_thm = mk_eq (cK oo vx oo vy, vx)
val s_thm_tagged = mk_eq (tag (cS oo vf oo vg oo vx), (vf oo vx) oo (vg oo vx))
val k_thm_tagged = mk_eq (tag (cK oo vx oo vy), vx)
val s_thm_quant = list_mk_forall ([vf,vg,vx],s_thm);
val k_thm_quant  = list_mk_forall ([vx,vy],k_thm);

val left_thm = mk_eq (tag (vf oo vg), tag vf oo vg)
val right_thm = mk_eq (tag (vf oo vg), vf oo tag vg)

fun mk_cA (a,b) = list_mk_comb (cA,[a,b])
fun list_mk_cA tml = case tml of
    [] => raise ERR "list_mk_cA" ""
  | [tm] => tm
  | a :: b :: m => list_mk_cA (mk_cA (a,b) :: m)

fun strip_cA_aux tm =
  if is_var tm then [tm] else
  let 
    val (oper,argl) = strip_comb tm
    val _ = if term_eq oper cA then () else raise ERR "strip_cA" ""
    val (a1,a2) = pair_of_list argl    
  in
    a2 :: strip_cA_aux a1
  end
fun strip_cA tm = rev (strip_cA_aux tm)
fun is_cconst x = is_var x andalso hd_string (fst (dest_var x)) = #"c"
fun cterm_size tm = 
  let fun test x = is_cconst x andalso not (term_eq x cA) in
    length (find_terms test tm) 
  end
fun random_cterm n = random_term [cA,cS,cK] (2*n-1,alpha);

(* -------------------------------------------------------------------------
   Printing combinators
   ------------------------------------------------------------------------- *)

fun cts_par tm = 
  if is_cconst tm then tl_string (fst (dest_var tm)) else 
    case (snd (strip_comb tm)) of
      [a] => "[" ^ cts a ^ "]"
    | [a,b] =>  "(" ^ cts a ^ " " ^ cts_par b ^ ")"
    | _ => raise ERR "cts_par" ""
and cts tm = 
  if is_cconst tm then tl_string (fst (dest_var tm)) else 
    case (snd (strip_comb tm)) of
      [a] => "[" ^ cts a ^ "]"
    | [a,b] =>  cts a ^ " " ^ cts_par b
    | _ => raise ERR "cts" ""

(* -------------------------------------------------------------------------
   Rewriting combinators
   ------------------------------------------------------------------------- *)

fun is_cmatch eq tm = 
  let val (sub,_) = match_term (lhs eq) tm in
    not (exists is_cconst (map #redex sub))
  end
  handle HOL_ERR _ => false

fun exists_cmatch eq tm = can (find_term (is_cmatch eq)) tm

fun subst_cmatch eq tm =
  let 
    val subtm = find_term (is_cmatch eq) tm
    val sub1 = fst (match_term (lhs eq) subtm)
    val eqinst = subst sub1 eq
    val sub2 = [{redex = lhs eqinst, residue = rhs eqinst}]
  in
    subst_occs [[1]] sub2 tm
  end

fun subst_cmatch_first eql tm =
  let 
    val subtm = find_term (fn x => exists (fn eq => is_cmatch eq x) eql) tm
    val eq = valOf (List.find (fn eq => is_cmatch eq subtm) eql)
    val sub1 = fst (match_term (lhs eq) subtm)
    val eqinst = subst sub1 eq
    val sub2 = [{redex = lhs eqinst, residue = rhs eqinst}]
  in
    subst_occs [[1]] sub2 tm
  end

fun lo_cnorm n eql tm =
  if not (exists (C exists_cmatch tm) eql) then SOME tm
  else if n <= 0 orelse cterm_size tm >= 100 then NONE else
    let val tm' = subst_cmatch_first eql tm in
      lo_cnorm (n-1) eql tm'
    end
    


end (* struct *)

