(* ========================================================================= *)
(* FILE          : mleDiophLib.sml                                           *)
(* DESCRIPTION   : Tools for term synthesis on Diophantin equations          *)
(* AUTHOR        : (c) Thibault Gauthier, Czech Technical University         *)
(* DATE          : 2020                                                      *)
(* ========================================================================= *)

structuremleDiophLib :>mleDiophLib =
struct

open HolKernel Abbrev boolLib aiLib numTheory arithmeticTheory psTermGen

val ERR = mk_HOL_ERR "mleLib"

fun compare_third cmp ((_,_,a),(_,_,b)) = cmp (a,b)

val modulo = 16
val numberl = List.tabulate (modulo,I)
val expl = List.tabulate (5,I)
val numbertml = map (fn x => mk_var ("n" ^ its x, ``:num``)) numberl
val basevl = [``v1:num``,``v2:num``,``v3:num``]
val basekvl = [``k0:num``] @ basevl
val basetml = numbertml @ basekvl

fun eval_f tm =
  if is_var tm then 
    let 
      val s = fst (dest_var tm)
      val sn = tl_string s
    in 
      if hd_string s = #"n" 
      then let val n = string_to_int sn in (fn l => n) end
      else let val i = string_to_int sn in (fn l => List.nth (l,i)) end
    end
  else let val (oper,argl) = strip_comb tm in
    if term_eq oper ``$+`` then 
      let val (f1,f2) = pair_of_list (map eval_f argl) in
        fn l => (f1 l + f2 l) mod modulo
      end
    else if term_eq oper ``$*`` then
      let val (f1,f2) = pair_of_list (map eval_f argl) in
        fn l => (f1 l * f2 l) mod modulo
      end
    else raise ERR "eval_f" (tts tm)
  end

fun has_solution bl diophf k =
  let
    val l1 = cartesian_productl 
      (map (fn b => if b then numberl else [0]) bl)
    val l2 = map (fn l => k :: l) l1
  in
    exists (fn l => diophf l = 0) l2
  end

fun dioph_set diophtm = 
  let 
    val vl = free_vars diophtm
    fun test x = tmem x vl
    val bl = map test basevl
    val diophf = eval_f diophtm 
  in 
    filter (has_solution bl diophf) numberl
  end

fun random_monomial () = 
  let 
    val expl = List.tabulate (length basekvl, fn _ => random_elem expl)
    val l = combine (basekvl,expl)
    fun f (v,n) = if n = 0 then ``n1:num`` else 
      list_mk_mult (List.tabulate (n,fn _ => v))
  in
    list_mk_mult (random_elem (tl numbertml) :: map f l)
  end

fun random_polynomial () =
  let val n = random_int (1,5) in
    list_mk_plus (List.tabulate (n, fn _ => random_monomial ()))
  end

fun dterm_size tm = 
  if is_var tm orelse is_numeral tm then 1 else
  let val (oper,argl) = strip_comb tm in
    1 + sum_int (map dterm_size argl)
  end

fun gen_diophset n d =
  if dlength d >= n then d else
  let 
    val tm = random_polynomial () 
    val set = dioph_set tm
  in
    if dmem set d then 
      let val oldtm = dfind set d in
        if dterm_size tm < dterm_size oldtm 
        then (print "*"; gen_diophset n (dadd set tm d))
        else (print "."; gen_diophset n d)
      end
    else (print_endline (its ((dlength d) + 1)); 
          gen_diophset n (dadd set tm d))
  end


(* -------------------------------------------------------------------------
   Position
   ------------------------------------------------------------------------- *)

fun subst_pos (tm,pos) res =
  if null pos then res else
  let
    val (oper,argl) = strip_comb tm
    fun f i x = if i = hd pos then subst_pos (x,tl pos) res else x
    val newargl = mapi f argl
  in
    list_mk_comb (oper,newargl)
  end

fun all_pos tm =
  let
    val (oper,argl) = strip_comb tm
    fun f i arg = map_snd (fn x => i :: x) (all_pos arg)
  in
    (tm,[]) :: List.concat (mapi f argl)
  end

(* -------------------------------------------------------------------------
   Combinators
   ------------------------------------------------------------------------- *)

(* variables *)
val cI = mk_var ("i",alpha)
val cK = mk_var ("k",alpha)
val cS = mk_var ("s",alpha)
val cC = mk_var ("c",alpha)
val cB = mk_var ("b",alpha)
val cY = mk_var ("y",alpha)

val cX = mk_var ("x",alpha)
val cA = mk_var ("a",``:'a -> 'a -> 'a``)
val cT = mk_var ("t",``:'a -> 'a``)
val cV = mk_var ("v",``:'a -> bool``)
val cL = mk_var ("l",``:'a -> bool``)


val vx = mk_var ("X",alpha)
val vy = mk_var ("Y",alpha)
val vz = mk_var ("Z",alpha)
val vu = mk_var ("U",alpha)
val vv = mk_var ("V",alpha)
val vw = mk_var ("W",alpha)
val v1 = mk_var ("V1",alpha)
val v2 = mk_var ("V2",alpha)
val v3 = mk_var ("V3",alpha)

(* constructors *)
fun mk_cV a = mk_comb (cV,a)
fun mk_cL a = mk_comb (cL,a)

val cEV = mk_var ("ev",``:'a -> 'a -> bool``)
val cRW = mk_var ("rw",``:'a -> 'a -> bool``)
fun mk_cRW (a,b) = list_mk_comb (cRW,[a,b])
fun mk_cEV (a,b) = list_mk_comb (cEV,[a,b])

fun mk_tag x = mk_comb (cT,x)
fun dest_tag tm = 
  let 
    val (oper,argl) = strip_comb tm
    val _ = if term_eq oper cT then () else raise ERR "dest_tag" ""
  in
    singleton_of_list argl
  end
 
infix oo
fun op oo (a,b) = list_mk_comb (cA,[a,b])
fun mk_cA (a,b) = list_mk_comb (cA,[a,b])
fun dest_cA tm = 
  let 
    val (oper,argl) = strip_comb tm
    val _ = if term_eq oper cA then () else raise ERR "dest_cA" ""
  in
    pair_of_list argl
  end

fun list_mk_cA tml = case tml of
    [] => raise ERR "list_mk_cA" ""
  | [tm] => tm
  | a :: b :: m => list_mk_cA (mk_cA (a,b) :: m)
fun strip_cA_aux tm =
  if is_var tm then [tm] else
  let val (oper,argl) = strip_comb tm in
    if term_eq oper cA then 
      let val (a1,a2) = pair_of_list argl in a2 :: strip_cA_aux a1 end 
    else [tm]
  end

fun strip_cA tm = rev (strip_cA_aux tm)

(* theorems *)
fun forall_capital tm =
  let 
    fun test v = (Char.isUpper o hd_string o fst o dest_var) v
    val vl = filter test (free_vars_lr tm)
  in
    list_mk_forall (vl,tm)
  end

val s_thm_bare = mk_eq (cS oo vx oo vy oo vz, (vx oo vz) oo (vy oo vz))
val k_thm_bare = mk_eq (cK oo vx oo vy, vx)

val eq_axl_bare = [s_thm_bare,k_thm_bare]
val eq_axl = map forall_capital eq_axl_bare

fun tag_lhs eq = let val (a,b) = dest_eq eq in mk_eq (mk_tag a, b) end
val left_thm = mk_eq (mk_tag (vx oo vy), mk_tag vx oo vy)
val right_thm = mk_eq (mk_tag (vx oo vy), vx oo mk_tag vy)
val tag_axl_bare = map tag_lhs eq_axl_bare @ [left_thm,right_thm]

fun cterm_size tm = 
  let val (oper,argl) = strip_comb tm in
    (if tmem oper [cA,cT] then 0 else 1) + sum_int (map cterm_size argl)
  end

(* big step semantics *)
val ev_ax1 = mk_cV cK
val ev_ax2 = mk_imp (mk_cV vv, mk_cV (mk_cA (cK,vv)))
val ev_ax3 = mk_cV cS
val ev_ax4 = mk_imp (mk_cV vv, mk_cV (mk_cA (cS,vv)))
val ev_ax5 = mk_imp (mk_cV vv, mk_cV (list_mk_cA [cS,vu,vv]))
val ev_ax6 = mk_imp (mk_cL vv,mk_cV vv)
val ev_ax7 = list_mk_imp ([mk_cL vu, mk_cV vv],mk_cL(mk_cA(vu,vv)))
val ev_ax8 = mk_imp (mk_cV vv, mk_cEV (vv,vv))
val ev_ax9 = mk_imp (mk_cEV (vx,vv), mk_cEV (list_mk_cA [cK,vx,vy],vv))
val ev_ax10 = mk_imp (mk_cEV ((vx oo vz) oo (vy oo vz),vv), 
  mk_cEV (list_mk_cA [cS,vx,vy,vz],vv))
val ev_ax11 = mk_imp (mk_cEV (vx,vv), mk_cEV (cK oo vx, cK oo vv));
val ev_ax12 = mk_imp (mk_cEV (vx,vv), mk_cEV (cS oo vx, cS oo vv));
val ev_ax13 = 
  list_mk_imp ([mk_cEV (vx,vu),mk_cEV (vy,vv)], 
    mk_cEV (cS oo vx oo vy, cS oo vu oo vv));
val ev_ax14 = 
  list_mk_imp ([mk_cEV (vx,vu),mk_cEV (vy,vv),mk_cEV (vu oo vv,vw)], 
    mk_cEV (vx oo vy,vw));
val ev_axl = 
  map forall_capital
    [ev_ax1,ev_ax2,ev_ax3,ev_ax4,ev_ax5,ev_ax6,ev_ax7,ev_ax8,
     ev_ax9,ev_ax10,ev_ax11,ev_ax12,ev_ax13,ev_ax14]

(* small step semantics *)
val rw_ax1 = mk_cRW (vx,vx)
val rw_ax2 = 
  list_mk_imp ([mk_cRW (vu,vv), mk_cRW (vx,vy)], mk_cRW (vu oo vx, vv oo vy));

val rw_ax3 = mk_cRW (list_mk_cA [cS,vx,vy,vz], (vx oo vz) oo (vy oo vz));
val rw_ax4 = mk_cRW (list_mk_cA [cK,vx,vy], vx);
val rw_ax5 = list_mk_imp ([mk_cRW (vx,vy), mk_cRW(vy,vz)], mk_cRW(vx,vz));
val rw_axl = map forall_capital [rw_ax1,rw_ax2,rw_ax3,rw_ax4,rw_ax5]

(* -------------------------------------------------------------------------
   Printing combinators
   ------------------------------------------------------------------------- *)

fun cts tm = 
  if is_var tm then fst (dest_var tm) else
  let val tml = strip_cA tm in
    "(" ^ String.concatWith " " (map cts tml) ^ ")"
  end

(* -------------------------------------------------------------------------
   Rewriting combinators
   ------------------------------------------------------------------------- *)

fun is_capital_var tm = is_var tm andalso 
  Char.isUpper (hd_string (fst (dest_var tm)))

fun is_match eq tm = 
  let val (sub,_) = match_term (lhs eq) tm in
    all is_capital_var (map #redex sub)
  end
  handle HOL_ERR _ => false

fun exists_match eq tm = can (find_term (is_match eq)) tm

fun subst_match eq tm =
  let 
    val subtm = find_term (is_match eq) tm
    val sub1 = fst (match_term (lhs eq) subtm)
    val eqinst = subst sub1 eq
    val sub2 = [{redex = lhs eqinst, residue = rhs eqinst}]
  in
    subst_occs [[1]] sub2 tm
  end

fun subst_match_first eql tm =
  let 
    val subtm = find_term (fn x => exists (fn eq => is_match eq x) eql) tm
    val eq = valOf (List.find (fn x => is_match x subtm) eql)
    val sub1 = fst (match_term (lhs eq) subtm)
    val eqinst = subst sub1 eq
    val sub2 = [{redex = lhs eqinst, residue = rhs eqinst}]
  in
    subst_occs [[1]] sub2 tm
  end

fun lo_cnorm n eql tm =
  if not (exists (C exists_match tm) eql) then SOME tm
  else if n <= 0 orelse cterm_size tm >= 100 then NONE else
    let val tm' = subst_match_first eql tm in
      lo_cnorm (n-1) eql tm'
    end

exception Break

fun fast_lo_cnorm n eql maintm =
  let
    val i = ref 0    
    fun fast_lo_cnorm_aux n eql tm = 
      let val eqo = List.find (fn x => is_match x tm) eql in
        case eqo of
          SOME eq => 
          let 
            val sub1 = fst (match_term (lhs eq) tm)
            val newtm = subst sub1 (rhs eq)
            val _ = incr i
            val _ = if !i > n then raise Break else () 
          in
            fast_lo_cnorm_aux n eql newtm
          end   
        | NONE => 
          let val (oper,argl) = strip_comb tm in
            list_mk_comb (oper, map (fast_lo_cnorm_aux n eql) argl)
          end  
      end
    fun loop tm =
      if not (exists (C exists_match tm) eql)
      then SOME tm
      else loop (fast_lo_cnorm_aux n eql tm)
  in
    loop maintm handle Break => NONE
  end

 
fun is_nf tm = not (exists (C exists_match tm) eq_axl_bare)

(* -------------------------------------------------------------------------
   Generating commbinators
   ------------------------------------------------------------------------- *)

fun random_cterm n = random_term [cA,cS,cK] (2*n-1,alpha)

fun cgen_random n (a,b) =
  let 
    val size = random_int (a,b)
    val tml = List.tabulate (n, fn _ => random_cterm size)
  in
    mk_fast_set Term.compare tml
  end 

fun cgen_exhaustive size = gen_term [cA,cS,cK] (2*size-1,alpha)

fun is_reducible tm =
  let 
    val tml = strip_cA tm 
    val oper = hd tml
    val n = length tml
  in
    if n <= 2 then false else
    if term_eq oper cK andalso length tml >= 3 then true else 
    if n <= 3 then false else
      (term_size (valOf (fast_lo_cnorm 100 eq_axl_bare tm)) < 
       term_size tm
       handle Option => false)
  end
    
fun cgen_synt_cache cache n = dfind n (!cache) handle NotFound =>
  if n <= 1 then raise ERR "cgen_synt_aux" "" else
    let 
      val l = map pair_of_list (number_partition 2 n)  
      fun f (n1,n2) =
      let
        val l1 = cgen_synt_cache cache n1
        val l2 = cgen_synt_cache cache n2
      in
        filter (not o is_reducible) (map mk_cA (cartesian_product l1 l2))
      end
      val l3 = List.concat (map f l)
    in
      cache := dadd n l3 (!cache); l3
    end

fun cgen_synt n = 
  let 
    val cache = ref (dnew Int.compare [(1,[cS,cK])])
    val il = List.tabulate (n, fn x => x + 1)
  in
    List.concat (map (cgen_synt_cache cache) il)
  end

(*
load "mleLib"; openmleDiophLib;
val tml = cgen_synt 10; length tml;
329699;

val tml' = cgen_exhaustive 8; length tml';
*)



end (* struct *)

