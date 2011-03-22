structure patriciaLib :> patriciaLib =
struct

(* interactive use:
  app load ["ConseqConv", "wordsLib", "bitSyntax", "pred_setSyntax",
            "patriciaSyntax"];
*)

open HolKernel Parse boolLib bossLib Q computeLib patriciaTheory patriciaSyntax;

(* ------------------------------------------------------------------------- *)

val emit_mesg = !Feedback.emit_MESG;
val _ = Feedback.emit_MESG := false;

val m = apropos;

val ERR = mk_HOL_ERR "patricia";

(* ------------------------------------------------------------------------- *)

datatype term_ptree =
    Empty
  | Leaf of Arbnum.num * term
  | Branch of Arbnum.num * int * term_ptree * term_ptree;

fun dest_ptree t =
  if is_empty t then
    Empty
  else if is_leaf t then
    let val (k, d) = dest_leaf t in
      Leaf (numLib.dest_numeral k, d)
    end
  else if is_branch t then
    let val (p,m,l,r) = dest_branch t in
      Branch (numLib.dest_numeral p,numLib.int_of_term m,
             dest_ptree l,dest_ptree r)
    end
  else
   raise ERR "dest_ptree" "";

fun mk_ptree Empty = mk_empty ``:'a``
  | mk_ptree (Leaf (k, d)) = mk_leaf(numLib.mk_numeral k, d)
  | mk_ptree (Branch (p,m,l,r)) =
        mk_branch (numLib.mk_numeral p,numLib.term_of_int m,
                   mk_ptree l, mk_ptree r);

fun odd n = Arbnum.mod2 n = Arbnum.one;
fun even n = Arbnum.mod2 n = Arbnum.zero;
fun div_2exp x n = funpow x Arbnum.div2 n;
fun bit b n = odd (div_2exp b n);

fun mod_2exp x n =
  if x = 0 orelse n = Arbnum.zero then Arbnum.zero
  else let val v = Arbnum.times2 (mod_2exp (x - 1) (Arbnum.div2 n)) in
    if even n then v else Arbnum.plus1 v
  end;

fun mod_2exp_eq x a b =
  if x = 0 then true else
    (odd a = odd b) andalso
    mod_2exp_eq (x - 1) (Arbnum.div2 a) (Arbnum.div2 b);

fun lt_2exp x n =
 (x = Arbnum.zero) orelse (Arbnum.toInt (Arbnum.log2 x) < n);

val empty = Empty;

fun every_leaf P Empty = true
  | every_leaf P (Leaf (j,d)) = P j d
  | every_leaf P (Branch (p,m,l,r)) = every_leaf P l andalso every_leaf P r;

fun is_ptree Empty = true
  | is_ptree (Leaf (k,d)) = true
  | is_ptree (Branch (p,m,l,r)) =
      lt_2exp p m andalso not (l = Empty) andalso not (r = Empty) andalso
      every_leaf (fn k => fn d => mod_2exp_eq m k p andalso bit m k) l
      andalso
      every_leaf (fn k => fn d => mod_2exp_eq m k p andalso not (bit m k)) r
      andalso
      is_ptree l andalso is_ptree r;

fun branching_bit p0 p1 =
  if (odd p0 = even p1) orelse (p0 = p1) then 0
  else branching_bit (Arbnum.div2 p0) (Arbnum.div2 p1) + 1;

fun peek Empty k = NONE
  | peek (Leaf (j,d)) k = if k = j then SOME d else NONE
  | peek (Branch (p,m,l,r)) k = peek (if bit m k then l else r) k;

fun join (p0,t0,p1,t1) =
let val m = branching_bit p0 p1 in
  if bit m p0 then
    Branch (mod_2exp m p0, m, t0, t1)
  else
    Branch (mod_2exp m p0, m, t1, t0)
end;

fun add Empty x = Leaf x
  | add (Leaf (j,d)) (x as (k,e)) =
      if j = k then Leaf x else join (k,Leaf x,j,Leaf (j,d))
  | add (Branch (p,m,l,r)) (x as (k,e)) =
      if mod_2exp_eq m k p then
        if bit m k then
             Branch (p,m,add l x,r)
           else
             Branch (p,m,l,add r x)
      else
        join (k, Leaf x, p, Branch (p,m,l,r));

fun add_list t = foldl (uncurry (C add)) t;

fun ptree_of_list l = add_list Empty l;

fun branch (_,_,Empty,t) = t
  | branch (_,_,t,Empty) = t
  | branch (p,m,t0,t1) = Branch (p,m,t0,t1);

fun remove Empty k = Empty
  | remove (t as Leaf (j,d)) k = if j = k then Empty else t
  | remove (t as Branch (p,m,l,r)) k =
         if mod_2exp_eq m k p then
           if bit m k then
             branch (p, m, remove l k, r)
           else
             branch (p, m, l, remove r k)
         else
           t;

local
  fun traverse_aux Empty f = f
    | traverse_aux (Leaf (j,d)) f = j :: f
    | traverse_aux (Branch (p,m,l,r)) f = traverse_aux l (traverse_aux r f)
in
  fun traverse t = traverse_aux t []
end;

fun keys t = Listsort.sort Arbnum.compare (traverse t);

fun transform f Empty = Empty
  | transform f (Leaf (j,d)) = Leaf (j, f d)
  | transform f (Branch (p,m,l,r)) = Branch (p,m,transform f l,transform f r);

local
  fun list_of_ptree_aux Empty f = f
    | list_of_ptree_aux (Leaf (j,d)) f = (j,d) :: f
    | list_of_ptree_aux (Branch (p,m,l,r)) f =
        list_of_ptree_aux l (list_of_ptree_aux r f)
in
  fun list_of_ptree t = list_of_ptree_aux t []
end;

fun size Empty = 0
  | size (Leaf (j,d)) = 1
  | size (Branch (p,m,l,r)) = size l + size r;

fun depth Empty = 0
  | depth (Leaf (j,d)) = 1
  | depth (Branch (p,m,l,r)) = 1 + (Int.max (depth l, depth r));

fun tabulate (n, f) =
    let fun h i =
       if i<n then
         add (h (i+1)) (f i)
       else
         Empty
    in if n<0 then raise Size else h 0 end;

val t = tabulate(1000,
 fn i => let val n = Arbnum.fromInt i in (n,numLib.mk_numeral n) end)

infix in_ptree insert_ptree;

fun op in_ptree (n,t) = isSome (peek t n);
fun op insert_ptree (n,t) = add t (n,oneSyntax.one_tm);

val ptree_of_nums = foldl (op insert_ptree) Empty;

fun int_peek t i = peek t (Arbnum.fromInt i);
fun int_add t (i,d) = add t (Arbnum.fromInt i, d);
fun int_add_list t = foldl (uncurry (C int_add)) t;
fun int_ptree_of_list l = int_add_list Empty l;
fun int_remove t i = remove t (Arbnum.fromInt i);
fun op int_in_ptree (n,t) = isSome (int_peek t n);
fun op int_insert_ptree (n,t) = int_add t (n,oneSyntax.one_tm);
val ptree_of_ints = foldl (op int_insert_ptree) Empty;

local
  val n256 = Arbnum.fromInt 256;
  fun l2n [] = Arbnum.zero
    | l2n (h::t) = Arbnum.+(Arbnum.mod(h, n256), Arbnum.*(n256, l2n t))
in
  fun string_to_num s =
    l2n (List.rev
      (Arbnum.one :: List.map (Arbnum.fromInt o Char.ord) (String.explode s)))
end

fun string_peek t i = peek t (string_to_num i);
fun string_add t (i,d) = add t (string_to_num i, d);
fun string_add_list t = foldl (uncurry (C string_add)) t;
fun string_ptree_of_list l = string_add_list Empty l;
fun string_remove t i = remove t (string_to_num i);
fun op string_in_ptree (n,t) = isSome (string_peek t n);
fun op string_insert_ptree (n,t) = string_add t (n,oneSyntax.one_tm);
val ptree_of_strings = foldl (op string_insert_ptree) Empty;

fun custom_pp_term_ptree pp_empty pp_entry i ppstrm t =
let open Portable
    val {add_break,add_newline,
         add_string,begin_block,end_block,...} = with_ppstream ppstrm
    val pp_empty = pp_empty ppstrm
    val pp_entry = pp_entry ppstrm
    val l = Listsort.sort (Arbnum.compare o (fst ## fst)) (list_of_ptree t)
    val ll = List.take(l, i) handle Subscript => l
    val ll_len = length ll
    val elided = length l - ll_len
    fun add_elided () =
          add_string ("|+ ... " ^ "(" ^ Int.toString elided ^
                      (if elided = 1 then " entry" else " entries") ^
                      " elided)")
in
  if null l then
    pp_empty true
  else
   (begin_block CONSISTENT 0;
    pp_empty false;
      begin_block CONSISTENT 0;
      if null ll then
        add_elided()
      else
        (app (fn x => (pp_entry x; add_break(1,0))) (List.take(ll, ll_len - 1));
         pp_entry (last ll) : unit;
         if 0 < elided then (add_newline(); add_elided()) else ());
      end_block ();
    end_block ())
end;

fun standard_pp_empty ppstrm (b:bool) =
  (Portable.add_string ppstrm "Empty";
   (if b then () else Portable.add_break ppstrm (1,1)));

fun standard_pp_entry ppstrm (n, tm) =
  (Portable.add_string ppstrm "|+ (";
   Arbnum.pp_num ppstrm n;
   Portable.add_string ppstrm ", ";
   Hol_pp.pp_term ppstrm tm;
   Portable.add_string ppstrm ")");

fun pp_term_ptree ppstrm t =
  (Portable.add_string ppstrm "``";
   custom_pp_term_ptree standard_pp_empty standard_pp_entry 150 ppstrm t;
   Portable.add_string ppstrm "``");

(* ------------------------------------------------------------------------- *)

val PAT_CONV =
let val compset = wordsLib.words_compset()
    val _ = add_thms [BRANCHING_BIT_def,BRANCH_def] compset
in
  CBV_CONV compset
end;

val QSORT_CONV =
let open sortingTheory
    val compset = reduceLib.num_compset()
    val _ = listSimps.list_rws compset
    val _ = add_thms
              [pairTheory.UNCURRY_DEF, QSORT_DEF, PARTITION_DEF, PART_DEF]
              compset
in
  CBV_CONV compset
end;

fun eval_eq m n = numLib.REDUCE_CONV (mk_eq(m,n));
fun eval_bit x n = wordsLib.WORD_EVAL_CONV (bitSyntax.mk_bit(x,n));
fun eval_mod_2exp x n = numLib.REDUCE_CONV (numSyntax.mk_mod_2exp(x,n));
fun eval_branching_bit m n = PAT_CONV (mk_branching_bit(m,n));
fun eval_mod_2exp_eq n a b =
   wordsLib.WORD_EVAL_CONV (bitSyntax.mk_mod_2exp_eq(n,a,b));

fun is_eqt t = same_const T (rhs (concl t)) handle HOL_ERR _ => false;
fun is_eqf t = same_const F (rhs (concl t)) handle HOL_ERR _ => false;

val nvariant = with_flag (priming, SOME "") (uncurry variant);

fun dest_strip t =
let val (l,r) = strip_comb t in
  (fst (dest_const l), r)
end;

(* ------------------------------------------------------------------------- *)

val PEEK_RWT = prove(
  `(!k p m l r. (BIT m k = T) ==> (PEEK (Branch p m l r) k = PEEK l k)) /\
    !k p m l r. (BIT m k = F) ==> (PEEK (Branch p m l r) k = PEEK r k)`,
  SRW_TAC [] [PEEK_def]);

val (peek_empty,peek_leaf,peek_branch_l,peek_branch_r) =
let val l = CONJUNCTS PEEK_def in
  (hd l,hd (tl l),SPEC_ALL (CONJUNCT1 PEEK_RWT),SPEC_ALL (CONJUNCT2 PEEK_RWT))
end;

fun peek_ptree t k =
  case dest_strip t of
    ("Empty", []) => ([REWR_CONV (Thm.SPEC k peek_empty)], t)
  | ("Leaf", [j, d]) =>
       ([REWR_CONV (numLib.REDUCE_RULE (Drule.ISPECL [k,j,d] peek_leaf))], t)
  | ("Branch", [p, m, l, r]) =>
        let val bthm = eval_bit m k in
          if is_eqt bthm then
            let val (c, lhs) = peek_ptree l k
                val v = nvariant (all_vars lhs, mk_var("v", type_of lhs))
            in
              (REWR_CONV (MATCH_MP peek_branch_l bthm) :: c,
               mk_branch(p,m,lhs,v))
            end
          else
            let val (c, rhs) = peek_ptree r k
                val v = nvariant (all_vars rhs, mk_var("v", type_of rhs))
            in
              (REWR_CONV (MATCH_MP peek_branch_r bthm) :: c,
               mk_branch(p,m,v,rhs))
            end
        end
  | _ => raise ERR "peek_ptree" "Not Empty, Leaf or Branch";

fun peek_ptree_thm(t,k) =
let val (cs, rt) = peek_ptree t k
    val mt = mk_peek(rt, k)
in
  EVERY_CONV cs mt
end;

fun PTREE_PEEK_CONV tm = REWR_CONV (peek_ptree_thm (dest_peek tm)) tm;

val IN_PTREE_SOME = prove(
  `(PEEK t k = SOME ()) ==> (k IN_PTREE t = T)`,
  SRW_TAC [] [IN_PTREE_def]);

val IN_PTREE_NONE = prove(
  `(PEEK t k = NONE) ==> (k IN_PTREE t = F)`,
  SRW_TAC [] [IN_PTREE_def]);

fun PTREE_IN_PTREE_CONV tm =
let val (k,t) = dest_in_ptree tm
    val peek_thm = peek_ptree_thm(t,k)
    val is_some = (optionSyntax.is_some o rhs o concl) peek_thm
    val thm = if is_some then IN_PTREE_SOME else IN_PTREE_NONE
in
  REWR_CONV (MATCH_MP thm peek_thm) tm
end;

(* ------------------------------------------------------------------------- *)

val ADD_RWT = prove(
  `(!j d e. ADD (Leaf j d) (j,e) = Leaf j e) /\
   (!j d k e b q.
      ((j = k) = F) /\
      (BRANCHING_BIT k j = b) /\
      (MOD_2EXP b k = q) /\
      (BIT b k = T) ==>
      (ADD (Leaf j d) (k,e) = Branch q b (Leaf k e) (Leaf j d))) /\
   (!j d k e b q.
      ((j = k) = F) /\
      (BRANCHING_BIT k j = b) /\
      (MOD_2EXP b k = q) /\
      (BIT b k = F) ==>
      (ADD (Leaf j d) (k,e) = Branch q b (Leaf j d) (Leaf k e))) /\
   (!k e p m l r b q.
      (MOD_2EXP_EQ m k p = F) /\
      (BRANCHING_BIT k p = b) /\
      (MOD_2EXP b k = q) /\
      (BIT b k = T) ==>
      (ADD (Branch p m l r) (k,e) =
         Branch q b (Leaf k e) (Branch p m l r))) /\
   (!k e p m l r b q.
      (MOD_2EXP_EQ m k p = F) /\
      (BRANCHING_BIT k p = b) /\
      (MOD_2EXP b k = q) /\
      (BIT b k = F) ==>
      (ADD (Branch p m l r) (k,e) =
         Branch q b (Branch p m l r) (Leaf k e))) /\
   (!k e p m l r.
      (MOD_2EXP_EQ m k p = T) /\
      (BIT m k = T) ==>
      (ADD (Branch p m l r) (k,e) = Branch p m (ADD l (k,e)) r)) /\
   (!k e p m l r.
      (MOD_2EXP_EQ m k p = T) /\
      (BIT m k = F) ==>
      (ADD (Branch p m l r) (k,e) = Branch p m l (ADD r (k,e))))`,
  SRW_TAC [boolSimps.LET_ss] [ADD_def, JOIN_def]);

val (add_empty,
     add_leaf_eq,add_leaf_l,add_leaf_r,
     add_branch_join_l,add_branch_join_r,
     add_branch_l,add_branch_r) =
  case map SPEC_ALL (CONJUNCTS ADD_RWT) of
    [a,b,c,d,e,f,g] => (CONJUNCT1 ADD_def, a, b, c, d, e, f, g)
  | _ => raise ERR "" "";

fun DREWR_CONV thm = DEPTH_CONV (REWR_CONV thm);

fun add_ptree t k e =
  case dest_strip t of
    ("Empty", []) => ([DREWR_CONV (Drule.ISPECL [k,e] add_empty)], t)
  | ("Leaf", [j, d]) =>
        let val eq_thm = eval_eq j k
            val tm = mk_leaf(j, mk_var("v", type_of d))
        in
          if is_eqt eq_thm then
            ([DREWR_CONV add_leaf_eq], tm)
          else
            let val bb_thm = eval_branching_bit k j
                val b = (rhs o concl) bb_thm
                val mod_thm = eval_mod_2exp b k
                val q = (rhs o concl) mod_thm
                val b_thm = eval_bit b k
            in
              ([DREWR_CONV
                 (MATCH_MP (if is_eqt b_thm then add_leaf_l else add_leaf_r)
                   (LIST_CONJ [eq_thm, bb_thm, mod_thm, b_thm]))], tm)
            end
        end
  | ("Branch", [p, m, l, r]) =>
        let val mod_eq_thm = eval_mod_2exp_eq m k p in
          if is_eqt mod_eq_thm then
            let val b_thm = eval_bit m k in
              if is_eqt b_thm then
                let val (c, lhs) = add_ptree l k e
                    val v = nvariant (all_vars lhs @ all_vars e,
                                      mk_var("v", type_of lhs))
                in
                  (DREWR_CONV
                     (MATCH_MP add_branch_l (CONJ mod_eq_thm b_thm)) :: c,
                   mk_branch(p,m,lhs,v))
                end
              else
                let val (c, rhs) = add_ptree r k e
                    val v = nvariant (all_vars rhs @ all_vars e,
                                      mk_var("v", type_of rhs))
                in
                  (DREWR_CONV
                     (MATCH_MP add_branch_r (CONJ mod_eq_thm b_thm)) :: c,
                   mk_branch(p,m,v,rhs))
                end
            end
          else
            let val bb_thm = eval_branching_bit k p
                val b = (rhs o concl) bb_thm
                val mod_thm = eval_mod_2exp b k
                val q = (rhs o concl) mod_thm
                val b_thm = eval_bit b k
                val vars = all_vars e
                val typ = type_of t
                val v1 = nvariant (vars, mk_var("v", typ))
                val v2 = nvariant (v1::vars, mk_var("v", typ))
                val tm = mk_branch(p,m,v1,v2)
            in
              ([DREWR_CONV
                 (MATCH_MP (if is_eqt b_thm
                            then add_branch_join_l
                            else add_branch_join_r)
                   (LIST_CONJ [mod_eq_thm, bb_thm, mod_thm, b_thm]))], tm)
            end
        end
  | _ => raise ERR "add_ptree" "Not Empty, Leaf or Branch";

fun add_ptree_thm(t,x) =
let val (k,e) = pairSyntax.dest_pair x
    val (cs, rt) = add_ptree t k e
    val mt = mk_add(rt,x)
in
  EVERY_CONV cs mt
end;

fun PTREE_ADD_CONV tm = REWR_CONV (add_ptree_thm (dest_add tm)) tm;

val INSERT_PTREE = prove(
  `(ADD t (k,()) = t') ==> (k INSERT_PTREE t = t')`,
  SRW_TAC [] []);

fun PTREE_INSERT_PTREE_CONV tm =
let val (k,t) = dest_insert_ptree tm
    val insert_thm = add_ptree_thm(t,pairSyntax.mk_pair(k,oneSyntax.one_tm))
in
  REWR_CONV (MATCH_MP INSERT_PTREE insert_thm) tm
end;

(* ------------------------------------------------------------------------- *)

val REMOVE_RWT = prove(
  `(!k p m l r.
      (MOD_2EXP_EQ m k p = F) ==>
      (REMOVE (Branch p m l r) k = Branch p m l r)) /\
   (!k p m l r.
      (MOD_2EXP_EQ m k p = T) /\
      (BIT m k = T) ==>
      (REMOVE (Branch p m l r) k = BRANCH (p,m,REMOVE l k,r))) /\
   (!k p m l r.
      (MOD_2EXP_EQ m k p = T) /\
      (BIT m k = F) ==>
      (REMOVE (Branch p m l r) k = BRANCH (p,m,l,REMOVE r k)))`,
  SRW_TAC [boolSimps.LET_ss] [REMOVE_def, BRANCH_def]);

val (remove_empty,remove_leaf,remove_prefix,remove_branch_l,remove_branch_r) =
let val l = CONJUNCTS REMOVE_def in
  case map SPEC_ALL (CONJUNCTS REMOVE_RWT) of
    [a,b,c] => (hd l,hd (tl l),a,b,c)
  | _ => raise ERR "" ""
end;

fun generic_ptree(t,vars) =
  case (fst o dest_const o fst o strip_comb) t of
    "Empty" => t
  | "Leaf" =>
      let val v1 = nvariant(vars, mk_var("v", ``:num``))
          val v2 = nvariant(v1::vars, mk_var("v", dest_ptree_type (type_of t)))
      in
        mk_leaf(v1,v2)
      end
  | "Branch" =>
      let val typ = type_of t
          val v1 = nvariant(vars, mk_var("v", ``:num``))
          val vars = v1::vars
          val v2 = nvariant(vars, mk_var("v", ``:num``))
          val vars = v2::vars
          val v3 = nvariant(vars, mk_var("v", typ))
          val vars = v3::vars
          val v4 = nvariant(vars, mk_var("v", typ))
      in
        mk_branch(v1,v2,v3,v4)
      end
  | _ => raise ERR "generic_ptree" "Not Empty, Leaf or Branch";

fun remove_ptree t k =
  case dest_strip t of
    ("Empty", []) => ([DREWR_CONV (Thm.SPEC k remove_empty)], t)
  | ("Leaf", [j, d]) =>
       ([DREWR_CONV (numLib.REDUCE_RULE (Drule.ISPECL [j,d,k] remove_leaf))], t)
  | ("Branch", [p, m, l, r]) =>
        let val mod_eq_thm = eval_mod_2exp_eq m k p in
          if is_eqt mod_eq_thm then
            let val b_thm = eval_bit m k in
              if is_eqt b_thm then
                let val (c, lhs) = remove_ptree l k in
                  (DREWR_CONV
                    (MATCH_MP remove_branch_l (CONJ mod_eq_thm b_thm)) :: c,
                   mk_branch(p,m,lhs,generic_ptree(r,all_vars lhs)))
                end
              else
                let val (c, rhs) = remove_ptree r k in
                  (DREWR_CONV
                    (MATCH_MP remove_branch_r (CONJ mod_eq_thm b_thm)) :: c,
                   mk_branch(p,m,generic_ptree(l,all_vars rhs),rhs))
                end
            end
          else
            let val typ = type_of t
                val v1 = mk_var("l", typ)
                val v2 = mk_var("r", typ)
            in
              ([DREWR_CONV (MATCH_MP remove_prefix mod_eq_thm)],
               mk_branch(p,m,v1,v2))
            end
        end
  | _ => raise ERR "remove_ptree" "Not Empty, Leaf or Branch";

fun remove_ptree_thm(t,k) =
let val (cs, rt) = remove_ptree t k
    val mt = mk_remove(rt, k)
in
  EVERY_CONV (cs @ [PAT_CONV]) mt
end;

fun PTREE_REMOVE_CONV tm = REWR_CONV (remove_ptree_thm (dest_remove tm)) tm;

(* ------------------------------------------------------------------------- *)

val TRANSFORM_RWT = prove(
  `!f p m l r x y.
     (TRANSFORM f l = x) /\ (TRANSFORM f r = y) ==>
     (TRANSFORM f (Branch p m l r) = Branch p m x y)`,
  SRW_TAC [] [TRANSFORM_def]);

val (transform_empty,transform_leaf,transform_branch) =
  (CONJUNCT1 TRANSFORM_def, CONJUNCT1 (CONJUNCT2 TRANSFORM_def),
   (GEN `f` o GEN `p` o GEN `m` o SPEC_ALL) TRANSFORM_RWT);

fun PTREE_TRANSFORM_CONV tm =
let
  val (f,t) = dest_transform tm
  fun ptree_transform t =
     (case dest_strip t of
        ("Empty", []) => REWR_CONV transform_empty (mk_transform(f,t))
      | ("Leaf", [j, d]) =>
           (REWR_CONV transform_leaf THENC EVAL) (mk_transform(f,t))
      | ("Branch", [p, m, l, r]) =>
           let val l_thm = ptree_transform l
               val r_thm = ptree_transform r
           in
          (MATCH_MP (Drule.ISPECL [f,p,m] transform_branch) (CONJ l_thm r_thm))
           end
      | _ => raise ERR "PTREE_TRANSFORM_CONV" "Not Empty, Leaf or Branch")
in
  ptree_transform t
end;

(* ------------------------------------------------------------------------- *)

val SIZE_RWT = prove(
  `!p m l r x y.
     (SIZE l = x) /\ (SIZE r = y) ==>
     (SIZE (Branch p m l r) = x + y)`,
  SRW_TAC [] [SIZE]);

val (size_empty,size_leaf,size_branch) =
  (CONJUNCT1 SIZE, CONJUNCT1 (CONJUNCT2 SIZE),
   (GEN `p` o GEN `m` o SPEC_ALL) SIZE_RWT);

fun ptree_size t =
  case dest_strip t of
    ("Empty", []) => REWR_CONV size_empty (mk_size t)
  | ("Leaf", [j, d]) => REWR_CONV size_leaf (mk_size t)
  | ("Branch", [p, m, l, r]) =>
        let val l_thm = ptree_size l
            val r_thm = ptree_size r
        in
          (MATCH_MP (Drule.ISPECL [p,m] size_branch) (CONJ l_thm r_thm))
        end
  | _ => raise ERR "ptree_size" "Not Empty, Leaf or Branch";

fun PTREE_SIZE_CONV tm =
  (ptree_size THENC numLib.REDUCE_CONV) (dest_size tm);

(* ------------------------------------------------------------------------- *)

val DEPTH_RWT = prove(
  `!p m l r x y.
     (DEPTH l = x) /\ (DEPTH r = y) ==>
     (DEPTH (Branch p m l r) = 1 + MAX x y)`,
  SRW_TAC [] [DEPTH_def]);

val (depth_empty,depth_leaf,depth_branch) =
  (CONJUNCT1 DEPTH_def, CONJUNCT1 (CONJUNCT2 DEPTH_def),
   (GEN `p` o GEN `m` o SPEC_ALL) DEPTH_RWT);

fun ptree_depth t =
  case dest_strip t of
    ("Empty", []) => REWR_CONV depth_empty (mk_depth t)
  | ("Leaf", [j, d]) => REWR_CONV depth_leaf (mk_depth t)
  | ("Branch", [p, m, l, r]) =>
        let val l_thm = ptree_depth l
            val r_thm = ptree_depth r
        in
          MATCH_MP (Drule.ISPECL [p,m] depth_branch)
                   (CONJ l_thm r_thm)
        end
  | _ => raise ERR "ptree_depth" "Not Empty, Leaf or Branch";

fun PTREE_DEPTH_CONV tm =
  (ptree_depth THENC numLib.REDUCE_CONV) (dest_depth tm);

(* ------------------------------------------------------------------------- *)

val EVERY_LEAF_RWT = prove(
  `(!P p m l r.
     (EVERY_LEAF P l = F) ==>
     (EVERY_LEAF P (Branch p m l r) = F)) /\
   (!P p m l r.
     (EVERY_LEAF P r = F) ==>
     (EVERY_LEAF P (Branch p m l r) = F)) /\
   (!P p m l r.
     (EVERY_LEAF P l = T) /\ (EVERY_LEAF P r = T) ==>
     (EVERY_LEAF P (Branch p m l r) = T))`,
  SRW_TAC [] [EVERY_LEAF_def]);

val (every_leaf_empty,every_leaf_leaf,
     every_leaf_l,every_leaf_r,every_leaf_T) =
  case map (GEN `P` o GEN `p` o GEN `m` o SPEC_ALL)
           (CONJUNCTS EVERY_LEAF_RWT)
  of
    [a,b,c] => (CONJUNCT1 EVERY_LEAF_def, CONJUNCT1 (CONJUNCT2 EVERY_LEAF_def),
                a,b,c)
  | _ => raise ERR "" "";

fun PTREE_EVERY_LEAF_CONV tm =
let
  val (P,t) = dest_every_leaf tm
  fun ptree_every_leaf t =
     (case dest_strip t of
        ("Empty", []) => REWR_CONV every_leaf_empty (mk_every_leaf(P,t))
      | ("Leaf", [j, d]) =>
           let val p_thm = EVAL (mk_comb(mk_comb(P,j),d)) in
             (REWR_CONV every_leaf_leaf THENC REWR_CONV p_thm)
                (mk_every_leaf(P,t))
           end
      | ("Branch", [p, m, l, r]) =>
           let val lhs = ptree_every_leaf l in
             if is_eqf lhs then
               MATCH_MP (Drule.ISPECL [P,p,m] every_leaf_l) lhs
             else
               let val rhs = ptree_every_leaf r in
                 if is_eqf rhs then
                   MATCH_MP (Drule.ISPECL [P,p,m] every_leaf_r) rhs
                 else
                   MATCH_MP (Drule.ISPECL [P,p,m] every_leaf_T)
                            (CONJ lhs rhs)
               end
           end
      | _ => raise ERR "PTREE_DEPTH_CONV" "Not Empty, Leaf or Branch")
  val thm = ptree_every_leaf t
in
  if is_eqf thm then
    REWR_CONV thm tm
  else
    thm
end;

(* ------------------------------------------------------------------------- *)

val EXISTS_LEAF_RWT = prove(
  `(!P p m l r.
     (EXISTS_LEAF P l = T) ==>
     (EXISTS_LEAF P (Branch p m l r) = T)) /\
   (!P p m l r.
     (EXISTS_LEAF P r = T) ==>
     (EXISTS_LEAF P (Branch p m l r) = T)) /\
   (!P p m l r.
     (EXISTS_LEAF P l = F) /\ (EXISTS_LEAF P r = F) ==>
     (EXISTS_LEAF P (Branch p m l r) = F))`,
  SRW_TAC [] [EXISTS_LEAF_def]);

val (exists_leaf_empty,exists_leaf_leaf,
     exists_leaf_l,exists_leaf_r,exists_leaf_F) =
  case map (GEN `P` o GEN `p` o GEN `m` o SPEC_ALL)
           (CONJUNCTS EXISTS_LEAF_RWT)
  of
    [a,b,c] => (CONJUNCT1 EXISTS_LEAF_def,
                CONJUNCT1 (CONJUNCT2 EXISTS_LEAF_def), a,b,c)
  | _ => raise ERR "" "";

fun PTREE_EXISTS_LEAF_CONV tm =
let
  val (P,t) = dest_exists_leaf tm
  fun ptree_exists_leaf t =
     (case dest_strip t of
        ("Empty", []) => REWR_CONV exists_leaf_empty (mk_exists_leaf(P,t))
      | ("Leaf", [j, d]) =>
           let val p_thm = EVAL (mk_comb(mk_comb(P,j),d)) in
             (REWR_CONV exists_leaf_leaf THENC REWR_CONV p_thm)
                (mk_exists_leaf(P,t))
           end
      | ("Branch", [p, m, l, r]) =>
           let val lhs = ptree_exists_leaf l in
             if is_eqt lhs then
               MATCH_MP (Drule.ISPECL [P,p,m] exists_leaf_l) lhs
             else
               let val rhs = ptree_exists_leaf r in
                 if is_eqt rhs then
                   MATCH_MP (Drule.ISPECL [P,p,m] exists_leaf_r) rhs
                 else
                   MATCH_MP (Drule.ISPECL [P,p,m] exists_leaf_F)
                            (CONJ lhs rhs)
               end
           end
      | _ => raise ERR "PTREE_DEPTH_CONV" "Not Empty, Leaf or Branch")
  val thm = ptree_exists_leaf t
in
  if is_eqt thm then
    REWR_CONV thm tm
  else
    thm
end;

(* ------------------------------------------------------------------------- *)

val is_ptree_term_size_limit = ref 5000;

val is_ptree_compset = wordsLib.words_compset();
val _ = add_thms [REWRITE_RULE [bitTheory.LT_TWOEXP] IS_PTREE_def,
                  (GSYM o CONJUNCT1) ptree_distinct,
                  (GSYM o CONJUNCT1 o CONJUNCT2) ptree_distinct]
                 is_ptree_compset;
val _ = add_conv (every_leaf_tm,  2, PTREE_EVERY_LEAF_CONV) is_ptree_compset;

fun IS_PTREE_EVAL_CONV t =
  if !is_ptree_term_size_limit = ~1 orelse
     term_size t < !is_ptree_term_size_limit
  then CHANGED_CONV (CBV_CONV is_ptree_compset) t else NO_CONV t;

val PMATCH = PART_MATCH (snd o dest_imp);

val IS_PTREE_ADD_CONV       = PMATCH ADD_IS_PTREE
val IS_PTREE_ADD_LIST_CONV  = PMATCH ADD_LIST_IS_PTREE
val IS_PTREE_REMOVE_CONV    = PMATCH REMOVE_IS_PTREE
val IS_PTREE_TRANSFORM_CONV = PMATCH TRANSFORM_IS_PTREE
val IS_PTREE_INSERT_PTREE_CONV    = PMATCH INSERT_PTREE_IS_PTREE
val IS_PTREE_PTREE_OF_NUMSET_CONV = PMATCH PTREE_OF_NUMSET_IS_PTREE;

val IS_PTREE_X_CONV =
  IS_PTREE_ADD_CONV ORELSEC IS_PTREE_INSERT_PTREE_CONV ORELSEC
  IS_PTREE_REMOVE_CONV ORELSEC IS_PTREE_TRANSFORM_CONV ORELSEC
  IS_PTREE_ADD_LIST_CONV ORELSEC IS_PTREE_PTREE_OF_NUMSET_CONV;

fun PTREE_IS_PTREE_CONV t =
let val thm = ConseqConv.DEPTH_STRENGTHEN_CONSEQ_CONV IS_PTREE_X_CONV t
    val (l,r) = dest_imp (concl thm)
    val is_ptree_thm = IS_PTREE_EVAL_CONV l
in
  if is_eqt is_ptree_thm then
    EQT_INTRO (MATCH_MP thm (EQT_ELIM is_ptree_thm))
  else
    raise ERR "PTREE_IS_PTREE_CONV" ""
end handle UNCHANGED => IS_PTREE_EVAL_CONV t;

(* ------------------------------------------------------------------------- *)

(* add conversion(s) for PTREE_OF_NUMSET *)

val rhsc = rhs o concl;
val lhsc = lhs o concl;

val PTREE_OF_NUMSET_RWT = prove(
  `(!x t s y.
     IS_PTREE t /\ FINITE s /\ (PTREE_OF_NUMSET t s = y) ==>
     (PTREE_OF_NUMSET t (x INSERT s) = x INSERT_PTREE y)) /\
   (!s1 s2 t y.
     IS_PTREE t /\ FINITE s1 /\ FINITE s2 /\
     (PTREE_OF_NUMSET t s1 = y) /\
     (PTREE_OF_NUMSET y s2 = z) ==>
     (PTREE_OF_NUMSET t (s1 UNION s2) = z))`,
  SRW_TAC [] [PTREE_OF_NUMSET_UNION, PTREE_OF_NUMSET_INSERT]);

val ptee_of_numset_insert = CONJUNCT1 PTREE_OF_NUMSET_RWT;
val ptee_of_numset_union = CONJUNCT2 PTREE_OF_NUMSET_RWT;

fun PTREE_OF_NUMSET_CONV tm =
  case total dest_ptree_of_numset tm of
    SOME (t,s) =>
      if pred_setSyntax.is_insert s then
        let val (x,y) = pred_setSyntax.dest_insert s
            val is_ptree_thm = EQT_ELIM (PTREE_IS_PTREE_CONV (mk_is_ptree t))
            val finite_thm = EQT_ELIM (EVAL (pred_setSyntax.mk_finite y))
            val thm = PTREE_OF_NUMSET_CONV (mk_ptree_of_numset(t,y))
        in
          MATCH_MP (Drule.ISPEC x ptee_of_numset_insert)
                   (LIST_CONJ [is_ptree_thm,finite_thm,thm])
        end
      else if pred_setSyntax.is_empty s then
        REWR_CONV PTREE_OF_NUMSET_EMPTY tm
      else if pred_setSyntax.is_union s then
        let val (s1,s2) = pred_setSyntax.dest_union s
            val is_ptree_thm = EQT_ELIM (PTREE_IS_PTREE_CONV (mk_is_ptree t))
            val finite_thm1 = EQT_ELIM (EVAL (pred_setSyntax.mk_finite s1))
            val finite_thm2 = EQT_ELIM (EVAL (pred_setSyntax.mk_finite s2))
            val thm1 = PTREE_OF_NUMSET_CONV (mk_ptree_of_numset(t,s1))
            val thm2 = PTREE_OF_NUMSET_CONV (mk_ptree_of_numset(rhsc thm1,s2))
        in
          MATCH_MP ptee_of_numset_union
                  (LIST_CONJ [is_ptree_thm,finite_thm1,finite_thm2,thm1,thm2])
        end
      else raise ERR "PTREE_OF_NUMSET_CONV" ""
  | _ => raise ERR "PTREE_OF_NUMSET_CONV" "";

(* ------------------------------------------------------------------------- *)
(* Conversion for applications of ADD, REMOVE and INSERT_PTREE (ARI)         *)
(* ------------------------------------------------------------------------- *)

val DEPTH_ADD_THM = prove(
  `(c1 = t) /\ (ADD t (k,d) = c2) ==> (ADD c1 (k,d) = c2)`,
  SRW_TAC [] []);

val DEPTH_REMOVE_THM = prove(
  `(c1 = t) /\ (REMOVE t k = c2) ==> (REMOVE c1 k = c2)`,
  SRW_TAC [] []);

val DEPTH_INSERT_PTREE_THM = prove(
  `(c1 = t) /\ (k INSERT_PTREE t = c2) ==> (k INSERT_PTREE c1 = c2)`,
  SRW_TAC [] []);

fun DEPTH_ARI_CONV rwt tm =
  REWR_CONV rwt tm
  handle HOL_ERR e =>
    if is_add tm then
      let val (t,x) = dest_add tm
          val thm = DEPTH_ARI_CONV rwt t
          val t' = rhsc thm
      in
        MATCH_MP DEPTH_ADD_THM (CONJ thm (PTREE_ADD_CONV (mk_add(t',x))))
      end
    else if is_remove tm then
      let val (t,k) = dest_remove tm
          val thm = DEPTH_ARI_CONV rwt t
          val t' = rhsc thm
      in
        MATCH_MP DEPTH_REMOVE_THM
          (CONJ thm (PTREE_REMOVE_CONV (mk_remove(t',k))))
      end
    else if is_insert_ptree tm then
      let val (k,t) = dest_insert_ptree tm
          val thm = DEPTH_ARI_CONV rwt t
          val t' = rhsc thm
      in
        MATCH_MP DEPTH_INSERT_PTREE_THM
          (CONJ thm (PTREE_INSERT_PTREE_CONV (mk_insert_ptree(k,t'))))
      end
    else
      raise HOL_ERR e;

(* ------------------------------------------------------------------------- *)

val ptree_consts_ref = ref ([]:term list);
val ptree_cache_ref = ref ([]:(term * thm) list);

val ptree_strict_defn_check = ref false;
val ptree_max_cache_size = ref 10;
val ptree_new_defn_depth = ref ~1;

local
  fun contains_term t1 t2 = can (find_term (can (match_term t2))) t1
in
  fun best_match_ptree tm =
    let fun get_best_match c [] = c
          | get_best_match NONE (h::t) =
              get_best_match
                (if contains_term tm (fst h) then SOME h else NONE) t
          | get_best_match (SOME x) (h::t) =
              get_best_match
                (if contains_term tm (fst h) andalso
                    term_size (fst x) < term_size (fst h)
                 then SOME h else SOME x) t
    in
      get_best_match NONE (!ptree_cache_ref)
    end
end;

fun remove_oldest_ptree_theorem () =
let val n = length (!ptree_cache_ref) in
  if !ptree_max_cache_size < n then
    ptree_cache_ref := List.take(!ptree_cache_ref, n - 1)
  else
    ()
end;

fun const_definition c =
let val {Name,Thy,...} = dest_thy_const c in
  DB.fetch Thy (Name^"_def") handle HOL_ERR _ => DB.fetch Thy Name
end;

fun root_const tm =
    if is_add tm then
      let val (t,_) = dest_add tm in root_const t end
    else if is_remove tm then
      let val (t,_) = dest_remove tm in root_const t end
    else if is_insert_ptree tm then
      let val (_,t) = dest_insert_ptree tm in root_const t end
    else
      tm;

fun is_add_remove_insert tm =
  is_add tm orelse is_remove tm orelse is_insert_ptree tm;

fun root_name tm =
  if is_const tm then
    let val defn = rhsc (const_definition tm) in
      if is_add_remove_insert defn then
        root_name (root_const defn)
      else
        dest_const tm
    end
  else
    if is_add_remove_insert tm then
      root_name (root_const tm)
    else
      raise ERR "root_name" "";

fun const_variant c =
let val (name,typ) = root_name c handle HOL_ERR _ => ("ptree", type_of c)
    val v = mk_var(name,typ)
in
  with_flag (priming,SOME "") (uncurry variant) ([], v)
end;

fun is_ptree_const tm = isSome (List.find (term_eq tm) (!ptree_consts_ref));

fun root_const_depth tm =
let fun const_depth d tm =
      if is_add tm then
        let val (t,_) = dest_add tm in const_depth (d + 1) t end
      else if is_remove tm then
        let val (t,_) = dest_remove tm in const_depth (d + 1) t end
      else if is_insert_ptree tm then
        let val (_,t) = dest_insert_ptree tm in const_depth (d + 1) t end
      else
        if is_ptree_const tm then
          d
        else
          if not (!ptree_strict_defn_check) orelse
             is_ptree (dest_ptree tm)
          then ~d - 1
          else raise ERR "root_const_depth" ""
in
  const_depth 0 tm
end;

fun insert_ptree_defn thm =
let val (l,r) = dest_eq (concl thm)
    val d = root_const_depth r
    val _ = is_const l andalso ((0 < d) orelse (d = ~1)) orelse
            raise ERR "insert_ptree_defn" "Not a patricia tree constant"
in
  ptree_consts_ref := l::(!ptree_consts_ref)
end;

fun insert_ptree_theorem thm =
let val (l,r) = dest_eq (concl thm)
    val _ = is_ptree_type (type_of l) andalso (root_const_depth r = ~1) orelse
            raise ERR "insert_ptree_theorem" "Not a patricia tree constant"
in
  ptree_cache_ref := (l,thm)::(!ptree_cache_ref)
end

fun save_ptree_thm save thm =
  if save then
    (insert_ptree_theorem thm;
     remove_oldest_ptree_theorem ();
     thm)
  else
    thm;

fun ptree_thm save tm =
  case best_match_ptree tm of
    SOME (_,thm) =>
      if term_eq (lhsc thm) tm then
        let val (h, t) = Lib.pluck (term_eq tm o fst) (!ptree_cache_ref)
            val _ = ptree_cache_ref := h::t
        in
          thm
        end
      else
        save_ptree_thm save (DEPTH_ARI_CONV thm tm)
  | NONE =>
      let val thm = const_definition (root_const tm)
          val defn = rhsc thm
      in
        if is_add_remove_insert defn then
          let val rwt = DEPTH_ARI_CONV
                          (ptree_thm false (root_const defn)) defn
          in
            save_ptree_thm save
              ((DEPTH_CONV (REWR_CONV thm) THENC DEPTH_ARI_CONV rwt) tm)
          end
        else
          save_ptree_thm save (DEPTH_ARI_CONV thm tm)
      end;

val PTREE_DEFN_CONV = ptree_thm false;

(* ------------------------------------------------------------------------- *)

fun create_ptree_definition v tm =
let val name = fst (dest_var v)
    val thm = Definition.new_definition(name,mk_eq(v, tm))
    val _ = insert_ptree_defn thm
    val _ = HOL_MESG ("Defined new ptree: " ^ name)
in
  REWR_CONV (SYM thm) tm
end;

fun find_const_ptree tm =
  case List.find (fn c => term_eq tm (rhsc (const_definition c)))
                 (!ptree_consts_ref) of
    SOME c => SOME (SYM (const_definition c))
  | NONE => NONE;

fun PTREE_ARI_CONV tm =
let val d = root_const_depth tm in
  if 0 < d andalso ((!ptree_new_defn_depth = ~1) orelse
                    d < !ptree_new_defn_depth) then
    raise ERR "PTREE_ARI_CONV" ""
  else
    if d < 0 then
      CHANGED_CONV (DEPTH_ARI_CONV (Thm.REFL (root_const tm))) tm
    else
      case find_const_ptree tm of
        SOME thm => REWR_CONV thm tm
      | NONE => create_ptree_definition (const_variant tm) tm
end;

val DEPTH_PEEK_THM = prove(
  `(c1 = t) /\ (PEEK t k = c2) ==> (PEEK c1 k = c2)`,
  SRW_TAC [] []);

fun PTREE_PEEK_ARI_CONV tm =
let val (t,k) = dest_peek tm in
  if is_const t andalso not (is_empty t) orelse is_add_remove_insert t then
    let val thm = ptree_thm true t in
      MATCH_MP DEPTH_PEEK_THM
        (CONJ thm (PTREE_PEEK_CONV (mk_peek(rhsc thm,k))))
    end
  else
    PTREE_PEEK_CONV tm
end;

fun mk_ptree_conv2 dest mk conv d_thm tm =
let val (x,t) = dest tm in
  if is_const t andalso not (is_empty t) orelse is_add_remove_insert t then
    let val thm = ptree_thm true t in
      MATCH_MP d_thm (CONJ thm (conv (mk(x,rhsc thm))))
    end
  else
    conv tm
end;

val thm = prove(
  `!f. (c1 = t) /\ (f k t = c2) ==> (f k c1 = c2)`,
  SRW_TAC [] []);

val PTREE_IN_PTREE_ARI_CONV = mk_ptree_conv2
  dest_in_ptree mk_in_ptree PTREE_IN_PTREE_CONV (ISPEC `$IN_PTREE` thm);

val PTREE_EVERY_LEAF_ARI_CONV = mk_ptree_conv2
  dest_every_leaf mk_every_leaf PTREE_EVERY_LEAF_CONV (ISPEC `EVERY_LEAF` thm);

val PTREE_EXISTS_LEAF_ARI_CONV = mk_ptree_conv2
  dest_exists_leaf mk_exists_leaf PTREE_EXISTS_LEAF_CONV
  (ISPEC `EXISTS_LEAF` thm);

val thm = prove(
  `!f. (c1 = t) /\ (f t = c2) ==> (f c1 = c2)`,
  SRW_TAC [] []);

fun mk_ptree_conv dest mk conv d_thm tm =
let val t = dest tm in
  if is_const t andalso not (is_empty t) orelse is_add_remove_insert t then
    let val thm = ptree_thm true t in
      MATCH_MP d_thm (CONJ thm (conv (mk(rhsc thm))))
    end
  else
    conv tm
end;

val PTREE_SIZE_ARI_CONV = mk_ptree_conv
  dest_size mk_size PTREE_SIZE_CONV (ISPEC `SIZE` thm);

val PTREE_DEPTH_ARI_CONV = mk_ptree_conv
  dest_depth mk_depth PTREE_DEPTH_CONV (ISPEC `DEPTH` thm);

(* ------------------------------------------------------------------------- *)

fun add_ptree_convs compset =
 (add_conv (peek_tm,         2, PTREE_PEEK_ARI_CONV)        compset;
  add_conv (add_tm,          2, PTREE_ARI_CONV)             compset;
  add_conv (remove_tm,       2, PTREE_ARI_CONV)             compset;
  add_conv (insert_ptree_tm, 2, PTREE_ARI_CONV)             compset;
  add_conv (size_tm,         1, PTREE_SIZE_ARI_CONV)        compset;
  add_conv (depth_tm,        1, PTREE_DEPTH_ARI_CONV)       compset;
  add_conv (every_leaf_tm,   2, PTREE_EVERY_LEAF_ARI_CONV)  compset;
  add_conv (exists_leaf_tm,  2, PTREE_EXISTS_LEAF_ARI_CONV) compset;
  add_conv (in_ptree_tm,     2, PTREE_IN_PTREE_ARI_CONV)    compset;
  add_conv (is_ptree_tm,     1, PTREE_IS_PTREE_CONV)        compset;
  add_conv (ptree_of_numset_tm, 2, PTREE_OF_NUMSET_CONV)    compset);

val _ = add_funs [PEEK_TRANSFORM];
val _ = add_ptree_convs the_compset;

fun add_ptree_compset compset =
let open listTheory pred_setTheory in
  add_thms [pairTheory.UNCURRY_DEF,
            optionTheory.THE_DEF, optionTheory.option_case_def,
            IS_EMPTY_def, FIND_def, ADD_INSERT, PEEK_TRANSFORM,
            FOLDL, NUMSET_OF_PTREE_def, ADD_LIST_def, LIST_TO_SET_THM,
            PTREE_OF_NUMSET_EMPTY, UNION_PTREE_def, COND_CLAUSES,
            EMPTY_DELETE, DELETE_INSERT, DELETE_UNION] compset;
  add_ptree_convs compset
end;

fun ptree_compset () =
let val compset = new_compset []
    val _ = add_ptree_compset compset
in
  compset
end;

val PTREE_CONV = CBV_CONV (ptree_compset());

(* ------------------------------------------------------------------------- *)

val DEPTH_IS_PTREE_THM = prove(
  `(t = x) /\ (c = x) /\ IS_PTREE t  ==> IS_PTREE c`,
  NTAC 2 (SRW_TAC [] []));

fun add_is_ptree_thm(s,tm,thm1,thm2) =
let val thm3 = EQT_ELIM (PTREE_IS_PTREE_CONV (mk_is_ptree tm))
    val is_ptree_thm = MATCH_MP DEPTH_IS_PTREE_THM (LIST_CONJ [thm1,thm2,thm3])
    val _ = save_thm(s^"_is_ptree_thm", is_ptree_thm)
    val _ = HOL_MESG ("Saved IS_PTREE theorem for new constant " ^ quote s)
in
  add_thms [is_ptree_thm] is_ptree_compset
end handle HOL_ERR _ => HOL_WARNING "patriciaLib" "Define_ptree"
      "Failed to prove IS_PTREE (is_ptree_term_size_limit might be too small).";

fun Define_ptree s tm =
let val d = !ptree_new_defn_depth
    val _ = ptree_new_defn_depth := ~1
    val thm1 = if root_const_depth tm = ~1 then Thm.REFL tm else PTREE_CONV tm
    val _ = ptree_new_defn_depth := d
    val t = rhsc thm1
    val thm2 = Definition.new_definition(s^"_def", mk_eq(mk_var(s,type_of t),t))
    val _ = add_is_ptree_thm(s,tm,thm1,thm2)
    val _ = insert_ptree_defn thm2
    val _ = insert_ptree_theorem thm2
    val _ = remove_oldest_ptree_theorem ()
in
  thm2
end;

fun Define_mk_ptree s tr = Define_ptree s (mk_ptree tr);

val dest_ptree_no_test = dest_ptree;

fun dest_ptree tm =
let val t = dest_ptree_no_test tm in
  if is_ptree t then
    t
  else
    raise ERR "dest_ptree" "not a valid Patricia tree"
end

val is_ptree = Lib.can dest_ptree;

(* ------------------------------------------------------------------------- *)

val _ = Feedback.emit_MESG := emit_mesg

end
