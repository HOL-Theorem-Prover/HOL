structure Halts :> Halts = 
struct

open HolKernel Parse basicHol90Lib;
infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

open arithLib Let_conv NonRecSize;

type thm    = Thm.thm;
type conv     = Abbrev.conv
type tactic = Abbrev.tactic;
type defn   = Defn.defn;

fun ERR f m = 
  HOL_ERR{origin_structure="Halts", origin_function=f, message=m};


fun proper_subterm tm1 tm2 = 
  not(aconv tm1 tm2) andalso Lib.can (find_term (aconv tm1)) tm2;

fun isWFR tm = 
  (#Name(dest_const(fst(strip_comb tm))) = "WF")
  handle HOL_ERR _ => false;

fun foo [] _  = raise ERR "foo" "empty arg."
  | foo _ []  = raise ERR "foo" "empty arg."
  | foo [x] Y = [(x,list_mk_pair Y)]
  | foo X [y] = [(list_mk_pair X, y)]
  | foo (x::rst) (y::rst1) = (x,y)::foo rst rst1;

fun dest tm = 
  let val Ryx = (snd o strip_imp o snd o strip_forall) tm
      val {Rator=Ry, Rand=x} = dest_comb Ryx
      val y = rand Ry
  in 
     foo (strip_pair y) (strip_pair x)
  end;

fun max [] m = m
  | max (h::t) m = max t (if h>m then h else m);

fun copies x =
  let fun repl 0 = []
        | repl n = x::repl (n-1)
  in repl
  end;

fun fill n [] = copies false n
  | fill n (h::t) = h::fill (n-1) t;

fun rectangular L = 
 let val lens = map length L
 in case mk_set lens
     of []  => raise ERR "rectangular" "impossible"
      | [x] => L
      |  _  => let val m = max lens 0
               in map (fill m) L
               end
 end;

fun true_col L = 
      if (all null L) then []
      else all I (map (Lib.trye hd) L)::true_col (map (Lib.trye tl) L);

fun fix [] = []
  | fix (true::t)  = true::map (fn x => false) t
  | fix (false::t) = false::fix t;

fun transp L = 
      if (all null L) then []
      else exists I (map (Lib.trye hd) L)::transp (map (Lib.trye tl) L);

fun projects L0 = 
  let val L = rectangular L0
      val trues = true_col L
  in 
    if exists I trues then fix trues else transp L
  end;

fun nth P [] _ N = rev N
  | nth P (h::t) n N = nth P t (n+1) (if P h then n::N else N);

fun strip_prod_ty [] _ = raise ERR "strip_prod_ty" ""
  | strip_prod_ty [x] ty = [(x,ty)]
  | strip_prod_ty (h::t) ty =
     if is_vartype ty then raise ERR "strip_prod_ty" "expected a product type"
     else case dest_type ty
           of {Tyop="prod", Args=[x,y]} => (h,x)::strip_prod_ty t y
            | _ => raise ERR "strip_prod_ty" "expected a product type"

val numty = mk_type{Tyop="num", Args=[]};
val Zero = Term`0`;
val Plus = mk_const{Name="+", Ty=Type`:num -> num -> num`};
fun mk_plus x y = list_mk_comb(Plus,[x,y]);
fun K0 ty = mk_abs{Bvar=mk_var{Name="v",Ty=ty}, Body=Zero};

fun list_mk_prod_tyl L = 
 let val (front,(b,last)) = front_last L
     val tysize = TypeBase.type_size (TypeBase.theTypeBase())
     val last' = (if b then tysize else K0) last
  in
  itlist (fn (b,ty1) => fn M => 
     let val x = mk_var{Name="x",Ty=ty1}
         val y = mk_var{Name="y",Ty=fst(dom_rng (type_of M))}
     in
       mk_pabs {varstruct=mk_pair{fst=x,snd=y},
                 body = mk_plus (mk_comb{Rator=(if b then tysize else K0) ty1,
                                               Rand=x})
                                (mk_comb{Rator=M,Rand=y})}
     end) front last'
 end;


(*---------------------------------------------------------------------------*
 * The general idea behind this is to try 2 termination measures. The first  *
 * measure takes the size of all subterms meeting the following criteria:    *
 * argument i in a recursive call must be a proper subterm of argument i     *
 * in the head call. For i, if at least one TC meets this criteria, then     *
 * position i will be measured. This measure should catch all primitive      *
 * recursions, and primitive recursive tail recursions. Because of           *
 * various syntactic limitations to the form of primitive recursions in HOL  *
 * e.g. not allowing varstructs, this should be useful. Also, this step      *
 * catches some non-prim.rec tail recursions, see the examples.              *
 *                                                                           *
 * The second measure is just the total size of the arguments.               *
 *---------------------------------------------------------------------------*)

local open Defn 
in
fun guessR defn =
 if null (tcs_of defn) then []
  else 
  case reln_of defn
   of NONE => []
    | SOME R => 
       let val domty = fst(dom_rng(type_of R))
           val (_,tcs) = Lib.pluck isWFR (tcs_of defn)
           val matrix = map dest tcs
           val check1 = map (map (uncurry proper_subterm)) matrix 
           val chf = projects check1
           val domtyl = strip_prod_ty chf domty
           val domty0 = list_mk_prod_tyl domtyl
       in
          [Term`measure ^domty0`,
           Term`measure ^(TypeBase.type_size (TypeBase.theTypeBase()) domty)`]
       end
end;

local open Defn
in
fun try_proof def tac r =
   let val def' = set_reln def r
       val tcs = tcs_of def'
       val thm = prove(list_mk_conj tcs, tac)
       val thml = CONJUNCTS thm
    in 
       elim_tcs def' thml
    end
fun proveTotal0 tac def =
  case guessR def
    of [] => def
     | cands => Lib.tryfind (try_proof def tac) cands
end;

(*---------------------------------------------------------------------------
      Terribly naive, but it still gets a lot.
 ---------------------------------------------------------------------------*)

fun simplify_conv tm =
 (Rewrite.REWRITE_CONV
    [prim_recTheory.WF_measure, prim_recTheory.WF_LESS,
     prim_recTheory.measure_def, relationTheory.inv_image_def]
  THENC REDEPTH_CONV Let_conv.GEN_BETA_CONV
  THENC Rewrite.REWRITE_CONV 
          (pairTheory.pair_rws @
           mapfilter (#2 o valOf o TypeBase.size_of) 
               (TypeBase.listItems (TypeBase.theTypeBase())))
  THENC REDEPTH_CONV BETA_CONV
  THENC Rewrite.REWRITE_CONV [arithmeticTheory.ADD_CLAUSES])  tm;

fun prover g =
(CONV_TAC simplify_conv
  THEN REPEAT STRIP_TAC
  THEN REPEAT (POP_ASSUM (fn th => 
       if arithSimps.is_arith (concl th)
       then MP_TAC th else ALL_TAC))
  THEN CONV_TAC arithLib.ARITH_CONV) g;

val proveTotal = proveTotal0 prover;


(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 Examples.

val Define = Count.apply bossLib.Define;

val gcd_def = 
  Define 
    `(gcd 0 y = y)  /\
     (gcd (SUC x) 0 = SUC x) /\
     (gcd (SUC x) (SUC y) = 
         if y<=x then gcd (x-y)   (SUC y) 
                 else gcd (SUC x) (y-x))`;

val gcd_def = 
  Define 
    `(gcd (0,y)          = y)      /\
     (gcd (SUC x, 0)     = SUC x)  /\
     (gcd (SUC x, SUC y) = ((y<=x) => gcd (x-y, SUC y) 
                                   |  gcd (SUC x, y-x)))`;

val Tot_def = 
  Define
    `(Tot [] = 0) /\
     (Tot (CONS 0 t) = Tot t) /\
     (Tot (CONS (SUC n) t) = 1 + Tot (CONS n t))`;

val Tot_def = 
  Define
    `(Tot [] = 0) /\
     (Tot (CONS 0 t) = Tot t) /\
     (Tot (CONS n t) = 1 + Tot (CONS (n-1) t))`;

val fact_cond_def = Define `fact x = ((x = 0) => 1 | x * fact(x-1))`;

val fact_pattern_def = Define
   `(Fact 0 = 1) /\
    (Fact (SUC x) = Fact x * SUC x)`;

val fib_def = Define
   `(Fib 0 = 1) /\
    (Fib (SUC 0) = 1) /\
    (Fib (SUC(SUC x)) = Fib x + Fib (SUC x))`;

val smaller_def = Define
  `(smaller((0,i), z) = (i:num))    /\
   (smaller((SUC x, i), (0,j)) = j) /\
   (smaller((SUC x, i), (SUC y,j)) = 
      ((SUC y = i) => i
     | (SUC x = j) => j
     | smaller((x,i), (y,j))))`;

val map2_def = Define
  `(map2(f, ([]:'a list),(L:'b list)) = ([]:'c list)) /\
   (map2(f, CONS h t,   []) = [])                     /\
   (map2(f, CONS h1 t1, CONS h2 t2) = CONS (f h1 h2) (map2 (f, t1, t2)))`;

val sorted_def = Define
   `(sorted (R, [])  = T) /\
    (sorted (R, [x]) = T) /\   
    (sorted (R, CONS x (CONS y rst)) = R x y /\ sorted (R, CONS y rst))`;

val filter_def = 
 Define
  `(filter P [] = []) /\
   (filter P (CONS h t) = (P h => CONS h (filter P t) | filter P t))`;

val qsort_def = Define
   `(qsort(ord,[]) = []) /\
    (qsort(ord, CONS x rst) = 
      APPEND (qsort(ord,filter($~ o ord x) rst))
             (CONS x (qsort(ord,filter(ord x) rst))))`;

(*
infix &&;
g`!l f P. list_size f (filter P l) <= list_size f l`;
e (Induct THEN RW_TAC arith_ss [listTheory.list_size, filter_def]);
... and on to Waltherism
*)

val mem_def = Define `(mem x [] = F) /\ (mem x (CONS h t) = (x=h) \/ mem x t)`;
val variant_def = Define `variant(x, L) = (mem x L => variant(x+1, L) | x)`;

(* Destructor style -- fails to prove termination *)
Define `Gate (l:num list,x) = 
           if l=[] then  1 
           else let rst = Gate (TL l, x) in FST (HD l, x))`;

(* Constructor style. *)
Define `(Gate ([],x) = 1)
     /\ (Gate (CONS h t, x) = let rst = Gate (t, x) in (h+rst))`;

val div_def = Define
   `(div(0,x) = (0,0)) /\
    (div(SUC x, y) = let (q,r) = div(x,y)
                     in (y <= SUC r => (SUC q,0) 
                        | (*otherwise*) (q, SUC r)))`;

(* Test nested lets *)
val div_def = Define
   `(Div(0,x) = (0,0)) /\
    (Div(SUC x, y) = let q = FST(Div(x,y)) 
                     and r = SND(Div(x,y))
                     in (y <= SUC r => (SUC q,0) 
                        | (*otherwise*) (q, SUC r)))`;

val part_def = 
Define
     `(part (P, [], l1,l2)         = (l1,l2)) /\
      (part (P, CONS h rst, l1,l2) = (P h => part(P,rst, CONS h l1, l2)
                                          |  part(P,rst,  l1,  CONS h l2)))`;

(*---------------------------------------------------------------------------*
 * new_recursive_definition gets invoked.                                    *
 *---------------------------------------------------------------------------*)
val part_def = 
   Define
       `(part P [] l1 l2 = (l1,l2)) /\
        (part P (CONS h rst) l1 l2 =
           (P h => part P rst (CONS h l1) l2
                |  part P rst  l1 (CONS h l2)))`;


(*---------------------------------------------------------------------------*
 * Quicksort again.                                                          *
 *---------------------------------------------------------------------------*)
val qsort_def = Define
   `(qsort ord [] = []) /\
    (qsort ord (CONS x rst) = 
       let (l1,l2) = part (ord x) rst [] []
       in 
        APPEND (qsort ord l1) 
               (CONS x (qsort ord l2)))`;


(*---------------------------------------------------------------------------*
 * Dutch National Flag by functional programming. Similar to bubble sort.    *
 *---------------------------------------------------------------------------*)
bossLib.Hol_datatype `colour = Red | White | Blue`;

val Swap_def =
 Define 
 `(Swap [] = NONE)        /\ 
  (Swap (CONS White (CONS Red rst)) =   SOME(CONS Red (CONS White rst)))  /\ 
  (Swap (CONS Blue  (CONS Red rst)) =   SOME(CONS Red (CONS Blue rst)))   /\ 
  (Swap (CONS Blue  (CONS White rst)) = SOME(CONS White (CONS Blue rst))) /\ 
  (Swap (CONS x rst) = option_APPLY (CONS x) (Swap rst))`;

val Flag = 
 Define `Flag list = option_case list (\l. Flag l) (Swap list)`;

(* Note that eta-expansion "\l. Flag l" needed in definition of Flag.  *)


(* Binary trees. *)
bossLib.Hol_datatype `btree = Leaf of 'a
                            | Brh of 'a => btree => btree`;
 
(* prim. rec. *)
Define 
   `(upheap R w (Leaf x) = Brh w (Leaf x) (Leaf x)) /\
    (upheap R w (Brh v p q) =
         (R w v => Brh w (upheap R v q) p
                 | Brh v (upheap R w q) p))`;

(* Not sure if this actually does anything useful. *)
Define
   `(merge_heap R (Leaf x) b = b)                         
 /\ (merge_heap R (Brh v b1 b2) (Leaf x) = Brh v b1 b2) 
 /\ (merge_heap R (Brh v b1 b2) (Brh w c1 c2) 
       = if R v w 
         then Brh v (merge_heap R b1 b2) (Brh w c1 c2)
         else Brh w (Brh v b1 b2) (merge_heap R c1 c2))`;

(*---------------------------------------------------------------------------*
 * This one is more difficult, because you need to know a relation between   *
 * term_size and list_size. Would work with multiset ordering.               *
 *---------------------------------------------------------------------------*)

val V_def = 
Define
  `(V [] acc = acc)
/\ (V (CONS(Leaf s) rst) acc        = V rst (CONS [Leaf s] acc)) 
/\ (V (CONS(Brh x tm1 tm2) rst) acc = V (CONS tm1 (CONS tm2 rst)) acc)`;

TypeBase.type_size (TypeBase.theTypeBase()) (Type`:'a btree list`);

(*---------------------------------------------------------------------------*
 * This one is difficult because the size of the tree is not changed.        *
 * Provable with the interpretation                                          *
 *                                                                           *
 *    Int (Leaf) = 0                                                         *
 *    Int (Brh x y) = 2 * Int x + Int y + 1                                  *
 *---------------------------------------------------------------------------*)

val Lin_def = 
Define`(Lin (Leaf x) = Leaf x) 
  /\   (Lin (Brh a (Leaf x) bt) = Brh a (Leaf x) (Lin bt))
  /\   (Lin (Brh a (Brh x bt1 bt2) bt) = Lin (Brh x bt1 (Brh a bt2 bt)))`;


Define`assoc x (CONS (x1,y) t) = if x=x1 then y else assoc x t`;

Define 
   `(Maj [] (winner,lead) = (winner,lead))
 /\ (Maj (CONS h t) (leader,0) = 
        if h=leader then Maj t (leader,1) else Maj t (h,1))
 /\ (Maj (CONS h t) (leader, SUC m) = 
        if h=leader then Maj t (leader, SUC(SUC m)) else Maj t (leader, m))`;

(* Used to fail *)
Define 
   `(Maj [] (winner,lead)      = (winner,lead))
 /\ (Maj (CONS h t) (leader,0) = Maj t (h=leader => (leader,1) | (h,1)))
 /\ (Maj (CONS h t) (leader, SUC m) = 
        (h=leader => Maj t (leader, SUC(SUC m))
                  |  Maj t (leader, m)))`;
(* Used to fail *)
Define 
   `(Maj [] (winner,lead)      = (winner,lead))
 /\ (Maj (CONS h t) (leader,0) = Maj t (h=leader => (leader,1) | (h,1)))
 /\ (Maj (CONS h t) (leader, SUC m) =
       Maj t (leader, (h=leader => SUC(SUC m) | m)))`;

(* Used to fail *)
Define 
   `(Maj [] (winner,lead)      = (winner,lead))
 /\ (Maj (CONS h t) (leader,0) = Maj t ((h=leader => leader | h),1))
 /\ (Maj (CONS h t) (leader, SUC m) =
       Maj t (leader, (h=leader => SUC(SUC m) | m)))`;

Define 
   `(Maj [] (winner,lead) = (winner,lead))
 /\ (Maj (CONS h t) (_,0) = Maj t (h,1))
 /\ (Maj (CONS h t) (leader, SUC m) =
       Maj t (leader, (h=leader => SUC(SUC m) | m)))`;


Define`step x = x`;
val SM =
Define
  `SM s n = if n=0 then s else SM (step s) (n-1)`;

*)

end;
