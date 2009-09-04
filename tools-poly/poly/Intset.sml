(* Intset -- modified for Moscow ML from SML/NJ library v. 0.2.
 *
 * COPYRIGHT (c) 1993 by AT&T Bell Laboratories.
 * See file mosml/copyrght/copyrght.att for details.
 *
 * This code was adapted from Stephen Adams' binary tree implementation
 * of applicative integer sets.
 *
 *  Copyright 1992 Stephen Adams.
 *
 *  This software may be used freely provided that:
 *    1. This copyright notice is attached to any copy, derived work,
 *       or work including all or part of this software.
 *    2. Any derived work must contain a prominent notice stating that
 *       it has been altered from the original.
 *
 *  Altered to conform to SML library interface - Emden Gansner
 *
 *
 * Name(s): Stephen Adams.
 * Department, Institution: Electronics & Computer Science,
 *    University of Southampton
 * Address:  Electronics & Computer Science
 *           University of Southampton
 *           Southampton  SO9 5NH
 *           Great Britian
 * E-mail:   sra@ecs.soton.ac.uk
 *
 * Comments:
 *
 *   1.  The implementation is based on Binary search trees of Bounded
 *       Balance, similar to Nievergelt & Reingold, SIAM J. Computing
 *       2(1), March 1973.  The main advantage of these trees is that
 *       they keep the size of the tree in the node, giving a constant
 *       time size operation.
 *
 *   2.  The bounded balance criterion is simpler than N&R's alpha.
 *       Simply, one subtree must not have more than `weight' times as
 *       many elements as the opposite subtree.  Rebalancing is
 *       guaranteed to reinstate the criterion for weight>2.23, but
 *       the occasional incorrect behaviour for weight=2 is not
 *       detrimental to performance.
 *
 *   3.  There are two implementations of union.  The default,
 *       hedge_union, is much more complex and usually 20% faster.  I
 *       am not sure that the performance increase warrants the
 *       complexity (and time it took to write), but I am leaving it
 *       in for the competition.  It is derived from the original
 *       union by replacing the split_lt(gt) operations with a lazy
 *       version. The `obvious' version is called old_union.
 *
 *   4.  Most time is spent in T', the rebalancing constructor.  If my
 *       understanding of the output of *<file> in the sml batch
 *       compiler is correct then the code produced by NJSML 0.75
 *       (sparc) for the final case is very disappointing.  Most
 *       invocations fall through to this case and most of these cases
 *       fall to the else part, i.e. the plain contructor,
 *       T(v,ln+rn+1,l,r).  The poor code allocates a 16 word vector
 *       and saves lots of registers into it.  In the common case it
 *       then retrieves a few of the registers and allocates the 5
 *       word T node.  The values that it retrieves were live in
 *       registers before the massive save.
 *)

structure Intset :> Intset =
struct

fun wt (i : int) = 3 * i

datatype Set = E | T of int * int * Set * Set

fun size E = 0
  | size (T(_,n,_,_)) = n

(*fun N(v,l,r) = T(v,1+size(l)+size(r),l,r)*)
fun N(v,E,              E)               = T(v,1,E,E)
  | N(v,E,              r as T(_,n,_,_)) = T(v,n+1,E,r)
  | N(v,l as T(_,n,_,_),E)               = T(v,n+1,l,E)
  | N(v,l as T(_,n,_,_),r as T(_,m,_,_)) = T(v,n+m+1,l,r)

fun single_L (a,x,T(b,_,y,z)) = N(b,N(a,x,y),z)
  | single_L _ = raise Match
fun single_R (b,T(a,_,x,y),z) = N(a,x,N(b,y,z))
  | single_R _ = raise Match
fun double_L (a,w,T(c,_,T(b,_,x,y),z)) = N(b,N(a,w,x),N(c,y,z))
  | double_L _ = raise Match
fun double_R (c,T(a,_,w,T(b,_,x,y)),z) = N(b,N(a,w,x),N(c,y,z))
  | double_R _ = raise Match

fun T' (v,E,E) = T(v,1,E,E)
  | T' (v,E,r as T(_,_,E,E))     = T(v,2,E,r)
  | T' (v,l as T(_,_,E,E),E)     = T(v,2,l,E)

  | T' (p as (_,E,T(_,_,T(_,_,_,_),E))) = double_L p
  | T' (p as (_,T(_,_,E,T(_,_,_,_)),E)) = double_R p

  (* these cases almost never happen with small weight*)
  | T' (p as (_,E,T(_,_,T(_,ln,_,_),T(_,rn,_,_)))) =
	if ln<rn then single_L p else double_L p
  | T' (p as (_,T(_,_,T(_,ln,_,_),T(_,rn,_,_)),E)) =
	if ln>rn then single_R p else double_R p

  | T' (p as (_,E,T(_,_,E,_)))  = single_L p
  | T' (p as (_,T(_,_,_,E),E))  = single_R p

  | T' (p as (v,l as T(lv,ln,ll,lr),r as T(rv,rn,rl,rr))) =
	if rn>=wt ln then (*right is too big*)
	    let val rln = size rl
		val rrn = size rr
	    in
		if rln < rrn then  single_L p  else  double_L p
	    end

	else if ln>=wt rn then  (*left is too big*)
	    let val lln = size ll
		val lrn = size lr
	    in
		if lrn < lln then  single_R p  else  double_R p
	    end

	else
         T(v,ln+rn+1,l,r)

fun addt t x =
    let fun h E = T(x,1,E,E)
	  | h (set as T(v,_,l,r)) =
	    if x<v then T'(v, h l, r)
	    else if x>v then T'(v, l, h r)
  	    else set
    in h t end

fun concat3 E v r = addt r v
  | concat3 l v E = addt l v
  | concat3 (l as T(v1,n1,l1,r1)) v (r as T(v2,n2,l2,r2)) =
    if wt n1 < n2 then T'(v2, concat3 l v l2,r2)
    else if wt n2 < n1 then T'(v1,l1,concat3 r1 v r)
    else N(v,l,r)

fun split_lt E x = E
  | split_lt (t as T(v,_,l,r)) x =
    if v>x then split_lt l x
    else if v<x then concat3 l v (split_lt r x)
    else l

fun split_gt E x = E
  | split_gt (t as T(v,_,l,r)) x =
    if v<x then split_gt r x
    else if v>x then concat3 (split_gt l x) v r
    else r

fun min (T(v,_,E,_)) = v
  | min (T(v,_,l,_)) = min l
  | min _            = raise Match
and delete' (E,r) = r
  | delete' (l,E) = l
  | delete' (l,r) =
    let val min_elt = min r
    in T'(min_elt,l,delmin r) end
and delmin (T(_,_,E,r)) = r
  | delmin (T(v,_,l,r)) = T'(v,delmin l,r)
  | delmin _ = raise Match

fun concat E  s2 = s2
  | concat s1 E  = s1
  | concat (t1 as T(v1,n1,l1,r1)) (t2 as T(v2,n2,l2,r2)) =
	if wt n1 < n2 then T'(v2, concat t1 l2, r2)
	else if wt n2 < n1 then T'(v1,l1, concat r1 t2)
	     else T'(min t2,t1, delmin t2)

type  intset = Set

exception NotFound

val empty = E

fun singleton x = T(x,1,E,E)

local
    fun trim lo hi E = E
      | trim lo hi (s as T(v,_,l,r)) =
	if  v<=lo  then  trim lo hi r
	else if  v>=hi  then  trim lo hi l
	else  s

    fun uni_bd s E lo hi = s
      | uni_bd E (T(v,_,l,r)) lo hi =
	concat3 (split_gt l lo) v (split_lt r hi)
      | uni_bd (T(v,_,l1,r1)) (s2 as T(v2,_,l2,r2)) lo hi =
	concat3 (uni_bd l1 (trim lo v s2) lo v)
		v
		(uni_bd r1 (trim v hi s2) v hi)
    (* inv:  lo < v < hi *)

   (*all the other versions of uni and trim are
   specializations of the above two functions with
   lo=-infinity and/or hi=+infinity *)

    fun trim_lo _ E = E
      | trim_lo lo (s as T(v,_,_,r)) =
	if v<=lo then trim_lo lo r else s
    fun trim_hi _ E = E
      | trim_hi hi (s as T(v,_,l,_)) =
	if v>=hi then trim_hi hi l else s

    fun uni_hi s E hi = s
      | uni_hi E (T(v,_,l,r)) hi =
	concat3 l v (split_lt r hi)
      | uni_hi (T(v,_,l1,r1)) (s2 as T(v2,_,l2,r2)) hi =
	concat3 (uni_hi l1 (trim_hi v s2) v)
		v
		(uni_bd r1 (trim v hi s2) v hi)

    fun uni_lo s E lo = s
      | uni_lo E (T(v,_,l,r)) lo =
	concat3 (split_gt l lo) v r
      | uni_lo (T(v,_,l1,r1)) (s2 as T(v2,_,l2,r2)) lo =
	concat3 (uni_bd l1 (trim lo v s2) lo v)
		v
		(uni_lo r1 (trim_lo v s2) v)

    fun uni (s,E) = s
      | uni (E,s as T(v,_,l,r)) = s
      | uni (T(v,_,l1,r1), s2 as T(v2,_,l2,r2)) =
	concat3 (uni_hi l1 (trim_hi v s2) v)
		v
		(uni_lo r1 (trim_lo v s2) v)
in
    val union = uni
end

fun addList (s,l) = List.foldl (fn (i,s) => addt s i) s l

fun add(s, i) = addt s i

fun difference (E,s)  = E
  | difference (s,E)  = s
  | difference (s, T(v,_,l,r)) =
    let val l2 = split_lt s v
	val r2 = split_gt s v
    in
	concat (difference(l2,l)) (difference(r2,r))
    end

fun membert set x =
    let fun mem E = false
	  | mem (T(v,_,l,r)) =
	    if x<v then mem l else if x>v then mem r else true
    in mem set end

fun member (set,x) = membert set x

(*fun intersection (a,b) = difference(a,difference(a,b))*)

fun intersection (E,_) = E
  | intersection (_,E) = E
  | intersection (s, T(v,_,l,r)) =
    let val l2 = split_lt s v
	val r2 = split_gt s v
    in
	if membert s v then
	    concat3 (intersection(l2,l)) v (intersection(r2,r))
	else
	    concat (intersection(l2,l)) (intersection(r2,r))
    end

fun numItems E = 0
  | numItems (T(_,n,_,_)) = n

fun isEmpty E = true
  | isEmpty _ = false

fun delete (E,x) = raise NotFound
  | delete (set as T(v,_,l,r),x) =
    if x<v then T'(v,delete(l,x),r)
    else if x>v then T'(v,l,delete(r,x))
    else delete'(l,r)

fun foldr f base set =
    let	fun fold' base E = base
	  | fold' base (T(v,_,l,r)) = fold' (f(v, fold' base r)) l
    in fold' base set end

fun foldl f base set =
    let	fun fold' base E = base
	  | fold' base (T(v,_,l,r)) = fold' (f(v, fold' base l)) r
    in fold' base set end

fun app f set =
    let	fun app' E = ()
	  | app'(T(v,_,l,r)) = (app' l; f v; app' r)
    in app' set end

fun revapp f set =
    let	fun app' E = ()
	  | app'(T(v,_,l,r)) = (app' r; f v; app' l)
    in app' set end

local
    (* true if every item in t is in t' *)
    fun treeIn t t' =
	let
	    fun isIn E = true
	      | isIn (T(v,_,E,E)) = membert t' v
	      | isIn (T(v,_,l,E)) =
		membert t' v andalso isIn l
	      | isIn (T(v,_,E,r)) =
		membert t' v andalso isIn r
	      | isIn (T(v,_,l,r)) =
		membert t' v andalso isIn l andalso isIn r
        in
	    isIn t
        end
in
    fun isSubset (E,_) = true
      | isSubset (_,E) = false
      | isSubset (t as T(_,n,_,_),t' as T(_,n',_,_)) =
	(n<=n') andalso treeIn t t'

    fun equal (E,E) = true
      | equal (t as T(_,n,_,_),t' as T(_,n',_,_)) =
	(n=n') andalso treeIn t t'
      | equal _ = false
end

fun find p set =
    let fun h E            = NONE
	  | h (T(v,_,l,r)) =
	    if p v then SOME v
	    else case h l of
		NONE => h r
	      | a => a
    in h set end;

fun listItems set = foldr (op::) [] set

end
