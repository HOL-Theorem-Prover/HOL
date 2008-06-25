structure Binarymap :> Binarymap =
struct

(* Binarymap -- modified for Moscow ML
 * from SML/NJ library v. 0.2 file binary-dict.sml.
 * COPYRIGHT (c) 1993 by AT&T Bell Laboratories.
 * See file mosml/copyrght/copyrght.att for details.
 *
 * This code was adapted from Stephen Adams' binary tree implementation
 * of applicative integer sets.
 *
 *   Copyright 1992 Stephen Adams.
 *
 *    This software may be used freely provided that:
 *      1. This copyright notice is attached to any copy, derived work,
 *         or work including all or part of this software.
 *      2. Any derived work must contain a prominent notice stating that
 *         it has been altered from the original.
 *
 *
 *   Name(s): Stephen Adams.
 *   Department, Institution: Electronics & Computer Science,
 *      University of Southampton
 *   Address:  Electronics & Computer Science
 *             University of Southampton
 *	     Southampton  SO9 5NH
 *	     Great Britian
 *   E-mail:   sra@ecs.soton.ac.uk
 *
 *   Comments:
 *
 *     1.  The implementation is based on Binary search trees of Bounded
 *         Balance, similar to Nievergelt & Reingold, SIAM J. Computing
 *         2(1), March 1973.  The main advantage of these trees is that
 *         they keep the size of the tree in the node, giving a constant
 *         time size operation.
 *
 *     2.  The bounded balance criterion is simpler than N&R's alpha.
 *         Simply, one subtree must not have more than `weight' times as
 *         many elements as the opposite subtree.  Rebalancing is
 *         guaranteed to reinstate the criterion for weight>2.23, but
 *         the occasional incorrect behaviour for weight=2 is not
 *         detrimental to performance.
 *
 *)

exception NotFound

fun wt (i : int) = 3 * i

datatype ('key, 'a) dict =
    DICT of ('key * 'key -> order) * ('key, 'a) tree
and ('key, 'a) tree =
    E
  | T of {key   : 'key,
	  value : 'a,
	  cnt   : int,
	  left  : ('key, 'a) tree,
	  right : ('key, 'a) tree}

fun treeSize E            = 0
  | treeSize (T{cnt,...}) = cnt

fun numItems (DICT(_, t)) = treeSize t

local
    fun N(k,v,E,E) = T{key=k,value=v,cnt=1,left=E,right=E}
      | N(k,v,E,r as T n) = T{key=k,value=v,cnt=1+(#cnt n),left=E,right=r}
      | N(k,v,l as T n,E) = T{key=k,value=v,cnt=1+(#cnt n),left=l,right=E}
      | N(k,v,l as T n,r as T n') =
          T{key=k,value=v,cnt=1+(#cnt n)+(#cnt n'),left=l,right=r}

    fun single_L (a,av,x,T{key=b,value=bv,left=y,right=z,...}) =
          N(b,bv,N(a,av,x,y),z)
      | single_L _ = raise Match
    fun single_R (b,bv,T{key=a,value=av,left=x,right=y,...},z) =
          N(a,av,x,N(b,bv,y,z))
      | single_R _ = raise Match
    fun double_L (a,av,w,T{key=c,value=cv,
			   left=T{key=b,value=bv,left=x,right=y,...},
			   right=z,...}) =
          N(b,bv,N(a,av,w,x),N(c,cv,y,z))
      | double_L _ = raise Match
    fun double_R (c,cv,T{key=a,value=av,left=w,
			 right=T{key=b,value=bv,left=x,right=y,...},...},z) =
          N(b,bv,N(a,av,w,x),N(c,cv,y,z))
      | double_R _ = raise Match

    fun T' (k,v,E,E) = T{key=k,value=v,cnt=1,left=E,right=E}
      | T' (k,v,E,r as T{right=E,left=E,...}) =
          T{key=k,value=v,cnt=2,left=E,right=r}
      | T' (k,v,l as T{right=E,left=E,...},E) =
          T{key=k,value=v,cnt=2,left=l,right=E}

      | T' (p as (_,_,E,T{left=T _,right=E,...})) = double_L p
      | T' (p as (_,_,T{left=E,right=T _,...},E)) = double_R p

        (* these cases almost never happen with small weight*)
      | T' (p as (_,_,E,T{left=T{cnt=ln,...},right=T{cnt=rn,...},...})) =
          if ln < rn then single_L p else double_L p
      | T' (p as (_,_,T{left=T{cnt=ln,...},right=T{cnt=rn,...},...},E)) =
          if ln > rn then single_R p else double_R p

      | T' (p as (_,_,E,T{left=E,...})) = single_L p
      | T' (p as (_,_,T{right=E,...},E)) = single_R p

      | T' (p as (k,v,l as T{cnt=ln,left=ll,right=lr,...},
                      r as T{cnt=rn,left=rl,right=rr,...})) =
          if rn >= wt ln then (*right is too big*)
            let val rln = treeSize rl
                val rrn = treeSize rr
            in
              if rln < rrn then  single_L p  else  double_L p
            end

          else if ln >= wt rn then  (*left is too big*)
            let val lln = treeSize ll
                val lrn = treeSize lr
            in
              if lrn < lln then  single_R p  else  double_R p
            end

          else T{key=k,value=v,cnt=ln+rn+1,left=l,right=r}

    local
      fun min (T{left=E,key,value,...}) = (key,value)
        | min (T{left,...}) = min left
        | min _ = raise Match

      fun delmin (T{left=E,right,...}) = right
        | delmin (T{key,value,left,right,...}) =
	  T'(key,value,delmin left,right)
        | delmin _ = raise Match
    in
      fun delete' (E,r) = r
        | delete' (l,E) = l
        | delete' (l,r) = let val (mink,minv) = min r
			  in T'(mink,minv,l,delmin r) end
    end
in
    fun mkDict cmpKey = DICT(cmpKey, E)

    fun insert (DICT (cmpKey, t),x,v) =
	let fun ins E = T{key=x,value=v,cnt=1,left=E,right=E}
	      | ins (T(set as {key,left,right,value,...})) =
		case cmpKey (key,x) of
		    GREATER => T'(key,value,ins left,right)
		  | LESS    => T'(key,value,left,ins right)
		  | _       =>
			T{key=x,value=v,left=left,right=right,cnt= #cnt set}
	in DICT(cmpKey, ins t) end

    fun find (DICT(cmpKey, t), x) =
	let fun mem E = raise NotFound
	      | mem (T(n as {key,left,right,...})) =
		case cmpKey (x,key) of
		    GREATER => mem right
		  | LESS    => mem left
		  | _       => #value n
	in mem t end

    fun peek arg = (SOME(find arg)) handle NotFound => NONE

    fun remove (DICT(cmpKey, t), x) =
	let fun rm E = raise NotFound
	      | rm (set as T{key,left,right,value,...}) =
		(case cmpKey (key,x) of
		     GREATER => let val (left', v) = rm left
				in (T'(key, value, left', right), v) end
		   | LESS    => let val (right', v) = rm right
				in (T'(key, value, left, right'), v) end
		   | _       => (delete'(left,right),value))
	    val (newtree, valrm) = rm t
	in (DICT(cmpKey, newtree), valrm) end

    fun listItems (DICT(_, d)) =
	let fun d2l E res = res
	      | d2l (T{key,value,left,right,...}) res =
		d2l left ((key,value) :: d2l right res)
	in d2l d [] end

    fun revapp f (DICT(_, d)) = let
      fun a E = ()
        | a (T{key,value,left,right,...}) = (a right; f(key,value); a left)
      in a d end

    fun app f (DICT(_, d)) = let
      fun a E = ()
        | a (T{key,value,left,right,...}) = (a left; f(key,value); a right)
      in a d end

    fun foldr f init (DICT(_, d)) = let
      fun a E v = v
        | a (T{key,value,left,right,...}) v = a left (f(key,value,a right v))
      in a d init end

    fun foldl f init (DICT(_, d)) = let
      fun a E v = v
        | a (T{key,value,left,right,...}) v = a right (f(key,value,a left v))
      in a d init end

    fun map f (DICT(cmpKey, d)) = let
      fun a E = E
        | a (T{key,value,left,right,cnt}) = let
            val left' = a left
            val value' = f(key,value)
            in
              T{cnt=cnt, key=key,value=value',left = left', right = a right}
            end
      in DICT(cmpKey, a d) end

    fun transform f (DICT(cmpKey, d)) =
	let fun a E = E
	      | a (T{key,value,left,right,cnt}) =
		let val left' = a left
		in
		    T{cnt=cnt, key=key, value=f value, left = left',
		      right = a right}
		end
      in DICT(cmpKey, a d) end
end

end (* struct *)