(* Merging and sorting *)

structure Sort: SORT =
struct

(* Merge two lists according to the given predicate.
   Assuming the two argument lists are sorted according to the
   predicate, [merge] returns a sorted list containing the elements
   from the two lists. The behavior is undefined if the two
   argument lists were not sorted. *)
fun merge lte =
    let fun loop ([],ys) = ys
	  | loop (xs,[]) = xs
	  | loop ((xs as x::xr),(ys as y::yr)) =
	      if lte(x,y) then x :: loop(xr,ys) 
	      else y :: loop(xs,yr)
    in  loop
    end

(* Sort a list in increasing order according to an ordering predicate.
   The predicate should return [true] if its first argument is
   less than or equal to its second argument. The original order of elements
   comparing equal is maintained (unlike ListMergeSort). *)
fun sort (lte,l) =
    let fun initList [] = []
	  | initList [e] = [[e]]
	  | initList (x1::x2::xs) =
	      (if lte(x1,x2) then [x1, x2] else [x2, x1]) :: initList xs
	fun merge2 (xs1::xs2::xss) = merge lte (xs1,xs2) :: merge2 xss
	  | merge2 x = x
	fun mergeAll [] = []
	  | mergeAll [xs] = xs
	  | mergeAll xss = mergeAll (merge2 xss)
    in  mergeAll(initList l)
    end


end (* structure Sort *)
