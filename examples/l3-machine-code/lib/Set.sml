(* -------------------------------------------------------------------------
   Set
   ------------------------------------------------------------------------- *)

structure Set :> Set =
struct

   fun mem (i, l) = List.exists (fn x => x = i) l

   fun insert (i, l) = if mem (i, l) then l else i :: l

   fun mk [] = []
     | mk (h :: t) = if mem (h, t) then mk t else h :: mk t

   fun diff (s1, s2) = List.filter (fn x => not (mem (x, s2))) s1
   fun intersect (s1, s2) = List.filter (fn x => mem (x, s2)) s1
   fun isSubset (s1, s2) = List.all (fn x => mem (x, s2)) s1

   fun equal (s1, s2) =
      List.length s1 = List.length s2 andalso intersect (s1, s2) = s1

   fun union ([], s) = s
     | union (s, []) = s
     | union (h :: t, s) = union (t, insert (h, s))

end (* structure Set *)
