(*---------------------------------------------------------------------------

     A database of lemmas. This is currently accessible in the
     following ways: 

       - strings used to denote (part of) the name of the binding, 
         or theory of interest. Case is not significant.

       - matching (first order) on the term structure of theorems.

       - a general matcher on the term structure of theorems.

 ---------------------------------------------------------------------------*)

structure DB :> DB =
struct

 type term = Term.term
 type thm = Thm.thm

 open Binarymap;

 datatype class = Def | Axm | Thm
 type data = (string * string) * (thm * class)

 fun comp ((s1,s2),(t1,t2)) =
   case String.compare(s1,t1)
    of EQUAL => String.compare(s2,t2)
     | x => x;

 val empty = 
   mkDict comp: (string*string, (string*string)*(thm*class)) dict;

 val dBref = ref empty
 fun lemmas() = !dBref;

(* Map keys to canonical case *)

 fun toLower s = 
   let open Char CharVector
   in tabulate(size s, fn i => toLower(sub(s, i))) end

 fun add ((p as (s1,s2)),x) db = 
    let val key = (toLower s1, toLower s2)
    in insert (db,key,(p,x))
    end;


 local fun occurs s1 s2 =
        not(Substring.isEmpty (#2(Substring.position s1 (Substring.all s2))))
 in
 fun thy s = 
   let val s' = toLower s
   in foldr (fn ((s1,_),x,A) => 
        if occurs s' s1 then x::A else A) [] (lemmas())
   end

 fun find s = 
    let val s' = toLower s
    in foldr (fn ((_,s2),x,A) => 
         if occurs s' s2 then x::A else A) [] (lemmas())
    end
 end


 local fun thmfind P thm = Lib.can (Dsyntax.find_term P) (Thm.concl thm)
 in
 fun rawmatch P [] pat =
       let val Q = thmfind (P pat)
       in
         foldr (fn (_,rc as (_,(thm,_)),A) => (if Q thm then rc::A else A))
                [] (lemmas())
       end
   | rawmatch P strl pat =
       let val Q = thmfind (P pat)
       in
          Lib.filter (fn (_,(thm,_)) => Q thm)
                     (Lib.flatten (List.map thy strl))
       end
end;

val match = rawmatch (fn tm => Lib.can(Term.match_term tm));


fun bindl thyname blist = 
  let fun addb (thname,th,cl) = add ((thyname,thname),(th,cl))
  in
     dBref := Lib.rev_itlist addb blist (lemmas())
  end;

end;
