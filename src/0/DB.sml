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

 type data = AncestorDB.data

 val ct = Theory.current_theory

 fun get_ctstuff () = let
   val defns = Theory.definitions ()
   val axms = Theory.axioms()
   val thms = Theory.theorems()
   val thyname = Theory.current_theory()
 in
   map (fn (s, thm) => ((thyname, s), (thm, Thm.Def))) defns @
   map (fn (s, thm) => ((thyname, s), (thm, Thm.Axm))) axms @
   map (fn (s, thm) => ((thyname, s), (thm, Thm.Thm))) thms
 end

 fun occurs s1 s2 =
   not(Substring.isEmpty (#2(Substring.position s1 (Substring.all s2))))

 fun toLower s =
   let open Char CharVector
   in tabulate(size s, fn i => toLower(sub(s, i))) end

 fun thy s =
   if s = "-" then get_ctstuff()
   else
     AncestorDB.thy s @
     (if occurs (toLower s) (toLower (ct())) then get_ctstuff() else [])

 fun find s = let
   val s' = toLower s
   val ctstuff = get_ctstuff()
 in
   AncestorDB.find s @
   List.filter (fn ((_, thmname), _) => occurs s' (toLower thmname)) ctstuff
 end

 fun rawfind thys P = let
   val include_ct =
     Lib.mem "-" thys orelse null thys orelse
     List.exists (fn s => occurs (toLower s) (toLower (ct()))) thys
   val ct_contribution =
     if include_ct then
       List.filter (fn (_, (thm,_)) => P (Thm.concl thm))
       (get_ctstuff())
     else
       []
   val ancestor_contrib =
     if thys = ["-"] then []
     else
       case (Lib.set_diff thys ["-"]) of
         [] => Binarymap.foldr (fn (_, rc as (_, (thm,_)), A) =>
                                if P (Thm.concl thm) then rc::A else A)
               [] (AncestorDB.lemmas())
       | strl => let
         in
           Lib.filter (fn (_, (thm, _)) => P (Thm.concl thm))
           (List.concat (List.map AncestorDB.thy strl))
         end
 in
   ct_contribution @ ancestor_contrib
 end


 fun match thys tm = let
   val matches = Lib.can (Term.match_term tm)
   val subterm_matches = Lib.can (Dsyntax.find_term matches)
 in
   rawfind thys subterm_matches
 end

 fun gen_theorems thyname =
   if thyname = "-" orelse toLower thyname = toLower (ct()) then
     map (fn ((_, thmname), (thm, c)) => (thmname, thm, c)) (get_ctstuff())
   else
     AncestorDB.gen_theorems thyname

 fun theorems thyname =
   map (fn (thname, thm, c) => (thname, thm)) (gen_theorems thyname)

 fun gen_theorem thyname thmname = let
   val thms = gen_theorems thyname
 in
   case List.find (fn (name, thm, c) => name = thmname) thms of
     SOME (n,t,c) => (t,c)
   | NONE => raise Exception.HOL_ERR {origin_structure = "DB",
                                      origin_function = "gen_theorem",
                                      message = "No theorem with that name"}
 end

 fun theorem thyname thmname = #1 (gen_theorem thyname thmname)

 fun all_thms () =
   Binarymap.foldr (fn (_, rc, A) => rc::A) (get_ctstuff())
   (AncestorDB.lemmas())


end