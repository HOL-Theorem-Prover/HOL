(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(*   A database of lemmas. This is currently accessible in the               *)
(*   following ways:                                                         *)
(*                                                                           *)
(*     - strings used to denote (part of) the name of the binding,           *)
(*       or theory of interest. Case is not significant.                     *)
(*                                                                           *)
(*     - a general matcher on the term structure of theorems.                *)
(*                                                                           *)
(*     - matching (first order) on the term structure of theorems.           *)
(*                                                                           *)
(*     - looking up a specific theorem in a specific segment.                *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

structure DB :> DB =
struct

open HolKernel Binarymap;
type 'a quotation = 'a Portable.frag list

datatype class = Thm | Axm | Def


(*---------------------------------------------------------------------------
    The pair of strings is theory * bindname
 ---------------------------------------------------------------------------*)

type data = (string * string) * (thm * class)

(*---------------------------------------------------------------------------
     Create the database
 ---------------------------------------------------------------------------*)

local open String
      fun comp ((s1,s2),(t1,t2)) = 
          case compare(s1,t1) of EQUAL => compare(s2,t2) | x => x
in
val DBref = ref (mkDict comp :(string*string, data) dict)

fun lemmas() = !DBref
end;

(*---------------------------------------------------------------------------
   Map keys to canonical case 
 ---------------------------------------------------------------------------*)

fun toLower s =
 let open Char CharVector in tabulate(size s, fn i => toLower(sub(s,i))) end

fun add ((p as (s1,s2)),x) db = insert (db,(toLower s1, toLower s2),(p,x))


(*---------------------------------------------------------------------------
     Persistence: bindl is used to populate the database when a theory
     is loaded.
 ---------------------------------------------------------------------------*)

fun bindl thyname blist =
  let fun addb (thname,th,cl) = add ((thyname,thname),(th,cl))
  in
     DBref := Lib.rev_itlist addb blist (lemmas())
  end;


(*---------------------------------------------------------------------------
     Misc. support
 ---------------------------------------------------------------------------*)

fun occurs s1 s2 =
    not(Substring.isEmpty (#2(Substring.position s1 (Substring.all s2))));

fun norm_thyname "-" = current_theory()
  | norm_thyname s = s;


(*---------------------------------------------------------------------------
    To the database representing all ancestor theories, add the
    entries in the current theory segment.
 ---------------------------------------------------------------------------*)

local fun classify thy cl (s,th) = ((thy,s),(th,cl))
in
fun CT() =
  let val thyname = Theory.current_theory()
  in
    itlist (add o classify thyname Def) (Theory.definitions ())
     (itlist (add o classify thyname Axm) (Theory.axioms ())
      (itlist (add o classify thyname Thm) (Theory.theorems ()) 
              (lemmas())))
  end
end;


(*---------------------------------------------------------------------------
     thy  : All entries in a specified theory
     find : Look up something by name fragment
 ---------------------------------------------------------------------------*)

fun prim_thy P  = foldr (fn ((s1,_),x,A) => if P s1 then x::A else A) []
fun prim_find P = foldr (fn ((_,s2),x,A) => if P s2 then x::A else A) []
fun prim_match P = foldr (fn (_,x,A) => if P x then x::A else A) [];

fun thy s  = prim_thy  (equal (toLower (norm_thyname s))) (CT())
fun find s = prim_find (occurs(toLower s)) (CT());


(*---------------------------------------------------------------------------
      Look up something by matching. Parameterized by the matcher.
 ---------------------------------------------------------------------------*)

fun matchp P thylist =
 let val matchfn = 
       case List.map norm_thyname thylist 
        of []   => (fn (_,(th,_)) => P th)
         | strl => (fn ((s,_),(th,_)) => Lib.mem s strl andalso P th)
 in
   prim_match matchfn (CT())
 end


fun matcher f thyl pat = 
  matchp (fn th => can (find_term (can (f pat))) (concl th)) thyl;

val match = matcher Term.match_term;
val apropos = matcher (ho_match_term []) [] o Parse.Term;


(*---------------------------------------------------------------------------
      Some other lookup functions
 ---------------------------------------------------------------------------*)

fun theorem_class thyname thmname = 
 #2 (Binarymap.find (CT(), (toLower (norm_thyname thyname), toLower thmname)))

fun theorem s1 s2 = fst (theorem_class s1 s2);

fun theorems thyn = List.map (fn ((_,s),(th,_)) => (s,th)) (thy thyn);

fun all_thms () = List.map snd (Binarymap.listItems (CT()));

end
