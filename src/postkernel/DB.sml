(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(*   A database of lemmas. This is currently accessible in the               *)
(*   following ways:                                                         *)
(*                                                                           *)
(*     - strings used to denote (part of) the name of the binding,           *)
(*       or the full name of the theory of interest. Case is not             *)
(*       significant.                                                        *)
(*                                                                           *)
(*     - a general matcher on the term structure of theorems.                *)
(*                                                                           *)
(*     - matching (higher order) on the term structure of theorems.          *)
(*                                                                           *)
(*     - looking up a specific theorem in a specific segment.                *)
(*                                                                           *)
(* ------------------------------------------------------------------------- *)

structure DB :> DB =
struct

open HolKernel DB_dtype;

val ERR = mk_HOL_ERR "DB";

fun indef_class2string Thm = "a theorem"
  | indef_class2string Axm = "an axiom"
  | indef_class2string Def = "a definition"


(*---------------------------------------------------------------------------
    The pair of strings is theory * bindname
 ---------------------------------------------------------------------------*)

type data    = (string * string) * (thm * class)


(*---------------------------------------------------------------------------
   Map keys to canonical case
 ---------------------------------------------------------------------------*)

fun toLower s =
 let open Char CharVector in tabulate(size s, fn i => toLower(sub(s,i))) end

(*---------------------------------------------------------------------------
     Persistence: bindl is used to populate the database when a theory
     is loaded.
 ---------------------------------------------------------------------------*)

structure Map = struct open Redblackmap end
(* the keys are lower-cased, but the data also stores the keys, and there
   the key infomration is kept in its original case *)

(* the submap is a map from lowercased item-name to those items with the
   same name.  There is a list of them because item-names are really
   case-sensitive *)
type submap = (string, data list) Map.dict
val empty_sdata_map = Map.mkDict String.compare

(* the dbmap is a map from lowercased theory-name to a submap (as above)
   and a map from exact theory name to a list of items.  These items are
   stored in the order they were made.  For the sake of clarity, call the
   latter sort of map an ordermap. *)
type dbmap = (string, submap * submap) Map.dict

local val DBref = ref (Map.mkDict String.compare) : dbmap ref
      fun lemmas() = !DBref
      fun add_to_submap m (newdata as ((s1, s2), x)) =
          let val s2key = toLower s2
              val oldvalue = case Map.peek(m, s2key) of
                               NONE => []
                             | SOME items => items
          in
            Map.insert(m, s2key, newdata :: oldvalue)
          end
      fun add_to_ordermap om thyname blist =
          let val oldvalue = case Map.peek(om, thyname) of
                               NONE => []
                             | SOME items => items
          in
            Map.insert(om, thyname, blist @ oldvalue)
          end
      fun functional_bindl db thy blist =
          (* used when a theory is loaded from disk *)
          let val thykey = toLower thy
              val (submap, ordermap) =
                  case Map.peek(db, thykey) of
                    NONE => (empty_sdata_map, empty_sdata_map)
                  | SOME m => m
              fun foldthis ((n,th,cl), m) = add_to_submap m ((thy,n), (th,cl))
              val submap' = List.foldl foldthis submap blist
              val ordermap' =
                  add_to_ordermap
                    ordermap thy
                    (map (fn (n,th,cl) => ((thy,n), (th, cl))) blist)
          in
            Map.insert(db, thykey, (submap', ordermap'))
          end
      fun bind_with_classfn thy cl thlist db =
          (* used to update a database with all of the current segment's
             theorems.  The latter are a moving target, so needs to be done
             multiple times.  Note that the result of this operation is
             not stored back into the reference cell, so there aren't
             multiple copies of the current segment in what DB stores.

             An alternative approach would be to augment the Theory module
             with a "theorem registration scheme", so that later modules
             could be informed whenever a new theorem was added to the current
             segment.  A function to clear things out would also need to
             be registered with after_new_theory so that theorems could be
             dropped if a segment was restarted. *)
          let val thykey = toLower thy
              val (submap, ordermap) =
                  case Map.peek(db, thykey) of
                    NONE => (empty_sdata_map, empty_sdata_map)
                  | SOME m => m
              fun foldthis ((n, th), m) = add_to_submap m ((thy,n),(th, cl))
              val submap' = List.foldl foldthis submap thlist
              val ordermap' =
                  add_to_ordermap
                    ordermap thy
                    (map (fn (n, th) => ((thy,n), (th, cl))) thlist)
          in
            Map.insert(db, thykey, (submap', ordermap'))
          end
in
fun bindl thy blist = DBref := functional_bindl (lemmas()) thy blist

(*---------------------------------------------------------------------------
    To the database representing all ancestor theories, add the
    entries in the current theory segment.
 ---------------------------------------------------------------------------*)

fun CT() =
  let val thyname = Theory.current_theory()
  in
    (bind_with_classfn thyname Def (rev (Theory.current_definitions ())) o
     bind_with_classfn thyname Axm (rev (Theory.current_axioms ())) o
     bind_with_classfn thyname Thm (rev (Theory.current_theorems ())))
    (lemmas())
  end
end (* local *)


(*---------------------------------------------------------------------------
     Misc. support
 ---------------------------------------------------------------------------*)

val occurs = String.isSubstring

fun norm_thyname "-" = current_theory()
  | norm_thyname s = s;


(*---------------------------------------------------------------------------
     thy  : All entries in a specified theory
     find : Look up something by name fragment
 ---------------------------------------------------------------------------*)

fun thy s =
    case Map.peek(CT(), toLower (norm_thyname s)) of
      NONE => []
    | SOME (m, om) => let
      in
        case Map.peek (om, norm_thyname s) of
          NONE => []
        | SOME x => x
      end

fun find s =
    let val s = toLower s
        fun subfold (k, v, acc) = if occurs s k then v @ acc else acc
        fun fold (thy, (m, _), acc) = Map.foldr subfold acc m
    in
      Map.foldr fold [] (CT())
    end


(*---------------------------------------------------------------------------
      Look up something by matching. Parameterized by the matcher.
 ---------------------------------------------------------------------------*)

fun matchp P thylist =
    let fun data_P (_, (th, _)) = P th
        fun subfold (k, v, acc) = List.filter data_P v @ acc
    in
      case thylist of
        [] => let fun fold (k, (m, _), acc) = Map.foldr subfold acc m
              in
                Map.foldr fold [] (CT())
              end
      | _ => let val db = CT()
                 fun fold (thyn, acc) =
                     case Map.peek(db, toLower (norm_thyname thyn)) of
                       NONE => acc
                     | SOME (m, _) => Map.foldr subfold acc m
             in
               List.foldr fold [] thylist
             end
    end


fun matcher f thyl pat =
  matchp (fn th => can (find_term (can (f pat))) (concl th)) thyl;

val match = matcher (ho_match_term [] empty_tmset);
val apropos = match [];

(* matches : term -> thm -> bool
  tests whether theorem matches pattern *)
fun matches pat th =
  can (find_term (can (ho_match_term [] empty_tmset pat))) (concl th) ;

fun apropos_in pat dbdata =
  List.filter (fn (_, (th, _)) => matches pat th) dbdata ;

fun find_in s =
  let val lows = toLower s ;
    fun finds dbdata =
      List.filter (fn ((_, name), _) => occurs lows (toLower name)) dbdata ;
  in finds end ;

fun listDB () =
    let fun subfold (k,v,acc) = v @ acc
        fun fold (_, (m, _), acc) = Map.foldr subfold acc m
    in
      Map.foldr fold [] (CT())
    end

(*---------------------------------------------------------------------------
      Some other lookup functions
 ---------------------------------------------------------------------------*)

fun thm_class origf thy name = let
  val db = CT()
  val thy = norm_thyname thy
  val nosuchthm = ("theorem "^thy^"$"^name^" not found")
  val thymap = #1 (Map.find(db, toLower thy))
               handle Map.NotFound => raise ERR origf ("no such theory: "^thy)
  val result = Map.find(thymap, toLower name)
               handle Map.NotFound => raise ERR origf nosuchthm
in
  case filter (equal (norm_thyname thy,name) o fst) result of
    [(_,p)] => p
  | [] => raise ERR origf nosuchthm
  | other => raise ERR origf
                       ("multiple things in theory "^thy^" with name "^name)
end

fun fetch s1 s2 = fst (thm_class "fetch" s1 s2);

fun thm_of ((_,n),(th,_)) = (n,th);
fun is x (_,(_,cl)) = (cl=x)

val thms        = List.map thm_of o thy
val theorems    = List.map thm_of o Lib.filter (is Thm) o thy
val definitions = List.map thm_of o Lib.filter (is Def) o thy
val axioms      = List.map thm_of o Lib.filter (is Axm) o thy

fun theorem s = let
  val (thm,c) = thm_class "theorem" "-" s
in
  if c = Thm then thm
  else raise ERR "theorem" ("No theorem in current theory of name "^s^
                            " (but there is "^indef_class2string c^")")
end

fun definition s = let
  val (thm,c) = thm_class "definition" "-" s
in
  if c = Def then thm
  else raise ERR "theorem" ("No definition in current theory of name "^s^
                            " (but there is "^indef_class2string c^")")
end

fun axiom s = let
  val (thm,c) = thm_class "axiom" "-" s
in
  if c = Axm then thm
  else raise ERR "axiom" ("No axiom in current theory of name "^s^
                          " (but there is "^indef_class2string c^")")
end

fun dest_theory s =
 let val thyname = if s = "-" then Theory.current_theory () else s
 in
   THEORY (thyname,
    {types = rev (Theory.types thyname),
     consts = rev (map dest_const (Theory.constants thyname)),
     parents = Theory.parents thyname,
     axioms = axioms thyname,
     definitions = definitions thyname,
     theorems = theorems thyname})
 end
 handle e => raise ERR "dest_theory" (Lib.quote s^" is not a known theory");

end
