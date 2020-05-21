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

fun dataName (((_, nm), _) : data) = nm
fun dataThy (((thy, _), _) : data) = thy
fun dataNameEq s d = dataName d = s


(*---------------------------------------------------------------------------
   Map keys to canonical case
 ---------------------------------------------------------------------------*)

fun toLower s =
 let open Char CharVector in tabulate(size s, fn i => toLower(sub(s,i))) end

(*---------------------------------------------------------------------------
     Persistence: bindl is used to populate the database when a theory
     is loaded.
 ---------------------------------------------------------------------------*)

structure Map = Redblackmap
(* the keys are lower-cased, but the data also stores the keys, and there
   the key infomration is kept in its original case *)

fun updexisting key f m =
    case Map.peek(m,key) of
        NONE => m
      | SOME v => Map.insert(m,key,f v)

(* the submap is a map from lowercased item-name to those items with the
   same name.  There is a list of them because item-names are really
   case-sensitive *)
type submap = (string, data list) Map.dict
val empty_sdata_map = Map.mkDict String.compare

(* the dbmap contains:
    - a map from theory-name to a submap (as above)
*)
datatype dbmap = DB of { namemap : (string, submap) Map.dict }

fun namemap (DB{namemap,...}) = namemap
fun updnamemap f (DB{namemap}) = DB {namemap = f namemap}

val empty_dbmap = DB {namemap = Map.mkDict String.compare}

local val DBref = ref empty_dbmap
      fun lemmas() = !DBref
      fun add_to_submap m (newdata as ((s1, s2), x)) =
          let val s2key = toLower s2
              val oldvalue = case Map.peek(m, s2key) of
                               NONE => []
                             | SOME items => items
          in
            Map.insert(m, s2key,
                       newdata :: List.filter (not o dataNameEq s2) oldvalue)
          end
      fun functional_bindl (DB {namemap,...}) thy blist =
          (* used when a theory is loaded from disk *)
          let val submap =
                  case Map.peek(namemap, thy) of
                    NONE => empty_sdata_map
                  | SOME m => m
              fun foldthis ((n,th,cl), m) = add_to_submap m ((thy,n), (th,cl))
              val submap' = List.foldl foldthis submap blist
          in
            DB {namemap = Map.insert(namemap, thy, submap')}
          end

      fun purge_stale_bindings() =
          let
            open Map
            fun foldthis (n, datas : data list, m) =
                let
                  val data' = List.filter (fn (_, (th, _)) => uptodate_thm th)
                                          datas
                in
                  insert(m,n,data')
                end
            val ct = current_theory()
          in
            DBref := updnamemap
                       (updexisting ct (foldl foldthis empty_sdata_map))
                       (!DBref)
          end

      fun delete_binding bnm =
          let
            open Map
            val ct = current_theory()
            fun smdelbinding bnm sm =
                case peek (sm, toLower bnm) of
                    NONE => sm
                  | SOME datas =>
                    insert(sm,toLower bnm,
                           List.filter(not o dataNameEq bnm) datas)
          in
            DBref := updnamemap (updexisting ct (smdelbinding bnm)) (!DBref)
          end


      fun hook thydelta =
          let
            open TheoryDelta
            fun toThmClass (s, ThmKind_dtype.Thm th) = (s, th, Thm)
              | toThmClass (s, ThmKind_dtype.Axiom(sn,th)) = (s, th, Axm)
              | toThmClass (s, ThmKind_dtype.Defn th) = (s, th, Def)
          in
            case thydelta of
                DelConstant _ => purge_stale_bindings()
              | DelTypeOp _ => purge_stale_bindings()
              | NewBinding nb =>
                (
                  if Theory.is_temp_binding (#1 nb) then ()
                  else
                    DBref := functional_bindl (!DBref) (current_theory())
                                              [toThmClass nb]
                )
              | DelBinding s => delete_binding s
              | _ => ()
          end
      val _ = Theory.register_hook("DB", hook)
in
fun bindl thy blist = DBref := functional_bindl (lemmas()) thy blist

(*---------------------------------------------------------------------------
    To the database representing all ancestor theories, add the
    entries in the current theory segment.
 ---------------------------------------------------------------------------*)

fun CT() = !DBref
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
    let
      val DB{namemap,...} = CT()
    in
      case Map.peek(namemap, norm_thyname s) of
          NONE => []
        | SOME m => Map.foldl (fn (lcnm, datas, A) => datas @ A) [] m
    end

fun findpred pat s =
    let
      val pat = toLower pat and s = toLower s
      val orparts = String.tokens (equal #"|") pat
      val subparts = map (String.tokens (equal #"~")) orparts
      val subpred = List.all (C occurs s)
    in
      List.exists subpred subparts
    end

fun find s =
    let
      val DB{namemap,...} = CT()
      fun subfold (k, v, acc) = if findpred s k then v @ acc else acc
      fun fold (thy, m, acc) = Map.foldr subfold acc m
    in
      Map.foldr fold [] namemap
    end


(*---------------------------------------------------------------------------
      Look up something by matching. Parameterized by the matcher.
 ---------------------------------------------------------------------------*)

fun matchp P thylist =
    let fun data_P (_, (th, _)) = P th
        fun subfold (k, v, acc) = List.filter data_P v @ acc
    in
      case thylist of
        [] => let fun fold (k, m, acc) = Map.foldr subfold acc m
              in
                Map.foldr fold [] (namemap (CT()))
              end
      | _ => let val db = namemap (CT())
                 fun fold (thyn, acc) =
                     case Map.peek(db, norm_thyname thyn) of
                       NONE => acc
                     | SOME m => Map.foldr subfold acc m
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

fun find_in s = List.filter (findpred s o dataName)

fun listDB () =
    let fun subfold (k,v,acc) = v @ acc
        fun fold (_, m, acc) = Map.foldr subfold acc m
    in
      Map.foldr fold [] (namemap (CT()))
    end

fun selectDB sels =
    let
      fun selfn (SelTM pat) = apropos_in pat
        | selfn (SelNM s) = find_in s
        | selfn (SelTHY s) = List.filter (equal (norm_thyname s) o dataThy)
      fun recurse sels d =
          case sels of
              [] => d
            | s::rest => recurse rest (selfn s d)
    in
      recurse sels (listDB())
    end


(*---------------------------------------------------------------------------
      Some other lookup functions
 ---------------------------------------------------------------------------*)

fun thm_class origf thy name = let
  val db = namemap (CT())
  val thy = norm_thyname thy
  val nosuchthm = ("theorem "^thy^"$"^name^" not found")
  val thymap = Map.find(db, thy)
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
