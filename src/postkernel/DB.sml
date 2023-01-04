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

fun pdv_thm (pdv : public_data_value) = #1 pdv
fun dv_thm (dv : data_value) : thm = #1 dv
fun dv_class (dv : data_value) : class = #2 dv
fun dv_isprivate (dv : data_value) = #private (#3 dv)

fun dataName (((_, nm), _) : 'a named) = nm
fun dataThy (((thy, _), _) : 'a named) = thy
fun data_isprivate (nms, dv) = dv_isprivate dv
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

structure Map = HOLdict
(* the keys are lower-cased, but the data also stores the keys, and there
   the key information is kept in its original case *)

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
datatype dbmap = DB of { namemap : (string, submap) Map.dict,
                         revmap : location list Termtab.table,
                         localmap : (thm * {private:bool}) Symtab.table
                       }

fun namemap (DB{namemap,...}) = namemap
fun revmap (DB{revmap,...}) = revmap
fun localmap (DB{localmap,...}) = localmap
fun updnamemap f (DB{namemap,revmap,localmap}) =
    DB {namemap = f namemap, revmap = revmap, localmap = localmap}
fun updrevmap f (DB{namemap,revmap,localmap}) =
    DB {namemap = namemap, revmap = f revmap, localmap=localmap}
fun updlocalmap f (DB{namemap,revmap,localmap}) =
    DB {namemap = namemap, revmap = revmap, localmap = f localmap}

val empty_dbmap = DB {namemap = Map.mkDict String.compare,
                      localmap = Symtab.empty, revmap = Termtab.empty}

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
      fun functional_bindl_names thy blist namemap =
          (* used when a theory is loaded from disk *)
          let val submap =
                  case Map.peek(namemap, thy) of
                    NONE => empty_sdata_map
                  | SOME m => m
              fun foldthis ((n,th,cl,vis), m) =
                  add_to_submap m ((thy,n), (th,cl,vis))
              val submap' = List.foldl foldthis submap blist
          in
            Map.insert(namemap, thy, submap')
          end
      fun functional_bindl_revmap thy blist revmap =
          List.foldl
            (fn ((n,th,cl,vis), A) =>
                Termtab.cons_list(concl th,Stored {Thy = thy,Name = n}) A)
            revmap
            blist
      fun functional_bindl db thy blist =
          db |> updnamemap (functional_bindl_names thy blist)
             |> updrevmap (functional_bindl_revmap thy blist)

      fun purge_stale_bindings() =
          let
            open Map
            fun foldthis (n, datas : data list, m) =
                let
                  val data' = List.filter(fn (_, (th, _, _)) => uptodate_thm th)
                                          datas
                in
                  insert(m,n,data')
                end
            fun purge_stale ttab =
                let open Termtab
                in
                  fold (fn (t,d) => fn A =>
                           if uptodate_term t then update (t,d) A else A)
                       ttab
                       empty
                end
            val ct = current_theory()
          in
            DBref := ((!DBref)
                       |> updnamemap
                            (updexisting ct (foldl foldthis empty_sdata_map))
                       |> updrevmap purge_stale)
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
            fun dest_thk (ThmKind_dtype.Thm th) = (th, Thm)
              | dest_thk (ThmKind_dtype.Axiom(_, th)) = (th, Axm)
              | dest_thk (ThmKind_dtype.Defn th) = (th, Def)
            fun toThmClass (s, (thk, v)) =
                let val (th,k) = dest_thk thk in (s,th,k,v) end
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
fun revlookup th = Termtab.lookup_list (revmap (!DBref)) (concl th)
(*---------------------------------------------------------------------------
    To the database representing all ancestor theories, add the
    entries in the current theory segment.
 ---------------------------------------------------------------------------*)
fun CT() = !DBref

fun store_local private s th =
    DBref := (!DBref |> updlocalmap (Symtab.update(s,(th,private)))
                     |> updrevmap (Termtab.cons_list(concl th, Local s)))
fun local_thm s = case Symtab.lookup (localmap (!DBref)) s of
                      NONE => NONE
                    | SOME (th,{private}) => if private then NONE else SOME th

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

fun find0 incprivatep s =
    let
      val DB{namemap,...} = CT()
      fun subfold (k, vs, acc) =
          if findpred s k then
            (if incprivatep then vs
             else List.filter (fn (_, (_, _, {private=p})) => not p) vs) @
            acc
          else acc
      fun fold (thy, m, acc) = Map.foldr subfold acc m
    in
      Map.foldr fold [] namemap
    end

fun find s = List.map (fn (n, (th,c,_)) => (n, (th,c))) (find0 false s)
val find_all = find0 true

(*---------------------------------------------------------------------------
      Look up something by matching. Parameterized by the matcher.
 ---------------------------------------------------------------------------*)

fun matchp0 incprivate P thylist =
    let fun data_P (_, (th, _, {private})) =
            (incprivate orelse not private) andalso P th
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

val match_primitive = ho_match_term [] empty_tmset

fun matchp P thys = map drop_private $ matchp0 false P thys
fun matcher f thyl pat =
  matchp (fn th => can (find_term (can (f pat))) (concl th)) thyl;

fun match thys pat = matcher match_primitive thys pat
val apropos = match [];

(* matches : term -> thm -> bool
  tests whether theorem matches pattern *)
fun matches pat th =
  can (find_term (can (match_primitive pat))) (concl th) ;

fun apropos_in pat dbdata =
  List.filter (fn (_, pdv) => matches pat $ pdv_thm pdv) dbdata

fun find_in s = List.filter (findpred s o dataName)

fun listDB () =
    let fun subfold (k,v,acc) = v @ acc
        fun fold (_, m, acc) = Map.foldr subfold acc m
    in
      Map.foldr fold [] (namemap (CT()))
    end

fun listPublicDB() =
    let
      fun subfold (_,dvs,acc) =
          let
            val dvs' =
                List.mapPartial (fn d => if data_isprivate d then NONE
                                         else SOME (drop_private d))
                                dvs
          in
            dvs' :: acc
          end
      fun fold (_, m, acc) = Map.foldr subfold acc m
    in
      List.concat (Map.foldr fold [] (namemap (CT())))
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
      recurse sels (listPublicDB())
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

fun fetch s1 s2 = #1 (thm_class "fetch" s1 s2);
fun fetch_knm{Thy,Name} = fetch Thy Name

fun thm_of ((_,n),dv) = (n,dv_thm dv);
fun is x (_,dv) = (dv_class dv=x)

val thms        = List.map thm_of o thy
val theorems    = List.map thm_of o Lib.filter (is Thm) o thy
val definitions = List.map thm_of o Lib.filter (is Def) o thy
val axioms      = List.map thm_of o Lib.filter (is Axm) o thy

fun theorem s = let
  val dv = thm_class "theorem" "-" s
  val c = dv_class dv
in
  if c = Thm then dv_thm dv
  else raise ERR "theorem" ("No theorem in current theory of name "^s^
                            " (but there is "^indef_class2string c^")")
end

fun definition s = let
  val dv = thm_class "definition" "-" s
  val c = dv_class dv
in
  if c = Def then dv_thm dv
  else raise ERR "theorem" ("No definition in current theory of name "^s^
                            " (but there is "^indef_class2string c^")")
end

fun axiom s = let
  val dv = thm_class "axiom" "-" s
  val c = dv_class dv
in
  if c = Axm then dv_thm dv
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

(* Derived search functions *)
fun find_consts_thy thl t =
  let
    val theConsts = List.concat (List.map constants thl)
  in
    List.filter (can (match_type t) o type_of) theConsts
end

(* The call to find_consts_thy is hidden under a fun binding to make sure that
  the theory list is constructed properly and not captured in a closure *)
fun find_consts t = find_consts_thy ("-" :: ancestry "-") t;

end
