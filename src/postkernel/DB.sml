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
fun dv_class (dv : data_value) : class = #class (#2 dv)
fun dv_isprivate (dv : data_value) = #private (#2 dv)

fun dataName (((_, nm), _) : 'a named) = nm
fun dataThy (((thy, _), _) : 'a named) = thy
fun data_isprivate (nms, dv) = dv_isprivate dv
fun dataNameEq s d = dataName d = s


(*---------------------------------------------------------------------------
   Map keys to canonical case
 ---------------------------------------------------------------------------*)

val toLower = CharVector.map Char.toLower

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
                         localmap : (thm * thminfo) Symtab.table
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
              fun foldthis ((n,th,info), m) =
                  add_to_submap m ((thy,n), (th,info))
              val submap' = List.foldl foldthis submap blist
          in
            Map.insert(namemap, thy, submap')
          end
      fun functional_bindl_revmap thy blist revmap =
          List.foldl
            (fn ((n,th,i), A) =>
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
                  val data' = List.filter(fn (_, (th, _)) => uptodate_thm th)
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
            fun flat (n,(th,i)) = (n,th,i)
          in
            case thydelta of
                DelConstant _ => purge_stale_bindings()
              | DelTypeOp _ => purge_stale_bindings()
              | NewBinding nb =>
                (
                  if Theory.is_temp_binding (#1 nb) then ()
                  else
                    DBref := functional_bindl (!DBref) (current_theory())
                                              [flat nb]
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
                    | SOME (th,{private,...}:thminfo) =>
                      if private then NONE else SOME th

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

fun findpred pat =
    let
        val pat = toLower pat
        open DBSearchParser
    in
        contains_regexp pat o toLower
    end

fun find0 incprivatep s =
    let
      val DB{namemap,...} = CT()
      val check = findpred s (* pre-compiles regexp *)
      fun subfold (k, vs, acc) =
          if check k then
            (if incprivatep then vs
             else List.filter (fn (_, (_, {private=p,...})) => not p) vs) @
            acc
          else acc
      fun fold (thy, m, acc) = Map.foldr subfold acc m
    in
      Map.foldr fold [] namemap
    end

fun find s = List.map drop_private (find0 false s)
val find_all = find0 true

(*---------------------------------------------------------------------------
      Look up something by matching. Parameterized by the matcher.
 ---------------------------------------------------------------------------*)

fun matchp0 incprivate P thylist =
    let fun data_P (_, (th, {private,...})) =
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

(* dtc': auxiliary function used by dest_polarity *)
fun dtc' (t : term) =
    let val {Thy, Name, ...} = dest_thy_const t in
        SOME (Thy, Name)
    end handle HOL_ERR _ => NONE

(* -------------------------------------------------------------------------- *)
(* dest_polarity:                                                             *)
(*                                                                            *)
(* The general idea of this function is to split a term into its conclusion   *)
(* and its premises.                                                          *)
(*                                                                            *)
(* This function will be used to allow the user to search for theorems        *)
(* matching a certain pattern in either the premises or in the conclusion.    *)
(*                                                                            *)
(* More precisely, it splits a term into a set of "positive" terms and        *)
(* "negative" terms. (Thanks to Michael Norrish for this idea. I'm not sure   *)
(* whether or not he himself got the idea from someplace else). This is a     *)
(* general notion of premises and conclusions that is more robust than an     *)
(* intuitive understanding. For example, in the equation (a ==> b) ==> c,     *)
(* at first glance, b appears to be the conclusion of an implication operator.*)
(* However, in this case, it makes more sense to treat b as a premise, since  *)
(* the implication it is a conclusion of is itself the premise of another     *)
(* implication. In particular, if you knew b, then you would immediately also *)
(* know (a ==> b), thus, you would have a premise to the equation. Similarly, *)
(* whereas 'a' appears at first glance to be a premise, in fact, it makes     *)
(* more sense to treat it as a conclusion. Knowing 'a' doesn't directly help  *)
(* in proving c, but if you know ~c, then you can derive 'a', since           *)
(* (a ==> b) ==> F can only be true if (a ==> b) is false, and (a ==> b) is   *)
(* only false if 'a' is true and b is false.                                  *)
(*                                                                            *)
(* My understanding of the notion of positive terms and negative terms is     *)
(* incomplete and more rigour could probably be applied. However, this is     *)
(* sufficient for the application of searching for theorems.                  *)
(*                                                                            *)
(* In this notion, "positive" terms are essentially those which are           *)
(* un-negated in the conclusion to the expression, and "negative" terms are   *)
(* essentially those which are negated in the conclusion to the expression.   *)
(* That is, "p" is positive whereas "~p" is negative.                         *)
(*                                                                            *)
(* This derives from the fact that a ==> b can be transformed into b \/ ~a.   *)
(*                                                                            *)
(* Also, given the theorem a ==> b, which has 'a' as a premise, we can use    *)
(* the contrapositive to derive a theorem with ~a as a conclusion. Similarly, *)
(* if we have 'b' as a conclusion, we can use the contrapositive to derive a  *)
(* theorem with ~b as a premise. Thus, premises are in some sense essentially *)
(* negated conclusions.                                                       *)
(*                                                                            *)
(* -------------------------------------------------------------------------- *)
(*                                                                            *)
(* The function is defined recursively as follows:                            *)
(*                                                                            *)
(* Terms which cannot be broken down further (or unrecognised terms) are      *)
(* treated as positive.                                                       *)
(*                                                                            *)
(* Applying a not swaps the positive and negative terms.                      *)
(*                                                                            *)
(* An implication will retain the polarity of the terms in the conclusion to  *)
(* the implication, and swap the polarity of the terms in the premise to the  *)
(* implication.                                                               *)
(*                                                                            *)
(* An 'and' statement will retain the polarity of its operands. Note that an  *)
(* 'and' statement in the outermost layer can be treated as essentially being *)
(* two separate theorems, which helps to motivate this treatment.             *)
(*                                                                            *)
(* An 'or' statement will retain the polarity of its operands.                *)
(*                                                                            *)
(* A 'forall' statement or an 'exists' statement will retain the polarity of  *)
(* its operands.                                                              *)
(*                                                                            *)
(* Unrecognised terms are treated as positive.                                *)
(*                                                                            *)
(* Thanks to Michael Norrish for writing some of the code used by this        *)
(* function.                                                                  *)
(*                                                                            *)
(* Term -> Term List * Term List                                              *)
(*                                                                            *)
(* The first term list contains the positive terms, while the second term     *)
(* list contains the negative terms.                                          *)
fun dest_polarity (t : term) : term list * term list =
    let
        val (f, xs) = strip_comb t
    in
        case (dtc' f) of
        SOME ("bool", "~") =>
            (let
                val inner_term = hd xs
                val recursive_result = dest_polarity inner_term
                val (positive_terms, negative_terms) = recursive_result
            in
                (negative_terms, positive_terms)
            end)
        | SOME ("min", "==>") =>
            (let
                val antecedent = el 1 xs
                val consequent = el 2 xs
                val ant_recursive_result = dest_polarity antecedent
                val con_recursive_result = dest_polarity consequent
                val (ant_pos, ant_neg) = ant_recursive_result
                val (con_pos, con_neg) = con_recursive_result
            in
                (ant_neg @ con_pos, ant_pos @ con_neg)
            end)
        | SOME ("bool", "/\\") =>
            (let
                val term1 = el 1 xs
                val term2 = el 2 xs
                val recursive_result_1 = dest_polarity term1
                val recursive_result_2 = dest_polarity term2
                val (pos_1, neg_1) = recursive_result_1
                val (pos_2, neg_2) = recursive_result_2
            in
                (pos_1 @ pos_2, neg_1 @ neg_2)
            end)
        | SOME ("bool", "\\/") =>
            (let
                val term1 = el 1 xs
                val term2 = el 2 xs
                val recursive_result_1 = dest_polarity term1
                val recursive_result_2 = dest_polarity term2
                val (pos_1, neg_1) = recursive_result_1
                val (pos_2, neg_2) = recursive_result_2
            in
                (pos_1 @ pos_2, neg_1 @ neg_2)
            end)
        | SOME ("bool", "!") =>
            (let
                val quantified_term = hd xs
                val recurse_on_term = (case (total dest_abs quantified_term) of
                    NONE => quantified_term
                    | SOME (_, bound_term) => bound_term)
                val recursive_result = dest_polarity recurse_on_term
            in
                recursive_result
            end)
        | SOME ("bool", "?") =>
            (let
                val quantified_term = hd xs
                val recurse_on_term = (case (total dest_abs quantified_term) of
                    NONE => quantified_term
                    | SOME (_, bound_term) => bound_term)
                val recursive_result = dest_polarity recurse_on_term
            in
                recursive_result
            end)
        | _ => ([t], [])
    end;

fun polarity_match (polarity : bool) (match_term : term) (th : thm) =
    (let
      val theorem_term = concl th
      val polarity_terms = dest_polarity theorem_term
      val match_predicate = can ((ho_match_term [] empty_tmset) match_term)
      val match_results = map (can (find_term match_predicate)) (if polarity then fst polarity_terms else snd polarity_terms)
    in
         List.exists (fn x => x) match_results
    end)

fun polarity_search (polarity : bool) (match_term : term) =
    matchp (polarity_match polarity match_term) []

fun apropos_in pat dbdata =
  List.filter (fn (_, pdv) => matches pat $ pdv_thm pdv) dbdata

fun find_in s = let
    val check = findpred s
in List.filter (check o dataName)
end

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
fun lookup {Thy,Name} = Lib.total (thm_class "lookup" Thy) Name

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
