(*  Title:      HolRefute/Refute_ModelFinder_Model.sml
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009, 2010

Model reconstruction for the HOL4 Refute model finder.  This is the M3
subset of Isabelle Nitpick's nitpick_model.ML. *)

signature REFUTE_MODEL_FINDER_MODEL = sig
  type term = Term.term
  type hol_type = Type.hol_type
  type rep = Refute_ModelFinder_Rep.rep
  type nut = Refute_ModelFinder_Nut.nut
  type scope = Refute_ModelFinder_Scope.scope
  type raw_bound = Refute_Forl.raw_bound

  type reconstruction =
    {bindings : (term * term) list,
     evals : (term * term) list,
     skolems : (string * term) list,
     consts : (term * term) list,
     types : (hol_type * term list * bool) list,
     codatatypes_ok : bool}

  datatype verdict = Keep of Refute_Core.counterexample | Drop

  val term_for_rep :
    {scope : scope,
     atoms : (hol_type option * string list) list,
     sel_names : nut list,
     rel_table : nut Refute_ModelFinder_Nut.NameTable.table,
     bounds : raw_bound list,
     maybe_opt : bool,
     ty : hol_type,
     representation : rep,
     tuples : int list list} -> term

  val reconstruct :
    {scope : scope,
     atoms : (hol_type option * string list) list,
     real_frees : term list,
     eval_terms : term list,
     free_names : nut list,
     sel_names : nut list,
     nonsel_names : nut list,
     rel_table : nut Refute_ModelFinder_Nut.NameTable.table,
     bounds : raw_bound list} -> reconstruction

  val model_report : reconstruction -> Refute_Core.model_report
  val certification_env :
    (term * term) list -> (term * term) list option
  val certifiable : bool -> (term * term) list -> bool
  val genuine_means_genuine :
    {got_all_mono_user_axioms : bool,
     no_poly_user_axioms : bool,
     wfs : bool list,
     total_consts : bool option} -> bool
  val try_again_reasons : string list -> string list
  val certify :
    {executable : bool,
     original : term,
     eval_terms : term list,
     reconstruction : reconstruction,
     cex : Refute_Core.counterexample,
     sound : bool,
     genuine_means_genuine : bool,
     reasons : string list} -> verdict
end

structure Refute_ModelFinder_Model
  :> REFUTE_MODEL_FINDER_MODEL = struct

open Feedback

structure MFH = Refute_ModelFinder_HOL
structure MFN = Refute_ModelFinder_Names
structure MFNT = Refute_ModelFinder_Nut
structure MFP = Refute_ModelFinder_Peephole
structure MFR = Refute_ModelFinder_Rep
structure MFS = Refute_ModelFinder_Scope
structure MFU = Refute_ModelFinder_Util

type term = Term.term
type hol_type = Type.hol_type
type rep = MFR.rep
type nut = MFNT.nut
type scope = MFS.scope
type raw_bound = Refute_Forl.raw_bound

type reconstruction =
  {bindings : (term * term) list,
   evals : (term * term) list,
   skolems : (string * term) list,
   consts : (term * term) list,
   types : (hol_type * term list * bool) list,
   codatatypes_ok : bool}

datatype verdict = Keep of Refute_Core.counterexample | Drop

(* Per-type running counters plus the numbers already handed out, so
   that numbering an atom is a pair of lookups rather than a scan. *)
type atom_pool =
  {counts : (hol_type, int) Redblackmap.dict,
   numbers : (hol_type * int, int) Redblackmap.dict} ref

fun new_atom_pool () : atom_pool =
  ref {counts = Redblackmap.mkDict Type.compare,
       numbers = Redblackmap.mkDict
         (Portable.pair_compare (Type.compare, Int.compare))}

type context =
  {scope : scope,
   atoms : (hol_type option * string list) list,
   sel_names : nut list,
   rel_table : nut MFNT.NameTable.table,
   bounds : raw_bound list,
   pool : atom_pool}

fun err function message =
  Feedback.mk_HOL_ERR "Refute_ModelFinder_Model" function message

fun same_type left right = Type.compare (left, right) = EQUAL

fun member_tuple tuple = List.exists (fn other => other = tuple)

fun chop count values =
  let
    fun split 0 front rest = (rev front, rest)
      | split _ front [] = (rev front, [])
      | split remaining front (value :: rest) =
          split (remaining - 1) (value :: front) rest
  in
    if count < 0 then raise err "chop" "negative count"
    else split count [] values
  end

fun find_name names nickname =
  List.find (fn name => MFNT.nickname_of name = nickname) names

fun tuples_for_name ({rel_table, bounds, ...} : context) name =
  let val relation = MFNT.the_rel rel_table name
  in Option.getOpt (AList.lookup (op =) bounds relation, []) end
  handle MFNT.NUT _ => [[]]

fun tuples_for_nickname (context as {sel_names, ...} : context) nickname =
  case find_name sel_names nickname of
      SOME name => tuples_for_name context name
    | NONE => []

fun type_atom_names atoms ty =
  case List.find (fn (pattern, _) =>
         case pattern of
             SOME pattern_ty =>
               same_type pattern_ty ty orelse
               Lib.can (Type.match_type pattern_ty) ty
           | NONE => false) atoms of
      SOME (_, names) => names
    | NONE =>
        (case List.find (fn (pattern, _) => not (Option.isSome pattern))
                        atoms of
             SOME (_, names) => names
           | NONE => [])

fun atom_number (pool : atom_pool) ty atom =
  let val {counts, numbers} = !pool in
    case Redblackmap.peek (numbers, (ty, atom)) of
        SOME number => number
      | NONE =>
          let
            val number = 1 + Option.getOpt (Redblackmap.peek (counts, ty), 0)
            val _ = pool :=
              {counts = Redblackmap.insert (counts, ty, number),
               numbers = Redblackmap.insert (numbers, (ty, atom), number)}
          in
            number
          end
  end

fun atom_term ({atoms, pool, ...} : context) ty atom =
  let
    val number = atom_number pool ty atom
    val overrides = type_atom_names atoms ty
  in
    if number <= length overrides then
      Term.mk_var (List.nth (overrides, number - 1), ty)
    else
      MFN.fake_atom number ty
  end

(* Schwartzian transform: one pretty-printer call per element instead of
   two per comparison.  Listsort.sort is not stable, so the original
   position is carried along as a tie-break; that reproduces exactly the
   order of the insertion sort this replaces. *)
fun sort_terms pairs =
  let
    fun tag _ [] = []
      | tag index ((pair as (term, _)) :: rest) =
          (Parse.term_to_string term, index, pair) :: tag (index + 1) rest
    fun compare ((left_key, left_index, _), (right_key, right_index, _)) =
      case String.compare (left_key, right_key) of
          EQUAL => Int.compare (left_index, right_index)
        | other => other
  in
    map #3 (Listsort.sort compare (tag 0 pairs))
  end

fun is_unknown term =
  Term.is_var term andalso #1 (Term.dest_var term) = "?"

fun make_update (point, value) base =
  Term.mk_comb (combinSyntax.mk_update (point, value), base)

fun make_fun ({scope, ...} : context) domain_ty range_ty pairs =
  let
    val complete = MFS.is_complete_type (#data_types scope) false domain_ty
    val marker =
      if complete then MFN.irrelevant_marker range_ty
      else MFN.unknown_marker range_ty
    val base = combinSyntax.mk_K_1 (marker, domain_ty)
    val determined = List.filter (not o is_unknown o #2) pairs
  in
    List.foldl (fn (pair, result) => make_update pair result)
      base (sort_terms determined)
  end

fun make_set ({scope, ...} : context) maybe_opt element_ty pairs =
  let
    val present = map #1 (List.filter
      (fn (_, value) => Term.aconv value boolSyntax.T) pairs)
    val all_unknown = not (null pairs) andalso List.all
      (fn (_, value) =>
        not (Term.aconv value boolSyntax.T) andalso
        not (Term.aconv value boolSyntax.F)) pairs
    val incomplete =
      not (MFS.is_complete_type (#data_types scope) false element_ty)
    val elements =
      if maybe_opt andalso incomplete then
        present @ [MFN.unrepresented_marker_ascii element_ty]
      else
        present
    fun insert (element, set) = pred_setSyntax.mk_insert (element, set)
  in
    if all_unknown then
      MFN.unknown_marker (pred_setSyntax.mk_set_type element_ty)
    else
      List.foldr insert (pred_setSyntax.mk_empty element_ty) elements
  end

fun make_fun_or_set context maybe_opt ty pairs =
  let val (domain_ty, range_ty) = Type.dom_rng ty
  in
    if pred_setSyntax.is_set_type ty then
      make_set context maybe_opt domain_ty pairs
    else
      make_fun context domain_ty range_ty pairs
  end

fun factor_types ty =
  if MFH.is_pair_type ty then
    let val (left, right) = pairSyntax.dest_prod ty
    in factor_types left @ factor_types right end
  else
    [ty]

fun rebuild_value ty values =
  if MFH.is_pair_type ty then
    let
      val (left_ty, right_ty) = pairSyntax.dest_prod ty
      val (left, values) = rebuild_value left_ty values
      val (right, values) = rebuild_value right_ty values
    in
      (pairSyntax.mk_pair (left, right), values)
    end
  else
    case values of
        value :: rest => (value, rest)
      | [] => raise err "rebuild_value" "not enough selector values"

fun reconstruct_term (context as {scope, sel_names, ...} : context)
      maybe_opt ty representation tuples =
  let
    val {card_assigns, data_types, ofs, ...} = scope

    fun term_for_rep maybe_opt seen ty representation tuples =
      case (representation, tuples) of
          (MFR.Any, _) => MFN.unknown_marker ty
        | (MFR.Formula _, _) =>
            if null tuples then boolSyntax.F else boolSyntax.T
        | (MFR.Atom (card, offset), [[atom]]) =>
            if atom < offset orelse atom >= offset + card then
              raise MFR.REP ("Refute_ModelFinder_Model.term_for_rep",
                             [representation])
            else
              term_for_atom seen ty (atom - offset) card
        | (MFR.Struct [left_rep, right_rep], [tuple]) =>
            if not (MFH.is_pair_type ty) then
              raise err "term_for_rep" "Struct used for a non-product"
            else
              let
                val (left_ty, right_ty) = pairSyntax.dest_prod ty
                val (left_tuple, right_tuple) =
                  chop (MFR.arity_of_rep left_rep) tuple
                val left = term_for_rep true seen left_ty left_rep
                  [left_tuple]
                val right = term_for_rep true seen right_ty right_rep
                  [right_tuple]
              in
                pairSyntax.mk_pair (left, right)
              end
        | (MFR.Vect (card, range_rep), [tuple]) =>
            let
              val (domain_ty, range_ty) = Type.dom_rng ty
              val width = MFR.arity_of_rep range_rep
              val chunks = MFU.chunk_list width tuple
              val domains = List.tabulate (card, fn atom =>
                term_for_atom seen domain_ty atom card)
              val ranges = map (fn chunk =>
                term_for_rep true seen range_ty range_rep [chunk]) chunks
            in
              if length domains <> length ranges then
                raise err "term_for_rep" "malformed vector tuple"
              else
                make_fun_or_set context true ty
                  (ListPair.zip (domains, ranges))
            end
        | (MFR.Func (domain_rep, MFR.Formula _), _) =>
            let
              val (domain_ty, _) = Type.dom_rng ty
              val combinations = MFR.all_combinations_for_rep domain_rep
              val domains = map (fn tuple =>
                term_for_rep true seen domain_ty domain_rep [tuple])
                combinations
              val ranges = map (fn tuple =>
                if member_tuple tuple tuples then boolSyntax.T
                else boolSyntax.F) combinations
            in
              make_fun_or_set context maybe_opt ty
                (ListPair.zip (domains, ranges))
            end
        | (MFR.Func (domain_rep, range_rep), _) =>
            let
              val (domain_ty, range_ty) = Type.dom_rng ty
              val domain_width = MFR.arity_of_rep domain_rep
              val combinations = MFR.all_combinations_for_rep domain_rep
              (* Chop once and index by prefix, rather than re-chopping
                 every tuple for every combination. *)
              val tail_table = List.foldl
                (fn ((prefix, tail), table) =>
                   Redblackmap.insert (table, prefix,
                     tail :: Option.getOpt
                       (Redblackmap.peek (table, prefix), [])))
                (Redblackmap.mkDict (Portable.list_compare Int.compare))
                (map (chop domain_width) tuples)
              fun tails tuple =
                rev (Option.getOpt (Redblackmap.peek (tail_table, tuple), []))
              val domains = map (fn tuple =>
                term_for_rep false seen domain_ty domain_rep [tuple])
                combinations
              val ranges = map (fn tuple =>
                term_for_rep false seen range_ty range_rep (tails tuple))
                combinations
            in
              make_fun_or_set context maybe_opt ty
                (ListPair.zip (domains, ranges))
            end
        | (MFR.Opt inner, []) => MFN.unknown_marker ty
        | (MFR.Opt inner, _) => term_for_rep true seen ty inner tuples
        | _ => raise err "term_for_rep"
            ("cannot decode " ^ MFR.string_for_rep representation ^
             " from " ^ Int.toString (length tuples) ^ " tuples")

    and term_for_atom seen ty atom card =
      case Lib.total Type.dom_rng ty of
          SOME (domain_ty, range_ty) =>
            let
              val domain_card = MFH.card_of_type card_assigns domain_ty
              val range_card = MFH.card_of_type card_assigns range_ty
              val range_rep = MFR.Atom (range_card, 0)
              val tuple = MFU.nth_combination
                (MFU.replicate_list domain_card [(range_card, 0)]) atom
            in
              term_for_rep true seen ty
                (MFR.Vect (domain_card, range_rep)) [tuple]
            end
        | NONE =>
            if MFH.is_pair_type ty then
              let
                val (left_ty, right_ty) = pairSyntax.dest_prod ty
                val left_card = MFH.card_of_type card_assigns left_ty
                val right_card = card div left_card
                val left = term_for_atom seen left_ty
                  (atom div right_card) left_card
                val right = term_for_atom seen right_ty
                  (atom mod right_card) right_card
              in
                pairSyntax.mk_pair (left, right)
              end
            else if MFH.is_boolean_type ty then
              if atom = 0 then boolSyntax.F else boolSyntax.T
            else if same_type ty MFH.num_type then
              numSyntax.term_of_int atom
            else if same_type ty MFH.int_type then
              intSyntax.term_of_int
                (Arbint.fromInt (MFP.int_for_atom (card, 0) atom))
            else
              case MFS.data_type_spec data_types ty of
                  SOME spec =>
                    if #deep spec andalso not (null (#constrs spec)) then
                      term_for_data_type seen spec atom
                    else
                      atom_term context ty atom
                | NONE => atom_term context ty atom

    and term_for_data_type seen (spec : MFS.data_type_spec) atom =
      let
        val ty = #typ spec
        val real_atom = atom + MFS.offset_of_type ofs ty
        fun discriminator constructor =
          MFN.discr_prefix ^ MFH.constructor_name constructor
        fun is_constructor ({const, ...} : MFS.constr_spec) =
          member_tuple [real_atom]
            (tuples_for_nickname context (discriminator const))
        val constructor_spec =
          case List.find is_constructor (#constrs spec) of
              SOME found => found
            | NONE => raise err "term_for_data_type"
                "no discriminator selected a constructor"
        val constructor = #const constructor_spec
        val constructor_id = MFH.constructor_name constructor
        val argument_tys = MFH.constructor_arg_types constructor
        val flat_tys = List.concat (map factor_types argument_tys)

        fun selector_value (index, argument_ty) =
          let
            val nickname = MFN.sel_prefix_for index ^ constructor_id
            val name =
              case find_name sel_names nickname of
                  SOME found => found
                | NONE => raise err "term_for_data_type"
                    ("missing selector " ^ nickname)
            val range_rep = #2 (MFR.dest_Func (MFNT.rep_of name))
            val selected = List.mapPartial
              (fn owner :: rest =>
                    if owner = real_atom then SOME rest else NONE
                | [] => NONE)
              (tuples_for_name context name)
          in
            term_for_rep true ((ty, atom) :: seen) argument_ty
              range_rep selected
          end

        val flat_values = map selector_value
          (ListPair.zip
            (List.tabulate (length flat_tys, fn index => index), flat_tys))
        fun rebuild (argument_ty, (arguments, values)) =
          let val (argument, values) = rebuild_value argument_ty values
          in (argument :: arguments, values) end
        val (arguments, remaining) =
          List.foldl rebuild ([], flat_values) argument_tys
        val _ = if null remaining then () else
          raise err "term_for_data_type" "unused selector values"
      in
        Term.list_mk_comb (constructor, rev arguments)
      end
  in
    term_for_rep maybe_opt [] ty representation tuples
  end

fun term_for_rep {scope, atoms, sel_names, rel_table, bounds, maybe_opt,
                  ty, representation, tuples} =
  reconstruct_term
    {scope = scope, atoms = atoms, sel_names = sel_names,
     rel_table = rel_table, bounds = bounds, pool = new_atom_pool ()}
    maybe_opt ty representation tuples

fun same_free name ty term =
  case Lib.total Term.dest_var term of
      SOME (other, other_ty) => name = other andalso same_type ty other_ty
    | NONE => false

fun free_name_for_term free_names term =
  let val (name, ty) = Term.dest_var term
  in
    case List.find (fn candidate =>
           case candidate of
               MFNT.FreeName (other, other_ty, _) =>
                 name = other andalso same_type ty other_ty
             | _ => false) free_names of
        SOME found => found
      | NONE => MFNT.FreeName (name, ty, MFR.Any)
  end

fun lhs_for_constant name ty =
  let
    val original = MFN.original_name name
    val (thy_part, name_part) = MFN.strip_first_name_sep original
  in
    if thy_part <> "" andalso name_part <> "" then
      Term.mk_thy_const {Thy = thy_part, Name = name_part, Ty = ty}
    else
      Term.mk_var (original, ty)
  end handle HOL_ERR _ => Term.mk_var (MFN.original_name name, ty)

fun eval_index name =
  if String.isPrefix MFN.eval_prefix name then
    Int.fromString (String.extract (name, size MFN.eval_prefix, NONE))
  else
    NONE

fun reconstruct {scope, atoms, real_frees, eval_terms, free_names,
                 sel_names, nonsel_names, rel_table, bounds} =
  let
    val context =
      {scope = scope, atoms = atoms, sel_names = sel_names,
       rel_table = rel_table, bounds = bounds, pool = new_atom_pool ()}

    fun decode name =
      case MFNT.rep_of name of
          MFR.Any => MFN.unknown_marker (MFNT.type_of name)
        | representation => reconstruct_term context
            (not (MFNT.is_fully_representable_set name))
            (MFNT.type_of name) representation
            (tuples_for_name context name)

    fun binding term =
      let val name = free_name_for_term free_names term
      in (term, decode name) end

    fun classify (name, (evals, skolems, consts)) =
      let
        val nickname = MFNT.nickname_of name
        val value = decode name
      in
        if MFNT.is_skolem_name name then
          (evals, (MFN.original_name nickname, value) :: skolems, consts)
        else
          case eval_index nickname of
              SOME index =>
                if index < length eval_terms then
                  ((List.nth (eval_terms, index), value) :: evals,
                   skolems, consts)
                else
                  (evals, skolems, consts)
            | NONE =>
                (evals, skolems,
                 (lhs_for_constant nickname (MFNT.type_of name), value) ::
                 consts)
      end

    val (evals, skolems, consts) =
      List.foldl classify ([], [], []) nonsel_names

    fun values_for_type (spec : MFS.data_type_spec) =
      let
        val ty = #typ spec
        val card = #card spec
        val offset = MFS.offset_of_type (#ofs scope) ty
        val values = List.tabulate (card, fn index =>
          reconstruct_term context false ty (MFR.Atom (card, offset))
            [[offset + index]])
        val complete = MFU.fun_from_pair (#complete spec) false
      in
        (ty, values, complete)
      end

    val deep_types = List.filter #deep (#data_types scope)
    fun has_type ty = List.exists (fn (spec : MFS.data_type_spec) =>
      same_type (#typ spec) ty) deep_types
    fun integer_type ty =
      case MFH.assignment_lookup (#card_assigns scope) ty of
          SOME card =>
            if has_type ty then [] else
              [{typ = ty, card = card, co = false, self_rec = true,
                complete = (false, false), concrete = (true, true),
                deep = true, constrs = []} : MFS.data_type_spec]
        | NONE => []
    fun type_variable_spec (ty, card) =
      if Type.is_vartype ty then
        [{typ = ty, card = card, co = false, self_rec = false,
          complete = (true, true), concrete = (true, true), deep = true,
          constrs = []} : MFS.data_type_spec]
      else
        []
    val report_types = deep_types @
      List.concat (map integer_type [MFH.num_type, MFH.int_type]) @
      List.concat (map type_variable_spec (#card_assigns scope))
    val types = map values_for_type report_types
  in
    {bindings = map binding real_frees,
     evals = rev evals,
     skolems = rev skolems,
     consts = rev consts,
     types = types,
     codatatypes_ok = true}
  end

fun model_report ({skolems, consts, types, ...} : reconstruction) =
  {skolems = skolems, consts = consts, types = types}

fun replace_irrelevant term =
  if combinSyntax.is_K_1 term then
    let
      val body = combinSyntax.dest_K_1 term
      val (domain_ty, _) = Type.dom_rng (Term.type_of term)
    in
      if Term.is_var body andalso #1 (Term.dest_var body) = "_" then
        combinSyntax.mk_K_1 (boolSyntax.mk_arb (Term.type_of body), domain_ty)
      else
        combinSyntax.mk_K_1 (replace_irrelevant body, domain_ty)
    end
  else if Term.is_var term then
    term
  else if Term.is_abs term then
    let val (variable, body) = Term.dest_abs term
    in Term.mk_abs (variable, replace_irrelevant body) end
  else if Term.is_comb term then
    let val (function, argument) = Term.dest_comb term
    in Term.mk_comb (replace_irrelevant function,
                     replace_irrelevant argument) end
  else
    term

fun certification_env bindings =
  let
    val copied = map (fn (variable, value) =>
      (variable, replace_irrelevant value)) bindings
  in
    if List.all (null o Term.free_vars_lr o #2) copied then SOME copied
    else NONE
  end

fun rf_type card =
  Type.mk_thy_type
    {Thy = "refute", Tyop = "rf" ^ Int.toString card, Args = []}

fun rf_constructor card serial =
  Term.prim_mk_const
    {Thy = "refute", Name = "rf" ^ Int.toString card ^ "_" ^
       Int.toString serial}

(* Certification is deliberately performed on a private, monomorphic copy.
   A native goal type variable with scope cardinality k is transported to
   the static rf_k enum and its displayed fake atoms are transported to the
   corresponding constructors.  The reconstructed model itself remains
   polymorphic, so none of these rf terms escape into model display. *)
fun certification_copy scope original eval_terms bindings =
  let
    val tyvars = Lib.U (map Term.type_vars_in_term
      (original :: eval_terms @
       List.concat (map (fn (left, right) => [left, right]) bindings)))
    fun scope_card ty =
      case scope of
          SOME assignments =>
            Option.map #2 (List.find (fn (other, _) => same_type ty other)
              assignments)
        | NONE => NONE
    fun collect [] = SOME []
      | collect (tyvar :: rest) =
          (case (scope_card tyvar, collect rest) of
               (SOME card, SOME rows) =>
                 if card >= 1 andalso card <= 6 then
                   SOME ((tyvar, card) :: rows)
                 else NONE
             | _ => NONE)
    fun atom_substitutions (tyvar, card) =
      let
        val ty = rf_type card
      in
        List.tabulate (card, fn index =>
          {redex = MFN.fake_atom (index + 1) ty,
           residue = rf_constructor card (index + 1)})
      end
  in
    if null tyvars then
      Option.map (fn env =>
        {original = original, eval_terms = eval_terms, env = env,
         polymorphic = false}) (certification_env bindings)
    else
      case collect tyvars of
          NONE => NONE
        | SOME rows =>
            let
              val theta = map (fn (tyvar, card) =>
                {redex = tyvar, residue = rf_type card}) rows
              val atoms = List.concat (map atom_substitutions rows)
              fun copy_value value = Term.subst atoms
                (Term.inst theta (replace_irrelevant value))
              val env = map (fn (variable, value) =>
                (Term.inst theta variable, copy_value value)) bindings
            in
              if List.all (null o Term.free_vars_lr o #2) env then
                SOME
                  {original = Term.inst theta original,
                   eval_terms = map (Term.inst theta) eval_terms,
                   env = env, polymorphic = true}
              else NONE
            end
  end

fun certifiable executable bindings =
  executable andalso Option.isSome (certification_env bindings)

fun genuine_means_genuine
      {got_all_mono_user_axioms, no_poly_user_axioms, wfs,
       total_consts} =
  got_all_mono_user_axioms andalso no_poly_user_axioms andalso
  List.all not wfs andalso total_consts <> SOME true

fun try_again_reasons options = map (fn option =>
  "Try again with " ^ option) options

fun replace_cex (cex : Refute_Core.counterexample) certainty bindings
      evals cert model =
  {backend = #backend cex, substrate = #substrate cex,
   certainty = certainty, bindings = bindings, evals = evals,
   cert = cert, scope = #scope cex, model = model, stats = #stats cex}

fun decoded_eval evals term =
  Option.map #2 (List.find (fn (candidate, _) =>
    Term.aconv candidate term) evals)

fun merge_evals decoded exact = map (fn (term, value) =>
  if is_unknown value orelse Term.aconv value term then
    (term, Option.getOpt (decoded_eval decoded term, value))
  else
    (term, value)) exact

fun fallback_certainty sound genuine reasons =
  if sound andalso genuine then Refute_Core.Genuine
  else if sound then Refute_Core.QuasiGenuine reasons
  else Refute_Core.Potential reasons

fun certify {executable, original, eval_terms,
             reconstruction = reconstructed, cex, sound,
             genuine_means_genuine = genuine, reasons} =
  let
    val {bindings, evals, ...} = reconstructed
    val model = SOME (model_report reconstructed)
    val base = replace_cex cex (fallback_certainty sound genuine reasons)
      bindings evals NONE model
  in
    case if executable then
           certification_copy (#scope cex) original eval_terms bindings
         else NONE of
        NONE => Keep base
      | SOME {original = cert_original, eval_terms = cert_evals,
              env, polymorphic} =>
          (case Refute_Cert.certify
              {original = cert_original, evals = cert_evals, env = env,
               cex = base} of
               Refute_Cert.Certified certified =>
                 Keep (replace_cex certified Refute_Core.Genuine bindings
                   (if polymorphic then evals
                    else merge_evals evals (#evals certified))
                   (#cert certified) model)
             | Refute_Cert.Potential potential =>
                 Keep (replace_cex potential (#certainty potential) bindings
                   evals NONE model)
             | Refute_Cert.Discarded =>
                 if sound then
                   let
                     val reason =
                       "certification refuted the model — please report"
                     val _ = Refute_Core.Private.say 1
                       ("Refute warning: " ^ reason ^ "\n")
                   in
                     Keep (replace_cex base
                       (Refute_Core.Potential [reason]) bindings evals NONE
                       model)
                   end
                 else
                   Drop)
  end

end
