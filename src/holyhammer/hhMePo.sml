(* ========================================================================= *)
(* FILE          : hhMePo.sml                                                *)
(* DESCRIPTION   : MePo (Meng-Paulson) relevance filter                      *)
(* AUTHORS       : Jia Meng and Jasmin Blanchette (Isabelle/HOL)             *)
(* PORTED FROM   : Isabelle's sledgehammer_mepo.ML, faithfully.  The caches  *)
(*                 of facts and weights and the restriction of a context are *)
(*                 new.  Only the simp and local stature bonuses apply, the  *)
(*                 goal's assumptions stand for the chained facts, a goal    *)
(*                 without ordinary constants falls back to those of the     *)
(*                 current theory's facts, and the theory pseudo-constant is *)
(*                 added even when both theory weights of the fudge are 0.   *)
(* ========================================================================= *)

structure hhMePo :> hhMePo =
struct

open HolKernel boolSyntax aiLib

type ptype = int * hol_type list
type pconst = string * ptype
type pconst_table = (string, ptype list) Redblackmap.dict
type ptype_counts = (ptype, int) Redblackmap.dict
type frequency_table = (string, ptype_counts) Redblackmap.dict

type fudge =
  {local_const_multiplier : real,
   worse_irrel_freq : real,
   higher_order_irrel_weight : real,
   abs_rel_weight : real,
   abs_irrel_weight : real,
   theory_const_rel_weight : real,
   theory_const_irrel_weight : real,
   chained_const_irrel_weight : real,
   intro_bonus : real,
   elim_bonus : real,
   simp_bonus : real,
   local_bonus : real,
   assum_bonus : real,
   chained_bonus : real,
   max_imperfect : real,
   max_imperfect_exp : real,
   threshold_divisor : real,
   ridiculous_threshold : real,
   fact_threshold0 : real,
   fact_threshold1 : real,
   perfect_threshold : real,
   hopeless_threshold : real,
   special_fact_index : int,
   hopeless_iter : int}

(* Isabelle's defaults, in one record so that tuning replaces them whole. *)
val default_fudge : fudge =
  {local_const_multiplier = 1.5,
   worse_irrel_freq = 100.0,
   higher_order_irrel_weight = 1.05,
   abs_rel_weight = 0.5,
   abs_irrel_weight = 2.0,
   theory_const_rel_weight = 0.5,
   theory_const_irrel_weight = 0.25,
   chained_const_irrel_weight = 0.25,
   intro_bonus = 0.15,
   elim_bonus = 0.15,
   simp_bonus = 0.15,
   local_bonus = 0.55,
   assum_bonus = 1.05,
   chained_bonus = 1.5,
   max_imperfect = 11.5,
   max_imperfect_exp = 1.0,
   threshold_divisor = 2.0,
   ridiculous_threshold = 0.1,
   fact_threshold0 = 0.45,
   fact_threshold1 = 0.85,
   perfect_threshold = 0.99999,
   hopeless_threshold = 0.001,
   special_fact_index = 45,
   hopeless_iter = 5}

val pseudo_abs_name = "%abs"
fun pseudo_theory_name thy = "%thy%" ^ thy

fun order_of_type ty =
  case total Type.dom_rng ty of
      SOME (domain, range) =>
        Int.max (order_of_type domain + 1, order_of_type range)
    | NONE =>
        if Type.is_type ty then
          foldl Int.max 0 (map order_of_type (#Args (Type.dest_thy_type ty)))
        else 0

(* A type operator is identified by (Thy, Tyop).  Comparing the pair
   lexicographically orders heads as String.compare orders Thy ^ "$" ^ Tyop,
   since theory names contain no character below "$". *)
fun type_name ty =
  let val {Thy, Tyop, Args} = Type.dest_thy_type ty in
    ((Thy, Tyop), Args)
  end

fun head_compare ((thy, tyop), (thy', tyop')) =
  case String.compare (thy, thy') of
      EQUAL => String.compare (tyop, tyop')
    | order => order

fun patternT_eq (pattern, instance) =
  if Type.is_vartype pattern then Type.is_vartype instance
  else if Type.is_type pattern andalso Type.is_type instance then
    let
      val (name, patterns) = type_name pattern
      val (name', instances) = type_name instance
    in
      name = name' andalso patternsT_eq (patterns, instances)
    end
  else false
and patternsT_eq ([], []) = true
  | patternsT_eq (pattern :: patterns, instance :: instances) =
      patternT_eq (pattern, instance) andalso
      patternsT_eq (patterns, instances)
  | patternsT_eq _ = false

fun ptype_eq ((order, patterns), (order', instances)) =
  order = order' andalso patternsT_eq (patterns, instances)

fun match_patternT (pattern, instance) =
  if Type.is_vartype pattern then true
  else if Type.is_type pattern andalso Type.is_type instance then
    let
      val (name, patterns) = type_name pattern
      val (name', instances) = type_name instance
    in
      name = name' andalso match_patternsT (patterns, instances)
    end
  else false
and match_patternsT (_, []) = true
  | match_patternsT ([], _ :: _) = false
  | match_patternsT (pattern :: patterns, instance :: instances) =
      match_patternT (pattern, instance) andalso
      match_patternsT (patterns, instances)

fun match_ptype ((_, patterns), (_, instances)) =
  match_patternsT (patterns, instances)

fun patternT_compare (left, right) =
  if Type.is_vartype left then
    if Type.is_vartype right then EQUAL else LESS
  else if Type.is_vartype right then GREATER
  else
    let
      val (name, arguments) = type_name left
      val (name', arguments') = type_name right
    in
      case head_compare (name, name') of
          EQUAL => List.collate patternT_compare (arguments, arguments')
        | order => order
    end

fun ptype_compare ((order, patterns), (order', patterns')) =
  case List.collate patternT_compare (patterns, patterns') of
      EQUAL => Int.compare (order, order')
    | result => result

fun empty_pconst_table () = dempty String.compare

fun new_pconst_patterns (name, ptype) table =
  case Redblackmap.peek (table, name) of
      NONE => SOME [ptype]
    | SOME old =>
        if List.exists (fn old_ptype => ptype_eq (ptype, old_ptype)) old
        then NONE
        else SOME (ptype :: old)

fun add_pconst_to_table (pconst as (name, _)) table =
  case new_pconst_patterns pconst table of
      NONE => table
    | SOME patterns => dadd name patterns table

fun const_ptype tm =
  let
    val {Thy, Name, Ty} = dest_thy_const tm
    val generic = type_of (prim_mk_const {Thy = Thy, Name = Name})
    val arguments =
      case total (Type.match_type generic) Ty of
          NONE => []
        | SOME substitution =>
            map (Type.type_subst substitution) (Type.type_vars generic)
  in
    (Thy ^ "$" ^ Name, (order_of_type Ty, arguments))
  end

fun free_ptype tm =
  let val (name, ty) = dest_var tm in
    (name, (order_of_type ty, []))
  end

fun irrelevant_const name =
  List.exists (fn irrelevant => irrelevant = name)
    ["min$=", "min$==>", "bool$T", "bool$F", "bool$~",
     "bool$/\\", "bool$\\/", "bool$COND", "bool$LET"]

fun set_const name = name = "bool$IN" orelse name = "pred_set$GSPEC"

fun add_pconsts_with read_const thy tm initial =
  let
    fun add pconst table = add_pconst_to_table pconst table

    fun do_const bound head arguments table =
      let val pconst as (name, _) = read_const head in
        if set_const name then foldl (do_term bound) table arguments
        else
          foldl (do_term bound)
            (if irrelevant_const name then table else add pconst table)
            arguments
      end

    and do_term bound (term, table) =
      do_term_ext bound false term table

    and do_term_ext bound ext_arg term table =
      let val (head, arguments) = strip_comb term in
        if is_const head then do_const bound head arguments table
        else if is_var head then
          foldl (do_term bound)
            (if List.exists (fn variable => aconv variable head) bound then
               table
             else add (free_ptype head) table)
            arguments
        else if is_abs head then
          let
            (* HOL's destructor opens the binder as a free variable.  Keep
               an explicit scope so it retains Isabelle Bound semantics. *)
            val (variable, body) = dest_abs head
            val table' =
              if null arguments andalso not ext_arg then
                add (pseudo_abs_name,
                     (order_of_type (type_of variable) + 1, [])) table
              else table
            val table'' = do_term (variable :: bound) (body, table')
          in
            foldl (do_term bound) table'' arguments
          end
        else foldl (do_term bound) table arguments
      end

    and do_term_or_formula bound ext_arg term table =
      if type_of term = Type.bool then do_formula bound term table
      else do_term_ext bound ext_arg term table

    and do_formula bound term table =
      if is_forall term then do_quantifier dest_forall bound term table
      else if is_exists term then do_quantifier dest_exists bound term table
      else if is_exists1 term then
        do_quantifier dest_exists1 bound term table
      else if is_imp_only term then
        let val (left, right) = dest_imp_only term in
          do_formula bound right (do_formula bound left table)
        end
      else if is_conj term then
        let val (left, right) = dest_conj term in
          do_formula bound right (do_formula bound left table)
        end
      else if is_disj term then
        let val (left, right) = dest_disj term in
          do_formula bound right (do_formula bound left table)
        end
      else if is_neg term then do_formula bound (dest_neg term) table
      else if is_eq term then
        let val (left, right) = dest_eq term in
          do_term_or_formula bound true right
            (do_term_or_formula bound false left table)
        end
      else if is_cond term then
        let
          val (condition, then_branch, else_branch) = dest_cond term
          val table' = do_formula bound condition table
          val table'' =
            do_term_or_formula bound false then_branch table'
        in
          do_term_or_formula bound false else_branch table''
        end
      else if is_res_forall term then
        do_restricted dest_res_forall bound term table
      else if is_res_exists term then
        do_restricted dest_res_exists bound term table
      else do_term_ext bound false term table

    and do_quantifier dest bound term table =
      let val (variable, body) = dest term in
        do_formula (variable :: bound) body table
      end

    and do_restricted dest bound term table =
      let
        val (variable, restriction, body) = dest term
        val restricted = mk_comb (restriction, variable)
        val body_bound = variable :: bound
      in
        do_formula body_bound body
          (do_formula body_bound restricted table)
      end

    val with_theory =
      add (pseudo_theory_name thy, (0, [])) initial
  in
    do_formula [] tm with_theory
  end

val add_pconsts_in_term = add_pconsts_with const_ptype

fun pconsts_of_table table =
  dfoldl
    (fn (name, ptypes, result) =>
      foldl (fn (ptype, entries) => (name, ptype) :: entries)
        result ptypes)
    [] table

fun pconsts_in_term thy tm =
  pconsts_of_table (add_pconsts_in_term thy tm (empty_pconst_table ()))

fun pconst_hyper_mem match table (name, ptype) =
  case Redblackmap.peek (table, name) of
      NONE => false
    | SOME ptypes => List.exists (fn other => match (ptype, other)) ptypes

fun empty_frequency_table () = dempty String.compare

fun increment_frequency (name, ptype) table =
  let
    val counts =
      case Redblackmap.peek (table, name) of
          SOME old => old
        | NONE => dempty ptype_compare
    val count =
      case Redblackmap.peek (counts, ptype) of
          SOME old => old
        | NONE => 0
  in
    dadd name (dadd ptype (count + 1) counts) table
  end

fun count_term_consts read_const bound (tm, table) =
  let val (head, arguments) = strip_comb tm in
    if is_const head then
      foldl (count_term_consts read_const bound)
        (increment_frequency (read_const head) table) arguments
    else if is_var head then
      foldl (count_term_consts read_const bound)
        (if List.exists (fn variable => aconv variable head) bound then table
         else increment_frequency (free_ptype head) table)
        arguments
    else if is_abs head then
      let
        val (variable, body) = dest_abs head
        val table' = count_term_consts read_const (variable :: bound)
          (body, table)
      in
        foldl (count_term_consts read_const bound) table' arguments
      end
    else foldl (count_term_consts read_const bound) table arguments
  end

fun count_fact read_const ((thy, term), table) =
  count_term_consts read_const []
    (term, increment_frequency (pseudo_theory_name thy, (0, [])) table)

fun count_fact_consts facts =
  foldl (count_fact const_ptype) (empty_frequency_table ()) facts

fun pconst_freq match table (name, ptype) =
  case Redblackmap.peek (table, name) of
      NONE => 0
    | SOME counts =>
        dfoldl
          (fn (other, count, total) =>
            if match (ptype, other) then total + count else total)
          0 counts

fun frequency_entries table =
  dfoldl
    (fn (name, counts, result) =>
      dfoldl (fn (ptype, count, entries) =>
        ((name, ptype), count) :: entries) result counts)
    [] table

fun pow_int _ 0 = 1.0
  | pow_int base exponent =
      if exponent > 0 then base * pow_int base (exponent - 1)
      else pow_int base (exponent + 1) / base

fun rel_weight_for _ frequency =
  1.0 + 2.0 / Math.ln (Real.fromInt frequency + 1.0)

fun irrel_weight_for
      ({worse_irrel_freq, higher_order_irrel_weight, ...} : fudge)
      order frequency =
  let
    val k = Real.ceil worse_irrel_freq
    val weight =
      if frequency < k then
        Math.ln (Real.fromInt (frequency + 1)) /
        Math.ln worse_irrel_freq
      else
        rel_weight_for order frequency / rel_weight_for order k
  in
    weight * pow_int higher_order_irrel_weight (order - 1)
  end

fun is_global_const name = String.isSubstring "$" name

fun generic_pconst_weight local_multiplier abs_weight theory_weight
      chained_weight weight_for match frequency_table chained_table
      (pconst as (name, (order, _))) =
  if name = pseudo_abs_name then abs_weight
  else if String.isPrefix "%thy%" name then theory_weight
  else
    let
      val locality = if is_global_const name then 1.0 else local_multiplier
      val frequency = pconst_freq match frequency_table pconst
      val chained =
        if chained_weight < 1.0 andalso
           pconst_hyper_mem match_ptype chained_table pconst
        then chained_weight
        else 1.0
    in
      locality * weight_for order frequency * chained
    end

fun rel_pconst_weight
      ({local_const_multiplier, abs_rel_weight,
        theory_const_rel_weight, ...} : fudge) frequency_table pconst =
  generic_pconst_weight local_const_multiplier abs_rel_weight
    theory_const_rel_weight 0.0 rel_weight_for match_ptype
    frequency_table (empty_pconst_table ()) pconst

fun swapped_match (left, right) = match_ptype (right, left)

fun irrel_pconst_weight
      (fudge as
       {local_const_multiplier, abs_irrel_weight,
        theory_const_irrel_weight, chained_const_irrel_weight, ...})
      frequency_table chained_table pconst =
  generic_pconst_weight local_const_multiplier abs_irrel_weight
    theory_const_irrel_weight chained_const_irrel_weight
    (irrel_weight_for fudge) swapped_match frequency_table chained_table
    pconst

(* Isabelle's Intro, Elim, Assum and Chained bonuses have no HOL4 stature. *)
fun stature_bonus ({simp_bonus, local_bonus, ...} : fudge)
      ({simp, local_, ...} : hhStature.stature) =
  if simp then simp_bonus else if local_ then local_bonus else 0.0

fun pconst_mem pconst_of match pconsts (name, ptype) =
  List.exists
    (fn entry =>
      let val (other_name, other_ptype) = pconst_of entry in
        name = other_name andalso match (ptype, other_ptype)
      end)
    pconsts

fun odd_const_name name =
  name = pseudo_abs_name orelse String.isPrefix "%thy%" name

fun score_fact fudge pconst_of rel_weight_of irrel_weight_of is_relevant
      is_irrelevant stature fact_pconsts =
  let
    val (relevant, rest) =
      List.partition is_relevant fact_pconsts
    val irrelevant =
      if null relevant then []
      else List.filter is_irrelevant rest
    fun odd entry = odd_const_name (#1 (pconst_of entry))
  in
    if null relevant orelse
       (List.all odd relevant andalso List.all odd irrelevant) then 0.0
    else
      let
        val irrelevant' =
          List.filter (not o pconst_mem pconst_of swapped_match relevant o
            pconst_of) irrelevant
        val rel_weight =
          foldl
            (fn (pconst, total) =>
              total + rel_weight_of pconst)
            0.0 relevant
        val irrel_weight =
          foldl
            (fn (pconst, total) =>
              total + irrel_weight_of pconst)
            (~ (stature_bonus fudge stature)) irrelevant'
        val result = rel_weight / (rel_weight + irrel_weight)
      in
        if Real.isFinite result then result else 0.0
      end
  end

fun fact_weight fudge stature frequency_table rel_table chained_table =
  score_fact fudge I (rel_pconst_weight fudge frequency_table)
    (irrel_pconst_weight fudge frequency_table chained_table)
    (pconst_hyper_mem match_ptype rel_table)
    (not o pconst_hyper_mem swapped_match rel_table) stature

datatype weight_cache = Dense of int | Sparse

fun memo_pconst (Dense count) compute =
      let val cache = Array.array (count, NONE) in
        fn (pconst, index) =>
          case Array.sub (cache, index) of
              SOME value => value
            | NONE =>
                let val value = compute pconst in
                  Array.update (cache, index, SOME value);
                  value
                end
      end
  | memo_pconst Sparse compute =
      let val cache = ref (Intmap.empty ()) in
        fn (pconst, index) =>
          case Intmap.peek (!cache, index) of
              SOME value => value
            | NONE =>
                let val value = compute pconst in
                  cache := Intmap.insert (!cache, index, value);
                  value
                end
      end

val split_at = part_n

fun take count items = #1 (split_at count items)

fun take_most_relevant (fudge : fudge)
      {max_facts, remaining_max, candidates} =
  let
    val ratio =
      Real.fromInt remaining_max / Real.fromInt max_facts
    val imperfect_limit =
      Real.ceil (Math.pow (#max_imperfect fudge,
        Math.pow (ratio, #max_imperfect_exp fudge)))
    val sorted = Listsort.sort
      (fn ((_, left), (_, right)) => Real.compare (right, left))
      candidates
    fun split_perfect (prefix, []) = (rev prefix, [])
      | split_perfect (prefix, items as (item as (_, weight)) :: rest) =
          if weight > #perfect_threshold fudge then
            split_perfect (item :: prefix, rest)
          else (rev prefix, items)
    val (perfect, imperfect) = split_perfect ([], sorted)
    val (best_imperfect, later_imperfect) =
      split_at imperfect_limit imperfect
    val (accepted, overflow) =
      split_at remaining_max (perfect @ best_imperfect)
  in
    (accepted, overflow @ later_imperfect)
  end

fun purge_hopeless (fudge : fudge) iteration weighted =
  if iteration = #hopeless_iter fudge then
    List.filter
      (fn (_, weight) => weight >= #hopeless_threshold fudge) weighted
  else weighted

(* counts is the fact's own contribution to the frequency table, so that
   restricted contexts can adjust a table instead of re-walking terms.
   The pconst indices belong to the context. Each ranking computes its own
   weights because frequencies and chained assumptions can differ. *)
type cached_fact =
  {thmid : string, theory : string, concl : term,
   pconsts : (pconst * int) list, counts : (pconst * int) list,
   stature : hhStature.stature}

type context =
  {current_theory : string, facts : cached_fact list,
   fact_index : cached_fact hhFactIndex.index,
   special_facts : cached_fact list,
   frequency_table : frequency_table Susp.susp, weight_cache : weight_cache}

fun context_from_facts current_theory facts special_facts frequency_table
      weight_cache =
  {current_theory = current_theory, facts = facts,
   fact_index = hhFactIndex.create #thmid facts,
   special_facts = special_facts,
   frequency_table = frequency_table, weight_cache = weight_cache} : context

val special_set_thmids =
  ["pred_setTheory.SPECIFICATION",
   "pred_setTheory.GSPECIFICATION", "boolTheory.IN_DEF"]
val ext_thmid = "boolTheory.EQ_EXT"

fun is_special_set_thmid thmid =
  List.exists (fn name => name = thmid) special_set_thmids

(* A restricted pool keeps the original pconst indices but uses at most as
   many as its facts hold.  Use a map when that bound, counted only up to
   the cutoff, is under 1/128 of the array. *)
fun restricted_weight_cache Sparse _ = Sparse
  | restricted_weight_cache (dense as Dense count) facts =
      let
        fun fits _ [] = true
          | fits remaining ((fact : cached_fact) :: rest) =
              let val left = remaining - length (#pconsts fact) in
                left >= 0 andalso fits left rest
              end
      in
        if fits (count div 128) facts then Sparse else dense
      end

fun cache_fact read_const index_pconst {thmid, theory, concl, stature} =
  {thmid = thmid, theory = theory, concl = concl,
   pconsts = map index_pconst (pconsts_of_table
     (add_pconsts_with read_const theory concl (empty_pconst_table ()))),
   counts = frequency_entries
     (count_fact read_const ((theory, concl), empty_frequency_table ())),
   stature = stature}

(* Entries never hold zero counts or empty count tables, whichever way the
   table was reached. *)
fun adjust_frequency delta ((name, ptype), amount) table =
  let
    val counts =
      case Redblackmap.peek (table, name) of
          SOME old => old
        | NONE => dempty ptype_compare
    val count =
      (case Redblackmap.peek (counts, ptype) of
           SOME old => old
         | NONE => 0) + delta * amount
    val counts' =
      if count = 0 then drem ptype counts else dadd ptype count counts
  in
    if dlength counts' = 0 then drem name table
    else dadd name counts' table
  end

fun adjust_by_facts delta facts table =
  foldl (fn (fact : cached_fact, table) =>
    foldl (fn (entry, table) => adjust_frequency delta entry table)
      table (#counts fact)) table facts

fun frequency_of_facts facts =
  adjust_by_facts 1 facts (empty_frequency_table ())

fun make_deferred_context {current_theory, facts} =
  let
    fun compare ((name, ptype), (name', ptype')) =
      case String.compare (name, name') of
          EQUAL => ptype_compare (ptype, ptype')
        | order => order
    val indices = ref (dempty compare)
    val const_types = ref (dempty Term.compare)
    fun read_const term =
      case Redblackmap.peek (!const_types, term) of
          SOME pconst => pconst
        | NONE =>
            let val pconst = const_ptype term in
              const_types := dadd term pconst (!const_types);
              pconst
            end
    fun index_pconst pconst =
      case Redblackmap.peek (!indices, pconst) of
          SOME entry => entry
        | NONE =>
            let val entry = (pconst, dlength (!indices)) in
              indices := dadd pconst entry (!indices);
              entry
            end
    val specials = ref []
    fun cache (fact as {thmid, ...}) =
      let val cached = cache_fact read_const index_pconst fact in
        if thmid = ext_thmid orelse is_special_set_thmid thmid
        then specials := cached :: !specials else ();
        cached
      end
    val cached = map cache facts
    val frequency = Susp.delay (fn () => frequency_of_facts cached)
  in
    context_from_facts current_theory cached (rev (!specials)) frequency
      (Dense (dlength (!indices)))
  end

fun prepare_frequencies (context : context) =
  ignore (Susp.force (#frequency_table context))

fun prepare_context context = (prepare_frequencies context; context)

fun make_context arguments = prepare_context (make_deferred_context arguments)

fun theory_of_thmid thmid =
  case total (split_string "Theory.") thmid of
      SOME (theory, _) => theory
    | NONE => Theory.current_theory ()

fun create_deferred_context_from_conclusions current conclusions =
  let
    fun fact (thmid, concl, stature) =
      {thmid = thmid, theory = theory_of_thmid thmid,
       concl = concl, stature = stature}
  in
    make_deferred_context
      {current_theory = current, facts = map fact conclusions}
  end

fun create_context_from_conclusions current conclusions =
  prepare_context
    (create_deferred_context_from_conclusions current conclusions)

fun create_context_for current (_, thm_features) statures =
  let
    fun fetch (thmid, _) =
      case total mlThmData.thm_of_name thmid of
          SOME (SOME (_, theorem)) =>
            SOME (thmid, Thm.concl theorem,
                  hhStature.stature_of statures thmid)
        | _ => NONE
  in
    create_context_from_conclusions current
      (List.mapPartial fetch thm_features)
  end

fun create_context thmdata statures =
  create_context_for (Theory.current_theory ()) thmdata statures

fun context_thmids ({facts, ...} : context) = map #thmid facts

fun restrict_context_to
    (context as {current_theory, facts, fact_index, special_facts,
      frequency_table, weight_cache} : context)
    wanted =
  let
    fun permitted (fact : cached_fact) = dmem (#thmid fact) wanted
    fun restrict restricted frequency =
      context_from_facts current_theory restricted
        (List.filter permitted special_facts) (Susp.delay frequency)
        (restricted_weight_cache weight_cache restricted)
    fun rebuild restricted =
      restrict restricted (fn () => frequency_of_facts restricted)
  in
    case hhFactIndex.select_sparse fact_index wanted of
        SOME restricted => rebuild restricted
      | NONE =>
          let val (restricted, excluded) = List.partition permitted facts in
            if null excluded then context
            else if length excluded < length restricted then
              restrict restricted (fn () =>
                adjust_by_facts ~1 excluded (Susp.force frequency_table))
            else rebuild restricted
          end
  end

fun restrict_context context thmids =
  restrict_context_to context
    (foldl (fn (thmid, set) => dadd thmid () set)
      (dempty String.compare) thmids)

fun add_fact_pconsts fact table =
  foldl (fn ((pconst, _), result) => add_pconst_to_table pconst result)
    table (#pconsts fact)

fun add_relevance (fact : cached_fact, state) =
  let
    fun add ((pconst as (name, _), _), state as (table, changed)) =
      case new_pconst_patterns pconst table of
          NONE => state
        | SOME patterns =>
            (dadd name patterns table, Redblackset.add (changed, name))
  in
    foldl add state (#pconsts fact)
  end

fun widely_irrelevant name =
  irrelevant_const name orelse
  List.exists (fn logical => name = logical)
    ["bool$!", "bool$?", "bool$?!", "bool$RES_FORALL",
     "bool$RES_EXISTS"]

fun could_benefit_from_ext facts =
  let
    fun consider term table =
      let
        fun walk tm result =
          case result of
              NONE => NONE
            | SOME arities =>
                let val (head, operands) = strip_comb tm in
                  if is_const head then
                    let
                      val name = #Thy (dest_thy_const head) ^ "$" ^
                        #Name (dest_thy_const head)
                      val arity = length operands
                      val arities' =
                        if widely_irrelevant name then SOME arities
                        else
                          (case Redblackmap.peek (arities, name) of
                               NONE => SOME (dadd name arity arities)
                             | SOME old =>
                                 if old = arity then SOME arities else NONE)
                    in
                      foldl
                        (fn (operand, state) => walk operand state)
                        arities' operands
                    end
                  else
                    foldl
                      (fn (operand, state) => walk operand state)
                      (SOME arities) operands
                end
      in
        walk term table
      end
  in
    case foldl
      (fn (fact, table) => consider (#concl fact) table)
      (SOME (dempty String.compare)) facts of
        NONE => true
      | SOME _ => false
  end

fun term_uses_set_const term =
  let
    fun uses tm =
      let val (head, arguments) = strip_comb tm in
        (is_const head andalso
         let val {Thy, Name, ...} = dest_thy_const head in
           set_const (Thy ^ "$" ^ Name)
         end) orelse List.exists uses arguments orelse
        (is_abs head andalso uses (#2 (dest_abs head)))
      end
  in
    uses term
  end

fun insert_special_facts _ _ [] _ accepted = accepted
  | insert_special_facts (fudge : fudge) max_facts special_facts goal_terms
      accepted =
    let
      val uses_set =
        List.exists (is_special_set_thmid o #thmid) special_facts andalso
        (List.exists term_uses_set_const goal_terms orelse
         List.exists (term_uses_set_const o #concl) accepted)
      val uses_ext =
        List.exists (fn fact => #thmid fact = ext_thmid) special_facts andalso
        could_benefit_from_ext accepted
      val wanted =
        (if uses_ext then [ext_thmid] else []) @
        (if uses_set then special_set_thmids else [])
      fun wanted_thmid thmid = List.exists (fn item => item = thmid) wanted
    in
      if null wanted then accepted
      else
        let
          val add =
            first_test_n (wanted_thmid o #thmid) max_facts special_facts
          val without = List.filter (not o wanted_thmid o #thmid) accepted
          val trimmed = take (max_facts - length add) without
          val (prefix, after) = split_at (#special_fact_index fudge) trimmed
        in
          prefix @ add @ after
        end
    end

fun mepo_rank_with_fudge (fudge : fudge)
      ({current_theory, facts, special_facts,
        frequency_table, weight_cache, ...} : context)
      (assumptions, conclusion) max_facts =
  if max_facts <= 0 orelse null facts then []
  else
    let
      val frequency_table = Susp.force frequency_table
      val chained_table =
        foldl
          (fn (term, table) =>
            add_pconsts_in_term current_theory term table)
          (empty_pconst_table ()) assumptions
      val goal_table0 =
        add_pconsts_in_term current_theory conclusion chained_table
      val score_with_membership =
        score_fact fudge fst
          (memo_pconst weight_cache (rel_pconst_weight fudge frequency_table))
          (memo_pconst weight_cache (irrel_pconst_weight fudge frequency_table
            chained_table))
      val goal_table =
        if not (Redblackmap.existsi
          (fn (name, _) => not (odd_const_name name)) goal_table0) then
          foldl
            (fn (fact, table) =>
              if #theory fact = current_theory then
                add_fact_pconsts fact table
              else table)
            (empty_pconst_table ()) facts
        else goal_table0
      val hopeful =
        List.mapPartial
          (fn fact =>
            if null (#pconsts fact) then NONE
            else SOME (fact, NONE : real option)) facts
      val decay = Math.pow
        ((1.0 - #fact_threshold1 fudge) /
         (1.0 - #fact_threshold0 fudge),
         1.0 / Real.fromInt (max_facts + 1))

      fun iter iteration remaining threshold rel_table hopeless hopeful =
        let
          val hopeless' =
            purge_hopeless fudge iteration hopeless
          val score = Susp.delay (fn () =>
            score_with_membership
              (memo_pconst weight_cache
                (pconst_hyper_mem match_ptype rel_table))
              (memo_pconst weight_cache
                (not o pconst_hyper_mem swapped_match rel_table)))
          fun scan candidates rejects [] =
                if null candidates then
                  if iteration = 0 andalso
                     threshold >= #ridiculous_threshold fudge
                  then
                    (* The relevance table is unchanged. Restore scan order
                       from the reversed rejects and keep their scores. *)
                    iter 0 max_facts
                      (threshold / #threshold_divisor fudge)
                      rel_table hopeless'
                      (foldl (fn ((fact, weight), items) =>
                        (fact, SOME weight) :: items) [] rejects)
                  else []
                else
                  let
                    val (accepted_candidates, unaccepted) =
                      take_most_relevant fudge
                        {max_facts = max_facts,
                         remaining_max = remaining,
                         candidates = candidates}
                    val accepted = map (#1 o #1) accepted_candidates
                    val accepted_count = length accepted
                    val remaining' = remaining - accepted_count
                  in
                    if remaining' = 0 then accepted
                    else
                      let
                        val (rel_table', changed) =
                          foldl add_relevance
                            (rel_table, Redblackset.empty String.compare)
                            accepted
                        val relevance_changed =
                          not (Redblackset.isEmpty changed)
                        fun dirty fact =
                          relevance_changed andalso
                          List.exists
                            (fn ((name, _), _) =>
                              Redblackset.member (changed, name))
                            (#pconsts fact)
                        fun reconsider ((fact, weight), (hope, lost)) =
                          if dirty fact then ((fact, NONE) :: hope, lost)
                          else (hope, (fact, weight) :: lost)
                        val (dirty_rejects, clean_rejects) =
                          foldl reconsider ([], []) (rejects @ hopeless')
                        val overflow = map
                          (fn ((fact, _), weight) =>
                            (fact, if dirty fact then NONE else SOME weight))
                          unaccepted
                        val next_hopeful = overflow @ dirty_rejects
                        val threshold' =
                          1.0 - (1.0 - threshold) *
                            Math.pow (decay, Real.fromInt accepted_count)
                      in
                        accepted @ iter (iteration + 1) remaining' threshold'
                          rel_table' clean_rejects next_hopeful
                      end
                  end
            | scan candidates rejects ((fact, cached) :: rest) =
                let
                  val weight =
                    case cached of
                        SOME value => value
                        | NONE =>
                            (Susp.force score) (#stature fact) (#pconsts fact)
                in
                  if weight >= threshold then
                    scan (((fact, #pconsts fact), weight) :: candidates)
                      rejects rest
                  else scan candidates ((fact, weight) :: rejects) rest
                end
        in
          scan [] [] hopeful
        end

      val accepted = iter 0 max_facts (#fact_threshold0 fudge)
        goal_table [] hopeful
      val with_specials = insert_special_facts fudge max_facts special_facts
        (conclusion :: assumptions) accepted
    in
      map #thmid (take max_facts with_specials)
    end

fun mepo_rank context goal max_facts =
  mepo_rank_with_fudge default_fudge context goal max_facts

end
