structure splitLib :> splitLib =
struct

open HolKernel boolLib

val ERR = mk_HOL_ERR "splitLib"

fun malformed msg =
  raise ERR "analyse_rule" ("Malformed split rule: " ^ msg)

fun require true _ = ()
  | require false msg = malformed msg

type split_rule =
  {thm : thm,
   head : term,
   pattern : term,
   arity : int,
   asm : bool}

(* Bucketed by the head constant's name.  [same_const] identifies only
   constants of the same name, so the name is a prefilter that never
   hides a key: the keys sharing one name are still told apart by
   [same_key] below.  Bucketing is what keeps a lookup from running
   [Type.match_type] against every rule in the set, which the splitter
   would otherwise pay for at every node of every term it scans. *)
type cmap = (term * split_rule list) list Symtab.table

fun rule_parts th =
  let
    val (qvars, body) = strip_forall (concl th)
    val _ = require (null (hyp th)) "the theorem has hypotheses"
    val (left, right) =
      dest_eq body
      handle HOL_ERR _ => malformed "the conclusion is not an equality"
    val (pred, pattern) =
      dest_comb left
      handle HOL_ERR _ =>
        malformed "the left side is not P (c a1 ... an)"
    val _ = require (is_var pred) "P is not a variable"
    val _ =
      require (List.exists (aconv pred) qvars)
        "P is not universally quantified"
    val (domain, range) =
      dom_rng (type_of pred)
      handle HOL_ERR _ => malformed "P is not a function"
    val _ = require (domain = type_of pattern) "P has the wrong domain"
    val _ = require (range = bool) "P is not bool-valued"
    val (head, args) = strip_comb pattern
    val _ = require (is_const head) "the split redex is not Const-headed"
  in
    {pred=pred, pattern=pattern, head=head, args=args,
     asm=is_neg right}
  end

fun analyse_rule th =
  let
    val {pattern,head,args,asm,...} = rule_parts th
  in
    {thm=th, head=head, pattern=pattern, arity=length args, asm=asm}
  end

fun is_asm_split th = #asm (rule_parts th)

val persistent_name = KernelSig.name_toString

fun split_thm_name th =
  let
    fun stored [] = NONE
      | stored (DB.Stored name :: _) = SOME (persistent_name name)
      | stored (_ :: rest) = stored rest
    fun local_location [] = NONE
      | local_location (DB.Local name :: _) =
          SOME (persistent_name {Thy = Theory.current_theory (), Name = name})
      | local_location (_ :: rest) = local_location rest
    val locations = DB.revlookup th
  in
    (* A stored name belongs to the theorem and reads the same in every
       theory that sees it, while [DB.Local] is only the current theory's
       name for a theorem it has not exported -- so a local alias of a
       stored theorem is the name no caller writes.  The name goes into
       the looper display [del_split] and an [ExclX] marker match, so
       taking the alias would answer a retraction written against the
       stored name with no match at all. *)
    case stored locations of
        SOME name => name
      | NONE =>
          (case local_location locations of
               SOME name => name
             | NONE =>
                 (* A rule derived on demand -- [type_split_of] builds one
                    out of TypeBase and stores nothing -- has no name in
                    the database, and the looper still needs an identity
                    to be added, displayed and retracted under.  The
                    split redex's head constant is that identity: it is
                    what the rule splits, so two derivations for one type
                    answer to the same name and no two types collide. *)
                 let
                   val {Thy, Name, ...} =
                     dest_thy_const (#head (rule_parts th))
                 in
                   persistent_name {Thy = Thy, Name = Name}
                 end)
  end

(* Persistence owns its decoder, attribute and dispatcher entirely within
   src/simp; the split algorithms only supply rule validation. *)
fun enable_split_attribute () =
  SplitData.initialize {validate=ignore o is_asm_split}
val exclude_split = SplitData.exclude
val named_split_thms = SplitData.named_rules
fun split_thms () = map #2 (named_split_thms ())

(* Turn a conclusion split rule [!P. P (c ...) = ...] into the rule for a
   negated predicate, which is the form that splits an assumption.  The
   predicate is a parameter of the derivation rather than read from the
   rule here, so that a caller who has already analysed the rule --
   split_forms below -- does not pay a second walk over it for the one
   part of the analysis this needs. *)
fun mk_asm_split_of pred split =
  let
    val (qvars, _) = strip_forall (concl split)
    val (domain, _) = dom_rng (type_of pred)
    val arg =
      variant (qvars @ free_vars (concl split)) (mk_var ("x", domain))
    val neg_pred = mk_abs (arg, mk_neg (mk_comb (pred, arg)))
    val specs =
      map (fn qvar => if aconv qvar pred then neg_pred else qvar) qvars
    val not_not = CONJUNCT1 boolTheory.NOT_CLAUSES
    val cleanup = REDEPTH_CONV (FIRST_CONV [BETA_CONV, REWR_CONV not_not])
  in
    split
      |> SPECL specs
      |> AP_TERM boolSyntax.negation
      |> CONV_RULE cleanup
      |> CONV_RULE (RAND_CONV (REWRITE_CONV [boolTheory.EQ_CLAUSES]))
      |> GENL qvars
  end

fun mk_asm_split split = mk_asm_split_of (#pred (rule_parts split)) split

(* The forms of one rule the splitter applies: an assumption rule
   stands alone, a conclusion rule is accompanied by the assumption
   rule derived from it.  A rule set built through here is walked once
   per rule rather than once per question asked about it, the analysis
   that decides which of the two cases a rule is in being the analysis
   the splitter goes on to use.  The derived rule is analysed in its
   turn rather than assembled from the parts of the rule it came from:
   mk_asm_split_of finishes with a rewriting pass over the derived
   right side, so whether that side is negated -- which is the whole of
   what the analysis decides -- is a question about the theorem in hand
   and not about the one it came from. *)
fun split_forms th =
  let
    val {pred, pattern, head, args, asm} = rule_parts th
    val rule =
      {thm=th, head=head, pattern=pattern, arity=length args, asm=asm}
  in
    if asm then [rule]
    else [rule, analyse_rule (mk_asm_split_of pred th)]
  end

(* [rules] is the derived form the splitter actually applies; it is cached
   with the rules it comes from, as deriving it costs real inference. *)
type type_splits = {split : thm, asm_split : thm, rules : thm list}
(* A TypeBase replacement keeps the same external type name.  Retain the
   exact tyinfo used for derivation so that updates and context changes miss
   this cache even when they select that same name again. *)
type cached_type_splits =
  {tyinfo : TypeBasePure.tyinfo, splits : type_splits}
val type_split_cache =
  Sref.new (Symtab.empty : cached_type_splits Symtab.table)

fun type_key tyinfo =
  let val (thy, tyop) = TypeBasePure.ty_name_of tyinfo
  in KernelSig.name_toString {Thy=thy, Name=tyop}
  end

fun type_splits_of ty =
  let
    val tyinfo =
      case TypeBase.fetch ty of
          SOME tyinfo => tyinfo
        | NONE =>
            raise ERR "type_splits_of" "type has no TypeBase information"
    val key = type_key tyinfo
    fun derive () =
      let
        val split = TypeBase.case_pred_imp_of ty
        val asm_split = TypeBasePure.case_elim_of tyinfo
        val splits =
          {split=split, asm_split=asm_split,
           rules=[split, mk_asm_split asm_split]}
        val entry = {tyinfo=tyinfo, splits=splits}
        val _ =
          Sref.update type_split_cache (Symtab.update (key, entry))
      in
        splits
      end
  in
    case Symtab.lookup (Sref.value type_split_cache) key of
        SOME {tyinfo=cached_tyinfo, splits} =>
          if Portable.pointer_eq (cached_tyinfo, tyinfo) then splits
          else derive ()
      | NONE => derive ()
  end

fun type_split_of ty = #split (type_splits_of ty)
fun type_asm_split_of ty = #asm_split (type_splits_of ty)
fun type_split_rules ty = #rules (type_splits_of ty)

fun const_key c =
  let val {Thy,Name,...} = dest_thy_const c
  in KernelSig.name_toString {Thy=Thy,Name=Name}
  end

fun applied_arities tms =
  let
    fun visit (tm,acc) =
      if is_abs tm then visit (body tm,acc)
      else
        let
          val (head,args) = strip_comb tm
          val acc = List.foldl visit acc args
          val n = length args
        in
          if is_const head then
            let val key = const_key head
            in
              case Binarymap.peek (acc,key) of
                  SOME old =>
                    if old >= n then acc else Binarymap.insert (acc,key,n)
                | NONE => Binarymap.insert (acc,key,n)
            end
          else if is_abs head then visit (head,acc)
          else acc
        end
  in
    List.foldl visit (Binarymap.mkDict String.compare) tms
  end

(* The registered case constants, indexed by name.  [order] is the
   constant's position in [TypeBase.elts], retained so that the groups
   below can be handed back in the order a walk over the TypeBase leaves
   them in. *)
type case_const = {order : int, ty : hol_type, arity : int}

(* Rebuilt whenever the TypeBase value changes, which is the pointer test
   [type_splits_of] makes against the tyinfo it derived from, applied to
   the table those tyinfos live in.  A datatype whose case constant
   cannot be analysed is left out, which is the skip the group builder
   below used to make for it on every call. *)
val case_const_index =
  Sref.new (NONE : (TypeBasePure.typeBase *
                    case_const list Symtab.table) option)

fun build_case_const_index typebase =
  let
    fun add (tyinfo,(order,index)) =
      let
        val head = TypeBasePure.case_const_of tyinfo
        val entry =
          {order=order, ty=TypeBasePure.ty_of tyinfo,
           arity=length (#1 (strip_fun (type_of head)))}
      in
        (order + 1, Symtab.cons_list (const_key head, entry) index)
      end handle HOL_ERR _ => (order + 1, index)
  in
    #2 (List.foldl add (0,Symtab.empty) (TypeBasePure.listItems typebase))
  end

fun case_const_index_of () =
  let
    val typebase = TypeBase.theTypeBase ()
    fun rebuild () =
      let val index = build_case_const_index typebase
      in
        Sref.update case_const_index (K (SOME (typebase,index)));
        index
      end
  in
    case Sref.value case_const_index of
        SOME (cached,index) =>
          if Portable.pointer_eq (cached,typebase) then index else rebuild ()
      | NONE => rebuild ()
  end

(* This deliberately does not use [TypeBase.is_case].  That predicate
   delegates to Pmatch's stricter and substantially more expensive case
   recognition.  Splitting only needs a saturated application of the
   registered case constant, which the maximum-arity table identifies in
   one walk over the goal and assumptions.  The looper is offered a goal
   on every simplification round, so the constants the goal does contain
   are looked up in the index rather than the whole TypeBase walked.  The
   derived rules themselves use [type_split_cache], so with
   [case_const_index] these are the only datatype-split caches. *)
fun goal_split_rule_groups terms =
  let
    val arities = applied_arities terms
    val index = case_const_index_of ()
    fun saturated (key,n,found) =
      let
        fun keep (entry : case_const, found) =
          if n >= #arity entry then (#order entry, #ty entry) :: found
          else found
      in
        List.foldl keep found (Symtab.lookup_list index key)
      end
    val matched = Binarymap.foldl saturated [] arities
    fun group ((_,ty),result) =
      (ty, type_split_rules ty) :: result
      handle HOL_ERR _ => result
  in
    List.foldl group [] (Listsort.sort (Lib.measure_cmp fst) matched)
  end

fun goal_split_rules terms =
  List.concat (map #2 (goal_split_rule_groups terms))

(* Two types are alpha-variants exactly when each is an instance of the
   other. *)
fun same_type_shape (ty1, ty2) =
  can (Type.match_type ty1) ty2 andalso can (Type.match_type ty2) ty1

fun same_key (h1,h2) =
  same_const h1 h2 andalso same_type_shape (type_of h1, type_of h2)

fun insert_rule (rule : split_rule) (cmap : cmap) =
  let
    val head = #head rule
    fun insert [] = [(head, [rule])]
      | insert ((key, rules) :: rest) =
          if same_key (head, key) then (key, rule :: rules) :: rest
          else (key, rules) :: insert rest
  in
    Symtab.map_default (const_key head, []) insert cmap
  end

fun index_rules rules =
  let
    fun index (rule : split_rule, (concls, asms)) =
      if #asm rule then (concls, insert_rule rule asms)
      else (insert_rule rule concls, asms)
  in
    foldl index (Symtab.empty, Symtab.empty) rules
  end

fun index_theorems thms = index_rules (map analyse_rule thms)

(* Paths are in [Conv.PATH_CONV] notation: "l" rator, "r" rand, "a" body. *)
datatype path_step = Body | Argument of int * int

type binder_info =
  {var : term,
   body : term,
   body_path : path_step list,
   depth : int}

type split_pack =
  {rule : split_rule,
   body_path : path_step list,
   redex : term,
   binders : int,
   depth : int,
   visit : int}

fun fold_candidates cmap head collect packs =
  case Symtab.lookup_list cmap (const_key head) of
      [] => packs
    | entries =>
        let
          val head_type = type_of head
          fun add ((key_head, rules), packs) =
            if same_const key_head head andalso
               can (Type.match_type (type_of key_head)) head_type
            then foldl collect packs rules
            else packs
        in
          foldl add packs entries
        end

(* Reach argument [i] of an [n]-ary application: strip the later arguments
   with rators, then take the rand. *)
fun prefix_path n i =
  StringCvt.padLeft #"l" (n - i - 1) "" ^ "r"

fun enter_path steps =
  let fun encode Body = "a"
        | encode (Argument (arity,i)) = prefix_path arity i
  in String.concat (List.rev (List.map encode steps)) end

fun matching (rule : split_rule) redex =
  can (match_term (#pattern rule)) redex

fun scan cmap tm =
  let
    val root_type = type_of tm

    (* Keep the path to the innermost binder referenced by the redex.
       Encode it only when trying to apply a rule. *)
    fun mk_pack depth (previous : split_pack list) binders node head args
                arity rule =
      let
        val n = #arity rule
      in
        if arity < n then NONE
        else
          let
            val redex =
              if arity = n then node
              else list_mk_comb (head, List.take (args, n))
            fun matched binder_depth body_path =
              let
                val visit =
                  case previous of [] => 0 | last :: _ => #visit last + 1
              in
                SOME {rule=rule, body_path=body_path, redex=redex,
                      binders=binder_depth, depth=depth, visit=visit}
              end
          in
            if not (matching rule redex) then NONE
            else
              case List.find (fn {var,...} => free_in var redex) binders of
                  NONE => if root_type = bool then matched 0 [] else NONE
                | SOME {body,body_path,depth=binder_depth,...} =>
                    if type_of body = bool then
                      matched binder_depth body_path
                    else NONE
          end
      end

    (* At equal depth, preorder visits argument paths in lexicographic
       order. Index each successful pack, including multiple rules at one
       node, so sorting preserves their collection order on ties. *)
    fun walk depth steps (binders : binder_info list) node packs =
      if is_abs node then
        let
          val (var, body) = dest_abs node
          val body_path = Body :: steps
          val binder_depth =
            case binders of [] => 1 | {depth,...} :: _ => depth + 1
          val info =
            {var=var, body=body, body_path=body_path, depth=binder_depth}
        in
          walk (depth + 1) body_path (info :: binders) body packs
        end
      else
        let
          val (head, args) = strip_comb node
          val arity = length args
          fun collect (rule, acc) =
            case mk_pack depth acc binders node head args arity rule of
                SOME pack => pack :: acc
              | NONE => acc
          val here =
            if is_const head then
              fold_candidates cmap head collect packs
            else packs
          fun descend (arg, (i, packs)) =
            let
              val arg_path = Argument (arity,i) :: steps
            in
              (i + 1, walk (depth + 1) arg_path binders arg packs)
            end
        in
          #2 (foldl descend (0, here) args)
        end
  in
    List.rev (walk 0 [] [] tm [])
  end

fun pack_compare (p1 : split_pack, p2 : split_pack) =
  case Int.compare (#binders p1, #binders p2) of
      EQUAL =>
        (case Int.compare (#depth p1, #depth p2) of
             EQUAL => Int.compare (#visit p1, #visit p2)
           | order => order)
    | order => order

fun fresh_parts th =
  let
    val sth = SPEC_ALL th
    val (left, _) = dest_eq (concl sth)
    val (pred, pattern) = dest_comb left
  in
    (sth, pred, pattern)
  end

fun instantiate (rule : split_rule) target body =
  let
    val (sth, pred, pattern) = fresh_parts (#thm rule)
    val (terminst, typeinst) = match_term pattern target
    val pred' = Term.inst typeinst pred
    val hole = genvar (type_of target)
    val context = mk_abs (hole, Term.subst [target |-> hole] body)
    val subst = (pred' |-> context) :: terminst
    val ith = INST subst (INST_TYPE typeinst sth)
    val beta =
      LAND_CONV BETA_CONV THENC
      RAND_CONV (TOP_DEPTH_CONV BETA_CONV)
    val result = CONV_RULE beta ith
    val _ =
      if aconv (lhs (concl result)) body then ()
      else raise ERR "instantiate" "instantiated rule has the wrong left side"
  in
    result
  end

fun apply_pack ({rule,body_path,redex,...} : split_pack) =
  PATH_CONV (enter_path body_path) (instantiate rule redex)

(* [tryfind] retries on any non-Interrupt exception from applying a pack. *)
fun first_success packs tm =
  Lib.with_exn (Lib.tryfind (fn pack => apply_pack pack tm)) packs
               (ERR "SPLIT_CONV" "no applicable split rule")

fun split_conv cmap tm =
  let
    val packs = if Symtab.is_empty cmap then []
                else Listsort.sort pack_compare (scan cmap tm)
    (* Isabelle tries only the first sorted pack.  Trying later packs
       when instantiation fails avoids one rejected rule shadowing an
       otherwise applicable rule, while retaining one split per call. *)
  in
    first_success packs tm
  end

fun SPLIT_CONV thms = split_conv (#1 (index_theorems thms))

fun clean_asm_eq th =
  let
    val not_not = CONJUNCT1 boolTheory.NOT_CLAUSES
    val cancel = REWR_CONV not_not
    val negated = AP_TERM boolSyntax.negation th
    val cleanup =
      LAND_CONV cancel THENC
      RAND_CONV cancel THENC
      RAND_CONV (REDEPTH_CONV cancel)
  in
    (* Cancel the two outer negations without simplifying inside the
       original assumption.  Then remove the double negations generated
       in the case hypotheses.  This is the small fragment of the usual
       NOT_CLAUSES/DE_MORGAN_THM cleanup needed here. *)
    CONV_RULE cleanup negated
  end

fun asm_eq cmap asm =
  let
    val negated = mk_neg asm
    val packs = Listsort.sort pack_compare (scan cmap negated)
  in
    clean_asm_eq (first_success packs negated)
  end

fun split_asm_tac cmap =
  let
    val heads = Symtab.fold
      (fn (_,entries) => fn acc => foldl (fn ((head,_),acc) => head::acc)
                                       acc entries) cmap []
    fun indexed_head head =
      List.exists (fn (key_head,_) => same_const key_head head)
        (Symtab.lookup_list cmap (const_key head))
    (* A short list avoids constructing a key string at each constant. *)
    val has_head =
      if length heads <= 8 then
        fn head => List.exists (fn key_head => same_const key_head head) heads
      else indexed_head
    fun contains_head tm =
      can (find_term (fn subtm => is_const subtm andalso has_head subtm)) tm

    (* [contains_head] sees only the head constant, so an assumption it
       admits may still yield no pack -- a partial application, or a rule
       whose pattern or binder-body type test the occurrence fails.  Go
       on to the next assumption in that case rather than failing the
       tactic; committing to the first assumption merely mentioning a key
       would hide a genuinely splittable one behind it.  The head test
       still keeps the [asm_eq] scan off the assumptions that cannot
       split, so only assumptions that mention a key are walked twice. *)
    fun first_split [] =
          raise ERR "SPLIT_ASM_TAC" "no assumption contains a split key"
      | first_split (asm :: rest) =
          if contains_head asm then
            case Lib.total (asm_eq cmap) asm of
                SOME eq => (asm, eq)
              | NONE => first_split rest
          else first_split rest

    fun tac (asms, goal) =
      let
        val (asm, eq) = first_split (if null heads then [] else asms)
        val cases = EQ_MP eq (ASSUME asm)
      in
        PRED_ASSUM (aconv asm) (K (STRIP_ASSUME_TAC cases)) (asms, goal)
      end
  in
    tac
  end

fun SPLIT_ASM_TAC thms = split_asm_tac (#2 (index_theorems thms))

(* Analyse the rules once and share the result between both attempts. *)
fun SPLIT_RULE_TAC rules =
  let val (concls,asms) = index_rules rules
  in
    CHANGED_TAC (CONV_TAC (split_conv concls)) ORELSE
    CHANGED_TAC (split_asm_tac asms)
  end

fun SPLIT_TAC thms = SPLIT_RULE_TAC (map analyse_rule thms)

end
