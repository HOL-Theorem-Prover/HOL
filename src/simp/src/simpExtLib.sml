(*===========================================================================*)
(* FILE          : simpExtLib.sml                                               *)
(* DESCRIPTION   : A programmable, contextual, conditional simplifier        *)
(*                                                                           *)
(* AUTHOR        : Donald Syme                                               *)
(*                 Based loosely on original HOL rewriting by                *)
(*                 Larry Paulson et al,                                      *)
(*                 and not-so-loosely on the Isabelle simplifier.            *)
(*===========================================================================*)

(* Extension-owned tracked compiler and traversal projections.
   Threaded construction uses Travrules.mk_threaded_travrules.
   Trace, tracking, bounds, marker and split identities stay shared.
   Diagnostic origin labels deliberately remain simpLib. *)
structure simpExtLib :> simpExtLib =
struct

infix oo;

open HolKernel boolLib liteLib Trace Cond_rewr Travrules TraverseExt Ho_Net


type thname = KernelSig.kernelname

val source_serial = ref 0
fun source_token () = (source_serial := !source_serial + 1; !source_serial)
type 'a source_slot = {item : 'a, token : int}
fun source_slot item = {item=item, token=source_token ()}
type source_origin =
  {event : int, slot : int, component : int, conjunct : int}
datatype rewrite_source = RewriteSource of
  {origin : source_origin, rewrite : thname option * thm,
   bound : (int ref * int) option}

fun source_rewrite (RewriteSource {rewrite,...}) = rewrite

fun rewrite_source_compare
      (RewriteSource {origin=a,...},RewriteSource {origin=b,...}) =
  case Int.compare (#event a,#event b) of
      EQUAL =>
        (case Int.compare (#slot a,#slot b) of
             EQUAL =>
               (case Int.compare (#component a,#component b) of
                    EQUAL => Int.compare (#conjunct a,#conjunct b)
                  | order => order)
           | order => order)
    | order => order

fun same_rewrite_source
      (s1 as RewriteSource {origin=o1,rewrite=(n1,t1),bound=b1},
       s2 as RewriteSource {origin=o2,rewrite=(n2,t2),bound=b2}) =
  Portable.pointer_eq (s1,s2) orelse
  (o1 = o2 andalso n1 = n2 andalso
   (Portable.pointer_eq (t1,t2) orelse
    (aconv (concl t1) (concl t2) andalso HOLset.equal (hypset t1, hypset t2)))
   andalso Option.map #2 b1 = Option.map #2 b2)

fun source_event (RewriteSource {origin,...}) = #event origin
fun source_is_bounded (RewriteSource {bound,...}) = Option.isSome bound

fun source_index include_source sources =
  List.foldl
    (fn (source,index) =>
      if include_source source then Binarymap.insert (index,source,source)
      else index)
    (Binarymap.mkDict rewrite_source_compare) sources

fun many_source_queries (_::_::_::_::_) = true
  | many_source_queries _ = false

(* Lookups select the last source-list entry at each origin, then check
   its statement. Sparse lookups index only requested origins. Report
   completeness so replay can reuse a dense index for surviving controls. *)
fun queried_source_index queries sources =
  if not (many_source_queries queries) then
    let
      fun origin (RewriteSource {origin,...}) = origin
      val wanted = map origin queries
      val index = source_index
        (fn source => Lib.mem (origin source) wanted) sources
    in (index,false) end
  else if length queries < length sources div 4 then
    let
      val wanted = Binaryset.addList
        (Binaryset.empty rewrite_source_compare,queries)
      val index = source_index
        (fn source => Binaryset.member (wanted,source)) sources
    in (index,false) end
  else (source_index (K true) sources,true)

fun grouped_by compare key items =
  let
    fun add (item,groups) =
      let
        val k = key item
        val previous = Option.getOpt (Binarymap.peek (groups,k),[])
      in Binarymap.insert (groups,k,item::previous) end
  in List.foldr add (Binarymap.mkDict compare) items end

fun group_items groups key =
  Option.getOpt (Binarymap.peek (groups,key),[])

(* Match within each origin bucket because replay can change a statement
   without changing its origin. *)
fun source_finder sources query_key queries =
  let
    (* Index sources directly when there are at least four queries per
       source. Stop the ratio check as soon as it can be decided. *)
    fun many_queries [] _ = true
      | many_queries (_::ss) (_::_::_::_::qs) = many_queries ss qs
      | many_queries _ _ = false
  in case (sources,queries) of
      (_::_::_::_,_::_::_::_::_) =>
        let
          val matching_origins =
            if many_queries sources queries then sources
            else
              let
                val wanted = Binaryset.addList
                  (Binaryset.empty rewrite_source_compare,map query_key queries)
              in
                List.filter (fn source => Binaryset.member (wanted,source))
                  sources
              end
          val groups = grouped_by rewrite_source_compare I matching_origins
        in fn wanted =>
          List.find (fn other => same_rewrite_source (wanted,other))
            (group_items groups wanted)
        end
    | _ => fn wanted =>
        List.find (fn other => same_rewrite_source (wanted,other)) sources
  end

local open markerTheory in end;

fun ERR x      = STRUCT_ERR "simpExtLib" x ;

val option_cases = simpCommon.option_cases
val op oo = simpCommon.oo

(*---------------------------------------------------------------------------*)
(* Representation of conversions manipulated by the simplifier.              *)
(*---------------------------------------------------------------------------*)


type convdata = simpCommon.convdata
(* NONE must reach each native candidate intact: a preceding failing
   user conversion can change Cond_rewr.stack_limit in the same net lookup. *)
type reducer_ctxt =
  {solver : term list -> term -> thm,
   stack : term list,
   cond_depth : int option,
   term_ord : term * term -> order}
type contextual_convdata =
  {name : string,
   key : (term list * term) option,
   trace : int,
   conv : reducer_ctxt -> conv}
type tagged_convdata =
  {thypart : string option, cd : contextual_convdata,
   legacy : (term list -> term -> thm) -> term list -> conv,
   source : (thname option * thm) option,
   prepared : Cond_rewrExt.prepared option,
   bound : (int ref * int) option}

(* slot_local means each bounded result uses its own slot's fresh input
   counter. Different slots then cannot share a counter. *)
type prepared_native =
  {rules : (tagged_convdata * rewrite_source) list, slot_local : bool}

fun lift_convdata {name,key,trace,conv} : contextual_convdata =
  {name=name, key=key, trace=trace,
   conv=fn {solver,stack,...} => conv solver stack}
(* An ordinary conversion as a fragment's conversion entry. *)
fun lift_conv thypart (c : convdata) =
  {thypart=thypart, cd=lift_convdata c, legacy= #conv c, source=NONE,
   prepared=NONE, bound=NONE}
val opttheory = simpCommon.opttheory

type stdconvdata = simpCommon.stdconvdata

(*---------------------------------------------------------------------------*)
(* Make a rewrite rule into a conversion.                                    *)
(*---------------------------------------------------------------------------*)

val mk_rewr_convdata : thname option * controlled_thm ->
                       tagged_convdata option =
  simpCommon.mk_rewr_convdata
    (fn {thypart,name=nm,key,nmopt,th,tag} =>
       let
         val bound = case tag of
                         UNBOUNDED => NONE | BOUNDED r => SOME (r, !r)
         val prepared = Cond_rewrExt.prepare (nm,th) tag
         val {legacy,configured} = Cond_rewrExt.runners prepared
       in
         {thypart = thypart, source = SOME (nmopt, th), legacy = legacy,
          prepared = SOME prepared, bound = bound,
          cd = {name = nm, key = key,
                trace = 100, (* COND_REWR_CONV provides the tracing. *)
                conv = configured}}
       end)

(* Replay rebinds an installed matcher, never recompiles its theorem.
   The declared allowance belongs to the source, not the current ref value. *)
fun rebind_convdata
      ({thypart,cd={name,key,trace,...},source,prepared,...} : tagged_convdata)
      (counter,declared) : tagged_convdata =
  let
    val prepared = Cond_rewrExt.rebind (valOf prepared) (BOUNDED counter)
    val {legacy,configured} = Cond_rewrExt.runners prepared
  in
    {thypart=thypart,source=source,prepared=SOME prepared,legacy=legacy,
     cd={name=name,key=key,trace=trace,conv=configured},
     bound=SOME (counter,declared)}
  end

(*---------------------------------------------------------------------------*)
(* Composable simpset fragments                                              *)
(*---------------------------------------------------------------------------*)

type relsimpdata = simpCommon.relsimpdata

type conv_info =
  {name : string,
   conval : (term list -> term -> thm) -> term list -> conv}
(* Every entry owns its cold companion, including rules compiled from
   supplied facts and addcontext, which source inventories do not cover.
   A single insertion attaches runner and actual quota together; filtering
   and persistent contexts retain or remove that association atomically.
   The lifted default evaluator selects ci, never this companion. *)
type configured_conv_info =
  {conval : reducer_ctxt -> conv, bound : (int ref * int) option}
type net_conv_info =
  {thypart : string option, ci : conv_info,
   configured : configured_conv_info}
type net = net_conv_info Ho_Net.net
type weakener_data =
  Travrules.preorder list * thm list * TraverseExt.reducer

(* One resolved rule exclusion.  [pattern] is what [name_match] tests the
   net's entries against; [original] is the spelling a decision procedure
   is registered under, and the two are not interchangeable.  A rule
   exclusion carries its parsed pattern for immediate application.  Strict
   Excl names are reparsed on history replay, as in simpLib; ExclX rule
   targets keep their resolved patterns across theory contexts. *)
type rule_exclusion =
  {original : string, pattern : string option * string, strict : bool}

datatype looper_kind = OrdinaryLooper | SplitLooper of bool
and looper_entry = LooperEntry of
  {kind : looper_kind, name : string, apply : simpset -> tactic}
and ssfrag = SSFRAG_CON of {
    name           : string option,
    convs          : tagged_convdata list,
    rewrs          : (thname option * thm) source_slot list,
    ac             : (thm * thm) source_slot list,
    (* Cache successful and rejected view matchers after installation.
       Replay checks the source statement and rebinds its actual control. *)
    views          : (rewrite_source * thm *
                      tagged_convdata option option) list,
    filter         : (controlled_thm -> controlled_thm list) option,
    dprocs         : TraverseExt.reducer list,
    congs          : thm list,
    threaded_congs : thm list,
    relsimps       : relsimpdata list,
    loopers        : looper_entry list,
    unsafe_solvers : TraverseExt.ssolver list,
    safe_solvers   : TraverseExt.ssolver list
}
and history_item =
    ADDFRAG of ssfrag * int *
      prepared_native option * rewrite_source list
                 | DELETE_EVENT of rule_exclusion list
                 | ADDWEAKENER of weakener_data
                 | STRATEGY_EVENT of strategy_event
                 | SET_MK_REWRS of
                     (controlled_thm -> controlled_thm list)
and strategy_event =
    ADD_LOOPER_EVENT of looper_entry
  | DEL_LOOPER_EVENT of looper_kind * string
  | SET_LOOPER_EVENT of looper_entry
  | ADD_UNSAFE_SOLVER_EVENT of TraverseExt.ssolver
  | ADD_SAFE_SOLVER_EVENT of TraverseExt.ssolver
  | SET_UNSAFE_SOLVERS_EVENT of TraverseExt.ssolver list
  | SET_SAFE_SOLVERS_EVENT of TraverseExt.ssolver list
  | REMOVE_SOLVER_EVENT of string
  | SET_SUBGOALER_EVENT of TraverseExt.subgoaler option
  | SET_COND_DEPTH_EVENT of int option
  | SET_TERM_ORD_EVENT of (term * term -> order) option
  (* Add one resolved split/case display to the persistent suppression
     set. Unlike DEL_LOOPER_EVENT this also suppresses later additions and
     rules supplied by the ambient split/TypeBase stores. Replay never
     resolves the display again. Repeated events are idempotent. *)
  | EXCLUDE_LOOPER_EVENT of string
  | SET_EXCL_LOOPERS_EVENT of string Binaryset.set
  | SET_STRATEGY_EVENT of strategy_data
and simpset = SS of {
    mk_rewrs       : controlled_thm -> controlled_thm list,
    history        : history_item list,
    initial_net    : net,
    rewrite_sources : (thname option * thm) list,
    native_sources : rewrite_source list,
    dprocs         : reducer list,
    travrules      : travrules,
    limit          : int option,
    excluded       : string Binaryset.set,
    strategy       : strategy_data
}
(* The traversal-strategy knobs are grouped so that the simpset updaters
   that leave them alone do not have to mention them one by one. *)
withtype strategy_data =
  {loopers        : looper_entry list,
   unsafe_solvers : TraverseExt.ssolver list,
   safe_solvers   : TraverseExt.ssolver list,
   subgoaler      : TraverseExt.subgoaler option,
   cond_depth     : int option,
   term_ord       : (term * term -> order) option,
   excl_loopers   : string Binaryset.set}

fun frag_name (SSFRAG_CON {name,...}) = name

val normCong = simpCommon.normCong

fun ordinary_looper (name,apply) =
  LooperEntry {kind=OrdinaryLooper,name=name,apply=apply}

(* Constructor-anchored private setters retain the original payload values.
   Replacement expressions are evaluated by callers, not by these setters. *)
fun setfrag_name name
      (SSFRAG_CON {convs,rewrs,ac,views,filter,dprocs,congs,threaded_congs,
                   relsimps,loopers,unsafe_solvers,safe_solvers,...}) =
  SSFRAG_CON
    {name=name, convs=convs, rewrs=rewrs, ac=ac, views=views, filter=filter,
     dprocs=dprocs, congs=congs, threaded_congs=threaded_congs,
     relsimps=relsimps, loopers=loopers,
     unsafe_solvers=unsafe_solvers, safe_solvers=safe_solvers}

fun setfrag_rewrs rewrs
      (SSFRAG_CON {name,convs,ac,views,filter,dprocs,congs,threaded_congs,
                   relsimps,loopers,unsafe_solvers,safe_solvers,...}) =
  SSFRAG_CON
    {name=name, convs=convs, rewrs=rewrs, ac=ac, views=views, filter=filter,
     dprocs=dprocs, congs=congs, threaded_congs=threaded_congs,
     relsimps=relsimps, loopers=loopers,
     unsafe_solvers=unsafe_solvers, safe_solvers=safe_solvers}

fun setfrag_views views
      (SSFRAG_CON {name,convs,rewrs,ac,filter,dprocs,congs,threaded_congs,
                   relsimps,loopers,unsafe_solvers,safe_solvers,...}) =
  SSFRAG_CON
    {name=name, convs=convs, rewrs=rewrs, ac=ac, views=views, filter=filter,
     dprocs=dprocs, congs=congs, threaded_congs=threaded_congs,
     relsimps=relsimps, loopers=loopers,
     unsafe_solvers=unsafe_solvers, safe_solvers=safe_solvers}

val empty_frag_data =
  {name=NONE, convs=[], rewrs=[], ac=[], views=[], filter=NONE,
   dprocs=[], congs=[], threaded_congs=[],
   relsimps=[], loopers=[], unsafe_solvers=[], safe_solvers=[]}
val empty_ssfrag = SSFRAG_CON empty_frag_data

fun SSFRAG {name,convs,rewrs,ac,filter,dprocs,congs} =
  let
    val convs = map (lift_conv NONE) convs
    val rewrs = map source_slot rewrs
    val ac = map source_slot ac
    val congs = map normCong congs
  in
    SSFRAG_CON
      {name=name, convs=convs, rewrs=rewrs, ac=ac, views=[], filter=filter,
       dprocs=dprocs, congs=congs, threaded_congs=[], relsimps=[],
       loopers=[], unsafe_solvers=[], safe_solvers=[]}
  end

(* Ordinary fragments, as extension fragments.  The lift of a named
   fragment is remembered (by identity, latest per name), so that repeated
   lifts and lookups of the same fragment share its source slots. *)
local
  fun lift0 ordinary =
    let
      val {name,convs,rewrs,ac,filter,dprocs,congs,relsimps} =
          simpLib.dest_ssfrag ordinary
    in
      SSFRAG_CON
        {name=name, convs=map (fn {thypart,cd} => lift_conv thypart cd) convs,
         rewrs=map source_slot rewrs,
         ac=map source_slot ac, views=[], filter=filter,
         dprocs=map TraverseExt.lift dprocs, congs=congs, threaded_congs=[],
         relsimps=relsimps, loopers=[], unsafe_solvers=[], safe_solvers=[]}
    end
  val lifted : (simpLib.ssfrag * ssfrag) Symtab.table ref = ref Symtab.empty
in
fun lift_ssfrag ordinary =
    case simpLib.frag_name ordinary of
        NONE => lift0 ordinary
      | SOME n =>
        case Symtab.lookup (!lifted) n of
            SOME (orig, f) => if Portable.pointer_eq (orig, ordinary) then f
                              else remember n ordinary
          | NONE => remember n ordinary
and remember n ordinary =
    let val f = lift0 ordinary
    in lifted := Symtab.update (n, (ordinary, f)) (!lifted); f end
end

fun ssf_upd_rewrs f (frag as SSFRAG_CON s) =
  setfrag_rewrs (map source_slot (f (map #item (#rewrs s)))) frag

(* ----------------------------------------------------------------------
    maintain a global database of (named) ssfrags
   ---------------------------------------------------------------------- *)

val ssfragDB_slot : ssfrag Symtab.table Context.Data.slot =
    simpCommon.new_fragDB "simpExtLib.ssfragDB"
fun register_frag ssf = simpCommon.register_frag ssfragDB_slot frag_name ssf
(* Names registered with simpLib resolve too, unless shadowed here *)
fun lookup_named_frag n =
    case simpCommon.lookup_named_frag ssfragDB_slot n of
        NONE => Option.map lift_ssfrag (simpLib.lookup_named_frag n)
      | sf => sf
fun all_named_frags() =
    Lib.op_union equal (simpCommon.all_named_frags ssfragDB_slot)
                 (simpLib.all_named_frags())

(*---------------------------------------------------------------------------*)
(* Operation on ssfrag values                                                *)
(*---------------------------------------------------------------------------*)

fun name_ss s frag = setfrag_name (SOME s) frag

fun rewrites rewrs =
  setfrag_rewrs (map (source_slot o pair NONE) rewrs) empty_ssfrag

fun rewrites_with_names rewrs =
  setfrag_rewrs (map (source_slot o apfst SOME) rewrs) empty_ssfrag

fun rewrite_views views =
  setfrag_views (map (fn (source,th) => (source,th,NONE)) views) empty_ssfrag

fun threaded_cong_ss congs =
  SSFRAG_CON
    {name=NONE, convs=[], rewrs=[], ac=[], views=[], filter=NONE,
     dprocs=[], congs=[], threaded_congs=map normCong congs, relsimps=[],
     loopers=[], unsafe_solvers=[], safe_solvers=[]}

fun dproc_ss dproc =
  SSFRAG_CON
    {name=NONE, convs=[], rewrs=[], ac=[], views=[], filter=NONE,
     dprocs=[dproc], congs=[], threaded_congs=[], relsimps=[],
     loopers=[], unsafe_solvers=[], safe_solvers=[]}

fun ac_ss aclist =
  SSFRAG_CON
    {name=NONE, convs=[], rewrs=[], ac=map source_slot aclist, views=[],
     filter=NONE, dprocs=[], congs=[], threaded_congs=[], relsimps=[],
     loopers=[], unsafe_solvers=[], safe_solvers=[]}

fun conv_ss conv =
  SSFRAG_CON
    {name=NONE, convs=[lift_conv NONE conv],
     rewrs=[], ac=[], views=[], filter=NONE, dprocs=[], congs=[],
     threaded_congs=[], relsimps=[], loopers=[],
     unsafe_solvers=[], safe_solvers=[]}

fun relsimp_ss rsdata =
  SSFRAG_CON
    {name=NONE, convs=[], rewrs=[], ac=[], views=[], filter=NONE,
     dprocs=[], congs=[], threaded_congs=[], relsimps=[rsdata],
     loopers=[], unsafe_solvers=[], safe_solvers=[]}

fun looper_ss looper =
  SSFRAG_CON
    {name=NONE, convs=[], rewrs=[], ac=[], views=[], filter=NONE,
     dprocs=[], congs=[], threaded_congs=[], relsimps=[],
     loopers=[ordinary_looper looper], unsafe_solvers=[], safe_solvers=[]}

fun solver_ss solver =
  SSFRAG_CON
    {name=NONE, convs=[], rewrs=[], ac=[], views=[], filter=NONE,
     dprocs=[], congs=[], threaded_congs=[], relsimps=[],
     loopers=[], unsafe_solvers=[solver], safe_solvers=[]}

fun safe_solver_ss solver =
  SSFRAG_CON
    {name=NONE, convs=[], rewrs=[], ac=[], views=[], filter=NONE,
     dprocs=[], congs=[], threaded_congs=[], relsimps=[],
     loopers=[], unsafe_solvers=[], safe_solvers=[solver]}

fun D (SSFRAG_CON s) = s;
fun frag_rewrites ssf = map (#2 o #item) (#rewrs (D ssf))

fun add_named_rwt nth ssfrag = ssf_upd_rewrs (cons (apfst SOME nth)) ssfrag

val merge_names = simpCommon.merge_names_by frag_name
val merge_filters = simpCommon.merge_filters_by (#filter o D)

(*---------------------------------------------------------------------------*)
(* Possibly need to suppress duplicates in the merge?                        *)
(*---------------------------------------------------------------------------*)

fun merge_ss (s:ssfrag list) =
  SSFRAG_CON
    { name     = merge_names s,
      convs    = flatten (map (#convs o D) s),
      rewrs    = map (source_slot o #item) (flatten (map (#rewrs o D) s)),
      filter   = merge_filters s,
      ac       = map (source_slot o #item) (flatten (map (#ac o D) s)),
      views    = flatten (map (#views o D) s),
      dprocs   = flatten (map (#dprocs o D) s),
      congs    = flatten (map (#congs o D) s),
      threaded_congs = flatten (map (#threaded_congs o D) s),
      relsimps = flatten (map (#relsimps o D) s),
      loopers  = flatten (map (#loopers o D) s),
      unsafe_solvers = flatten (map (#unsafe_solvers o D) s),
      safe_solvers = flatten (map (#safe_solvers o D) s)
    }

fun named_rewrites name = (name_ss name) o rewrites;
fun named_rewrites_with_names name = (name_ss name) o rewrites_with_names;
fun named_merge_ss name = (name_ss name) o merge_ss;

val std_conv_ss =
    simpCommon.std_conv_ss {conv_ss = conv_ss, merge_ss = merge_ss}

fun partition_ssfrags names ssdata =
    simpCommon.partition_ssfrags frag_name names ssdata

(*---------------------------------------------------------------------------*)
(* Simpsets and basic operations on them. Simpsets contain enough            *)
(* information to spark off term traversal quickly and efficiently. In       *)
(* theory the net need not be stored (and the code would look neater if it   *)
(* wasn't), but in practice it has to be.                                    *)
(* --------------------------------------------------------------------------*)

(* Names in [excluded] are forbidden from being added by [++].
   [exclude_ssfrags] sets them and [force_add] clears them per name. *)

val empty_excluded : string Binaryset.set = Binaryset.empty String.compare

val empty_strategy : strategy_data =
  {loopers=[], unsafe_solvers=[], safe_solvers=[], subgoaler=NONE,
   cond_depth=NONE, term_ord=NONE, excl_loopers=empty_excluded}

val empty_ss =
  SS{mk_rewrs=fn x => [x], history=[], limit=NONE, initial_net=empty,
     rewrite_sources=[], native_sources=[],
     dprocs=[], travrules=EQ_tr, excluded=empty_excluded,
     strategy=empty_strategy}

 fun ssfrags_of (SS x) =
     List.mapPartial
       (fn ADDFRAG (sf,_,_,_) => SOME sf | _ => NONE) (#history x)

fun rewrite_source_handles (SS s) = #native_sources s

val entry_name_match = simpCommon.entry_name_match

fun name_match matches ({thypart,ci,...}:net_conv_info) =
  matches thypart (#name ci)

(* A user key names a theorem in the kernel [Thy$Name] spelling, in the
   [Thy.Name] spelling, or with no theory part at all.  A dot is not
   decisive on its own: a theorem name can carry a numeric suffix, and can
   itself contain a dot.  This extended reading is reserved for [rule:]
   exclusions; bare exclusions and [-*] use simpLib's parser below. *)
fun parse_simpset_name {unknown_thy} p =
  let
    fun known_thy (thy,name) =
      if mem thy (ancestry "-") then (SOME thy,name)
      else unknown_thy (thy,name)
    fun dotted () =
      case String.fields (equal #".") p of
          [_] => (NONE,p)
        | [s1,s2] =>
            if CharVector.all Char.isDigit s2 then (NONE,p)
            else known_thy (s1,s2)
        | [s1,s2,s3] => (SOME s1,s2 ^ "." ^ s3)
        | _ => raise ERR ("-*", "User key has too many dots")
  in
    case String.fields (equal #"$") p of
        [thy,name] =>
          if thy = "" orelse name = "" then dotted ()
          else known_thy (thy,name)
      | _ => dotted ()
  end

(* simpLib's [munge_pat], used by [-*] and every [Excl] name. *)
val munge_simpset_name = simpCommon.munge_simpset_name

(* [rule:] exclusions have to be able to name what is installed.  A net
   entry records whatever theory its rewrite was named with, and nothing
   requires that
   theory to be an ancestor of the theory being built: a fragment carrying
   names from an unloaded theory sits in the net all the same, and its
   qualified spelling is what a user writes to exclude it.  So for
   exclusion a theory part whose only fault is not being an ancestor is
   read positionally and matched against the entries. The dots-only
   fallback still rejects keys with too many dots; a nonempty Thy$Name
   spelling is split at the dollar instead, leaving dots literal. *)
fun excl_simpset_name p =
  parse_simpset_name {unknown_thy = fn (thy,name) => (SOME thy,name)} p

(* [Ho_Net.fold'] visits every entry; an exclusion only needs to know
   whether one of them matches, so a local exception stops the traversal at
   the first hit. *)
local exception FoundEntry
in
fun net_exists P net =
  (Ho_Net.fold' (fn entry => fn () => if P entry then raise FoundEntry
                                      else ())
                net ();
   false)
  handle FoundEntry => true
end

fun simpset_has_dproc name (SS s) =
  List.exists
    (fn reducer => #name (TraverseExt.reducer_data reducer) = SOME name)
    (#dprocs s)

(* The historical rewrite exclusion operation also removes decision
   procedures by name.  Treat the two stores as one target here so a rewrite
   and a dproc sharing a name are excluded together, as [ss -* names] has
   always specified.  [pending] holds the rule exclusions that
   [apply_exclusions] has resolved but not yet applied to the net; masking
   them here is what makes deferring the filter invisible.  Only exclusion
   resolution asks this, and supplies the already parsed pattern. *)
fun simpset_has_rule_target {pending : rule_exclusion list}
                            ({original=name,pattern,...} : rule_exclusion)
                            (ss as SS s) =
  let
    val target = name_match (simpCommon.prepare_entry_name_match [pattern])
    val gone =
      name_match (simpCommon.prepare_entry_name_match (map #pattern pending))
  in
    net_exists (fn nd => target nd andalso not (gone nd)) (#initial_net s)
    orelse
    (not (List.exists (fn e : rule_exclusion => #original e = name)
                      pending) andalso
     simpset_has_dproc name ss)
  end

fun filter_dprocs_by_names nms =
    simpCommon.drop_named (#name o TraverseExt.reducer_data) nms

(* Apply already parsed exclusions. Replay refreshes strict Excl patterns
   first, but retains resolved ExclX patterns. The history records that
   distinction even when no current entry matches a strict exclusion. *)
fun delete_exclusions (excls : rule_exclusion list) (ss as SS s) =
    if null excls then ss
    else
      let
        val matcher = ref NONE
        fun matches thy name =
          case !matcher of
              SOME match => match thy name
            | NONE =>
                let val match =
                  simpCommon.prepare_entry_name_match (map #pattern excls)
                in matcher := SOME match; match thy name end
        fun retained (nm, _) =
          let
            val (thy, name) =
              case nm of NONE => (NONE, "<anonymous>")
                       | SOME {Thy,Name} => (SOME Thy, Name)
          in
            not (matches thy ("rewrite:" ^ name))
          end
      in
        let
          val initial_net =
            Ho_Net.vfilter (not o name_match matches) (#initial_net s)
          val rewrite_sources = List.filter retained (#rewrite_sources s)
          val native_sources =
            List.filter (retained o source_rewrite) (#native_sources s)
          val history = DELETE_EVENT excls :: #history s
          val dprocs =
            filter_dprocs_by_names (map #original excls) (#dprocs s)
        in
          SS {mk_rewrs = #mk_rewrs s, history = history,
              initial_net = initial_net, rewrite_sources = rewrite_sources,
              native_sources = native_sources, dprocs = dprocs,
              travrules = #travrules s, limit = #limit s,
              excluded = #excluded s, strategy = #strategy s}
        end
      end

fun exclusion_of_name p : rule_exclusion =
  {original = p, pattern = munge_simpset_name p, strict = true}

fun replay_exclusion (excl : rule_exclusion) =
  if #strict excl then exclusion_of_name (#original excl) else excl

fun ss -* nms = delete_exclusions (map exclusion_of_name nms) ss
fun remove_simps nms ss = ss -* nms


  (* ---------------------------------------------------------------------
   * USER_CONVS shares trace strings between direct and configured runners.
   *
   * net_add_convs (internal function) adds conversions to the
   * initial context net.
   * ---------------------------------------------------------------------*)

 fun USER_CONVS {name,key,trace,conv} legacy =
  let val traced = simpCommon.user_conv {name=name,trace=trace}
  in
    {legacy = fn solver => fn stack => traced (legacy solver stack),
     configured = fn ctxt => traced (conv ctxt)}
  end;

 val any = simpCommon.any

 fun net_add_conv
       {thypart,source,prepared,bound,legacy,
        cd = data as {name,key,trace,conv}:contextual_convdata} =
   let val runners = USER_CONVS data legacy
   in
     enter (option_cases #1 [] key,
            option_cases #2 any key,
            {thypart = thypart,
             configured = {conval= #configured runners,bound=bound},
             ci = {name = name, conval = #legacy runners}})
   end

(* itlist is like foldr, so that theorems get added to the context starting
   from the end of the list *)
 fun net_add_convs net convs = itlist net_add_conv convs net;


 val mk_ac = simpCommon.mk_ac
 fun ssfrag_names_of ss = simpCommon.frag_names frag_name (ssfrags_of ss)

 fun fupdlimit f (SS s) =
   let val limit = f (#limit s)
   in
     SS {mk_rewrs = #mk_rewrs s, history = #history s,
         initial_net = #initial_net s, rewrite_sources = #rewrite_sources s,
         native_sources = #native_sources s, dprocs = #dprocs s,
         travrules = #travrules s, limit = limit,
         excluded = #excluded s, strategy = #strategy s}
   end

 fun limit n = fupdlimit (fn _ => SOME n)

val unlimit = fupdlimit (fn _ => NONE)

fun getlimit (SS ss) = #limit ss

fun map_strategy f (SS s) =
  let val strategy = f (#strategy s)
  in
    SS {mk_rewrs = #mk_rewrs s, history = #history s,
        initial_net = #initial_net s, rewrite_sources = #rewrite_sources s,
        native_sources = #native_sources s, dprocs = #dprocs s,
        travrules = #travrules s, limit = #limit s,
        excluded = #excluded s, strategy = strategy}
  end

(* Monomorphic field updaters retain every other strategy value unchanged. *)
fun upd_loopers f (s:strategy_data) : strategy_data =
  let val loopers = f (#loopers s)
  in
    {loopers = loopers, unsafe_solvers = #unsafe_solvers s,
     safe_solvers = #safe_solvers s, subgoaler = #subgoaler s,
     cond_depth = #cond_depth s, term_ord = #term_ord s,
     excl_loopers = #excl_loopers s}
  end
fun upd_unsafe_solvers f (s:strategy_data) : strategy_data =
  let val unsafe_solvers = f (#unsafe_solvers s)
  in
    {loopers = #loopers s, unsafe_solvers = unsafe_solvers,
     safe_solvers = #safe_solvers s, subgoaler = #subgoaler s,
     cond_depth = #cond_depth s, term_ord = #term_ord s,
     excl_loopers = #excl_loopers s}
  end
fun upd_safe_solvers f (s:strategy_data) : strategy_data =
  let val safe_solvers = f (#safe_solvers s)
  in
    {loopers = #loopers s, unsafe_solvers = #unsafe_solvers s,
     safe_solvers = safe_solvers, subgoaler = #subgoaler s,
     cond_depth = #cond_depth s, term_ord = #term_ord s,
     excl_loopers = #excl_loopers s}
  end
fun upd_subgoaler f (s:strategy_data) : strategy_data =
  let val subgoaler = f (#subgoaler s)
  in
    {loopers = #loopers s, unsafe_solvers = #unsafe_solvers s,
     safe_solvers = #safe_solvers s, subgoaler = subgoaler,
     cond_depth = #cond_depth s, term_ord = #term_ord s,
     excl_loopers = #excl_loopers s}
  end
fun upd_cond_depth f (s:strategy_data) : strategy_data =
  let val cond_depth = f (#cond_depth s)
  in
    {loopers = #loopers s, unsafe_solvers = #unsafe_solvers s,
     safe_solvers = #safe_solvers s, subgoaler = #subgoaler s,
     cond_depth = cond_depth, term_ord = #term_ord s,
     excl_loopers = #excl_loopers s}
  end
fun upd_term_ord f (s:strategy_data) : strategy_data =
  let val term_ord = f (#term_ord s)
  in
    {loopers = #loopers s, unsafe_solvers = #unsafe_solvers s,
     safe_solvers = #safe_solvers s, subgoaler = #subgoaler s,
     cond_depth = #cond_depth s, term_ord = term_ord,
     excl_loopers = #excl_loopers s}
  end
fun upd_excl_loopers f (s:strategy_data) : strategy_data =
  let val excl_loopers = f (#excl_loopers s)
  in
    {loopers = #loopers s, unsafe_solvers = #unsafe_solvers s,
     safe_solvers = #safe_solvers s, subgoaler = #subgoaler s,
     cond_depth = #cond_depth s, term_ord = #term_ord s,
     excl_loopers = excl_loopers}
  end

fun fupdhistory f (SS s) =
  let val history = f (#history s)
  in
    SS {mk_rewrs = #mk_rewrs s, history = history,
        initial_net = #initial_net s, rewrite_sources = #rewrite_sources s,
        native_sources = #native_sources s, dprocs = #dprocs s,
        travrules = #travrules s, limit = #limit s,
        excluded = #excluded s, strategy = #strategy s}
  end

fun record_strategy event =
  fupdhistory (fn history => STRATEGY_EVENT event::history)

fun same_looper_id
      (LooperEntry {kind=OrdinaryLooper,name,...})
      (OrdinaryLooper,name') = name = name'
  | same_looper_id (LooperEntry {kind=SplitLooper asm,name,...})
      (SplitLooper asm',name') = asm = asm' andalso name = name'
  | same_looper_id _ _ = false

fun looper_data (LooperEntry data) = data

fun looper_display (LooperEntry {kind=OrdinaryLooper,name,...}) = name
  | looper_display (LooperEntry {kind=SplitLooper asm,name,...}) =
      (if asm then "split_asm " else "split ") ^ name

fun update_looper (looper,[]) = [looper]
  | update_looper (looper,entry::rest) =
      if same_looper_id entry
           (#kind (looper_data looper),#name (looper_data looper))
      then looper::rest
      else entry::update_looper(looper,rest)

local
  (* Only ordinary loopers can be added by a fragment. An installed split
     looper keeps its slot even if its name is also in the batch. *)
  fun indexed_update batch installed =
    let
      (* First occurrence determines the position, last the entry. *)
      fun remember (entry,(first,pending)) =
        let
          val name = #name (looper_data entry)
          val first = if Symtab.defined pending name then first
                      else name::first
        in (first,Symtab.update (name,entry) pending) end
      val (first,pending) = List.foldl remember ([],Symtab.empty) batch
      fun append pending (name,entries) =
        case Symtab.lookup pending name of
            SOME entry => entry::entries
          | NONE => entries
      fun merge pending installed =
        if Symtab.is_empty pending then installed
        else case installed of
            [] => List.foldl (append pending) [] first
          | (entry as LooperEntry {kind=OrdinaryLooper,name,...})::rest =>
              (case Symtab.lookup pending name of
                  NONE => entry::merge pending rest
                | SOME replacement =>
                    replacement::merge (Symtab.delete_safe name pending) rest)
          | entry::rest => entry::merge pending rest
    in merge pending installed end

  fun long_batch 0 _ = true
    | long_batch _ [] = false
    | long_batch n (_::rest) = long_batch (n - 1) rest

  fun group_updates batch installed =
    let
      (* Replacing the same ID leaves its first position intact. Grouping a
         short list once avoids walking the installed list for each repeat. *)
      fun collect [] grouped = List.foldl update_looper installed grouped
        | collect (looper::rest) grouped =
            case update_looper (looper,grouped) of
                grouped as _::_::_::_::_::_ =>
                  indexed_update (grouped @ rest) installed
              | grouped => collect rest grouped
    in collect batch [] end
in
  fun update_loopers [] installed = installed
    | update_loopers [looper] installed = update_looper (looper,installed)
    | update_loopers batch installed =
        if long_batch 65 batch then group_updates batch installed
        else List.foldl update_looper installed batch
end

fun add_solver (solver : TraverseExt.ssolver,
                solvers : TraverseExt.ssolver list) =
  if List.exists (fn {name,...} => name = #name solver) solvers then solvers
  else solvers @ [solver]

fun add_solvers [] solvers = solvers
  | add_solvers [solver] solvers = add_solver (solver,solvers)
  | add_solvers [first,second] solvers =
      add_solver (second,add_solver (first,solvers))
  | add_solvers batch solvers =
      let
        fun add_indexed added batch =
          let
            fun collect (solver as {name,...} : TraverseExt.ssolver,
                         acc as (names,added)) =
              if Symtab.defined names name then acc
              else (Symtab.insert_set name names,solver::added)
            val initial = List.foldl
              (fn (solver,names) => Symtab.insert_set (#name solver) names)
              Symtab.empty added
            val (names,added) = List.foldl collect (initial,added) batch
            (* Index only incoming names. A duplicate-only batch can finish
               as soon as it has found those names in the existing list. *)
            fun remove_installed [] pending = pending
              | remove_installed (({name,...} : TraverseExt.ssolver)::rest)
                                 pending =
                  if Symtab.is_empty pending then pending
                  else remove_installed rest (Symtab.remove_set name pending)
            val pending = remove_installed solvers names
          in
            if Symtab.is_empty pending then solvers
            else if Portable.pointer_eq (names,pending) then
              solvers @ List.rev added
            else solvers @ List.rev
              (List.filter (Symtab.defined pending o #name) added)
          end
        fun finish added =
          if null solvers then List.rev added
          else
            let
              fun collect (solver as {name,...} : TraverseExt.ssolver, new) =
                if List.exists (fn s => #name s = name) solvers then new
                else solver::new
            in
              case List.foldl collect [] added of
                  [] => solvers
                | new => solvers @ new
            end
        (* A small set of distinct names is cheap to scan, even when
           repeated throughout a long batch. *)
        fun gather [] _ added = finish added
          | gather (batch as (solver as {name,...} : TraverseExt.ssolver)::rest)
                   room added =
              if List.exists (fn s => #name s = name) added then
                gather rest room added
              else if room = 0 then add_indexed added batch
              else gather rest (room - 1) (solver::added)
        fun short _ [] = true
          | short 0 _ = false
          | short n (_::rest) = short (n - 1) rest
        fun skip_installed
              (batch as (solver : TraverseExt.ssolver)::rest)
              ((installed : TraverseExt.ssolver)::more) =
              if #name solver = #name installed then skip_installed rest more
              else batch
          | skip_installed batch _ = batch
      in
        case skip_installed batch solvers of
            [] => solvers
          | [solver] => add_solver (solver,solvers)
          | rest => gather rest (if short 64 rest then 64 else 8) []
      end

fun dedup_solvers solvers = add_solvers solvers []

fun strategy_of (SS s) = #strategy s
fun has_looper_id id ss =
  List.exists (fn entry => same_looper_id entry id)
    (#loopers (strategy_of ss))
fun has_solver name ss =
  let fun named {name=name',...} = name = name'
  in
    List.exists named (#unsafe_solvers (strategy_of ss)) orelse
    List.exists named (#safe_solvers (strategy_of ss))
  end

(* The single implementation of every strategy change.  The exported
   setters and the [build_from_history] replay both go through it, so the
   simpset a user builds and the one rebuilt from its history cannot
   drift apart. *)
fun apply_strategy_event event =
  map_strategy
    (case event of
         ADD_LOOPER_EVENT looper =>
           upd_loopers (fn ls => update_looper(looper,ls))
       | DEL_LOOPER_EVENT id =>
           upd_loopers (List.filter (fn entry => not (same_looper_id entry id)))
       | SET_LOOPER_EVENT looper => upd_loopers (K [looper])
       | ADD_UNSAFE_SOLVER_EVENT solver =>
           upd_unsafe_solvers (fn ss => add_solver(solver,ss))
       | ADD_SAFE_SOLVER_EVENT solver =>
           upd_safe_solvers (fn ss => add_solver(solver,ss))
       | SET_UNSAFE_SOLVERS_EVENT solvers => upd_unsafe_solvers (K solvers)
       | SET_SAFE_SOLVERS_EVENT solvers => upd_safe_solvers (K solvers)
       | REMOVE_SOLVER_EVENT name =>
           let fun keep {name=name',...} = name <> name'
           in upd_unsafe_solvers (List.filter keep) o
              upd_safe_solvers (List.filter keep)
           end
       | SET_SUBGOALER_EVENT subgoaler => upd_subgoaler (K subgoaler)
       | SET_COND_DEPTH_EVENT cond_depth => upd_cond_depth (K cond_depth)
       | SET_TERM_ORD_EVENT term_ord => upd_term_ord (K term_ord)
       | EXCLUDE_LOOPER_EVENT display =>
           upd_excl_loopers (fn excl => Binaryset.add (excl,display))
       | SET_EXCL_LOOPERS_EVENT excl => upd_excl_loopers (K excl)
       | SET_STRATEGY_EVENT strategy => K strategy)

fun strategy_op event ss =
  apply_strategy_event event ss |> record_strategy event

fun add_looper looper =
  strategy_op (ADD_LOOPER_EVENT (ordinary_looper looper))
fun set_looper looper =
  strategy_op (SET_LOOPER_EVENT (ordinary_looper looper))
fun add_unsafe_solver solver = strategy_op (ADD_UNSAFE_SOLVER_EVENT solver)
fun add_safe_solver solver = strategy_op (ADD_SAFE_SOLVER_EVENT solver)
fun set_unsafe_solvers solvers =
  strategy_op (SET_UNSAFE_SOLVERS_EVENT (dedup_solvers solvers))
fun set_safe_solvers solvers =
  strategy_op (SET_SAFE_SOLVERS_EVENT (dedup_solvers solvers))
fun set_subgoaler subgoaler =
  strategy_op (SET_SUBGOALER_EVENT (SOME subgoaler))
fun set_cond_depth depth = strategy_op (SET_COND_DEPTH_EVENT (SOME depth))
fun set_term_ord term_ord = strategy_op (SET_TERM_ORD_EVENT (SOME term_ord))

(* Deleting an absent looper is a no-op; only the exported [del_looper]
   warns about it. *)
fun del_looper_id_quiet id ss =
  if has_looper_id id ss then strategy_op (DEL_LOOPER_EVENT id) ss else ss

fun del_looper_quiet name = del_looper_id_quiet (OrdinaryLooper,name)

fun del_looper name ss =
  if has_looper_id (OrdinaryLooper,name) ss then del_looper_quiet name ss
  else (HOL_WARNING "simpExtLib" "del_looper" ("No looper called " ^ name); ss)

fun remove_solver name ss =
  if has_solver name ss then strategy_op (REMOVE_SOLVER_EVENT name) ss else ss

fun split_looper_id name th =
  (SplitLooper (splitLib.is_asm_split th),name)

fun split_looper_display name th =
  (if splitLib.is_asm_split th then "split_asm " else "split ") ^ name

fun add_split th =
  let val name = splitLib.split_thm_name th
      val (kind,_) = split_looper_id name th
  in
    strategy_op
      (ADD_LOOPER_EVENT
        (LooperEntry
          {kind=kind, name=name,
           apply=K (splitLib.SPLIT_TAC [th])}))
  end

fun strip_namespace prefix = Lib.total (Lib.unprefix prefix)

fun del_split name ss =
  let
    val ids =
      case strip_namespace "split " name of
          SOME base => [(SplitLooper false,base)]
        | NONE =>
          case strip_namespace "split_asm " name of
              SOME base => [(SplitLooper true,base)]
            | NONE => [(SplitLooper false,name),(SplitLooper true,name)]
  in
    List.foldl (fn (id,result) => del_looper_id_quiet id result) ss ids
  end

(* A tactic solver runs a tactic, which needs a context, but is called from
   conversions, which have none.  The simplifier tactics below record the
   context they are given, on their thread, for the length of the call.
   Outside one, a tactic solver proves against the ambient context. *)
local
  val current : Context.t option ThreadLocal.t = ThreadLocal.new ()
  fun get () = Option.join (ThreadLocal.get current)
in
  fun tactic_context () = get ()
  fun with_tactic_context (tac : tactic) : tactic = fn g => fn ctxt =>
    let
      val old = get ()
      fun reset () = ThreadLocal.set (current, old)
      val () = ThreadLocal.set (current, SOME ctxt)
      val result = tac g ctxt handle e => (reset (); raise e)
    in
      reset (); result
    end
end

(* The context a split or case name is resolved in: the tactic's, else, in
   a conversion, which has none, the ambient one. *)
fun split_context () =
  case tactic_context () of
      SOME ctxt => ctxt
    | NONE => Context.snapshot ()

(* The [split] rules and datatypes are those of the context the tactic runs
   in. *)
fun splitter_looper ss (asms, goal) ctxt =
  let
    val excluded = #excl_loopers (strategy_of ss)
    val unfiltered = Binaryset.isEmpty excluded
    fun enabled name = not (Binaryset.member (excluded, name))
    fun enabled_named (name, th) = enabled (split_looper_display name th)
    val named = splitLib.named_split_thms_of ctxt
    val persistent =
      map #2 (if unfiltered then named else List.filter enabled_named named)
    fun type_enabled ty =
      let
        val {Thy,Tyop,...} = dest_thy_type ty
        val full = KernelSig.name_toString {Thy=Thy, Name=Tyop}
      in
        enabled ("split.case " ^ full) andalso
        enabled ("split.case " ^ Tyop)
      end
    val groups = splitLib.goal_split_rule_groups_of ctxt (goal :: asms)
    val datatype_rules =
      List.concat (map #2
        (if unfiltered then groups else List.filter (type_enabled o #1) groups))
  in
    splitLib.SPLIT_TAC (persistent @ datatype_rules) (asms, goal) ctxt
  end

val cases_simp =
  let
    val b = mk_var ("b", bool)
    val t = mk_var ("t", bool)
    val expand = SPECL [b,t,t] boolTheory.COND_EXPAND_IMP
    val identity = ISPECL [b,t] boolTheory.COND_ID
  in
    TRANS (SYM expand) identity
  end

val split_ss =
  named_merge_ss "split"
    [looper_ss ("splitter", splitter_looper), rewrites [cases_simp]]

datatype exclusion_target =
    ExcludeRule of rule_exclusion
  | ExcludeLooper of looper_kind * string
  | ExcludeSolver of string
  | ExcludeSplits of string list
  | ExcludeCase of string

(* Membership in the split and case display spaces, rather than the lists
   themselves: ExclX asks these questions, and enumerating the case
   displays means walking all of [TypeBase.elts()].  The display prefix
   settles almost every name before either store is touched. *)
fun split_display_exists ss display =
  (String.isPrefix "split " display orelse
   String.isPrefix "split_asm " display) andalso
  let
    fun is_local (entry as LooperEntry {kind=SplitLooper _,...}) =
          looper_display entry = display
      | is_local _ = false
    fun is_persistent (name,th) = split_looper_display name th = display
  in
    List.exists is_local (#loopers (strategy_of ss)) orelse
    List.exists is_persistent (splitLib.named_split_thms_of (split_context ()))
  end

val case_prefix = "split.case "

fun case_display_exists display =
  String.isPrefix case_prefix display andalso
  let
    val wanted = String.extract (display,String.size case_prefix,NONE)
    (* Compare the common qualified spelling without building a string for
       each entry. Type names can contain dollar signs themselves. *)
    val qualified =
      case String.fields (equal #"$") wanted of
          [_] => K false
        | [theory,name] =>
            (fn (thy,tyop) => thy = theory andalso tyop = name)
        | _ => (fn (thy,tyop) =>
            wanted = KernelSig.name_toString {Thy=thy,Name=tyop})
    fun names tyinfo =
      let val (thy,tyop) = TypeBasePure.ty_name_of tyinfo
      in
        wanted = tyop orelse qualified (thy,tyop)
      end
  in
    List.exists names (TypeBase.elts_of (split_context ()))
  end

(* Only ExclX resolves targets. Bare names first use simpLib's rule
   reading; only when that matches nothing do they fall through to the
   strategy targets. Multiple strategy kinds are ambiguous. Unlike literal
   Excl, an explicit extended exclusion with no target is an error. *)
fun no_target original =
  raise ERR ("process_tags", "ExclX did not match " ^ original)

fun ambiguous_target original =
  raise ERR
    ("process_tags",
     "ExclX name " ^ original ^
     " is ambiguous; qualify it with rule:, looper:, solver:, " ^
     "split:, or case:")

fun optional_target _ [] = NONE
  | optional_target _ [target] = SOME target
  | optional_target original _ = ambiguous_target original

(* Parse once for extended resolution and immediate application. History
   replay retains the resolved rule pattern, including for bare names. *)
fun resolve_exclusion {pending} ss original =
  let
    fun rule_target name pattern =
      let val excl = {original = name, pattern = pattern, strict = false}
      in
        if simpset_has_rule_target {pending=pending} excl ss
        then SOME excl
        else NONE
      end
  in
  case strip_namespace "rule:" original of
      SOME name =>
        (case Option.mapPartial (rule_target name)
                                (Lib.total excl_simpset_name name) of
             SOME excl => SOME (ExcludeRule excl)
           | NONE => no_target original)
    | NONE =>
      case strip_namespace "looper:" original of
          SOME name =>
            if has_looper_id (OrdinaryLooper,name) ss
            then SOME (ExcludeLooper (OrdinaryLooper,name))
            else no_target original
        | NONE =>
          case strip_namespace "solver:" original of
              SOME name =>
                if has_solver name ss then SOME (ExcludeSolver name)
                else no_target original
            | NONE =>
              case strip_namespace "split:" original of
                  SOME name =>
                    let
                      val candidates = ["split " ^ name,"split_asm " ^ name]
                      val matches =
                        List.filter (split_display_exists ss) candidates
                    in
                      if null matches then no_target original
                      else SOME (ExcludeSplits matches)
                    end
                | NONE =>
                  case strip_namespace "case:" original of
                      SOME name =>
                        let val display = case_prefix ^ name
                        in
                          if case_display_exists display
                          then SOME (ExcludeCase display)
                          else no_target original
                        end
                    | NONE =>
                      let
                        val excl =
                          {original=original,
                           pattern=munge_simpset_name original, strict=false}
                      in
                        if simpset_has_rule_target {pending=pending} excl ss
                        then SOME (ExcludeRule excl)
                        else
                          let
                            val targets =
                              (if has_looper_id (OrdinaryLooper,original) ss
                               then [ExcludeLooper (OrdinaryLooper,original)]
                               else []) @
                              (if has_solver original ss
                               then [ExcludeSolver original] else []) @
                              (if split_display_exists ss original
                               then [ExcludeSplits [original]] else []) @
                              (if case_display_exists original
                               then [ExcludeCase original] else [])
                          in
                            case optional_target original targets of
                                NONE => no_target original
                              | target => target
                          end
                      end
  end

fun exclude_split_display (display,ss) =
  let
    val ids =
      List.mapPartial
        (fn entry as LooperEntry {kind=SplitLooper _,name,...} =>
              if looper_display entry = display
              then SOME (#kind (looper_data entry),name) else NONE
          | _ => NONE)
        (#loopers (strategy_of ss))
    val without_local =
      List.foldl (fn (id,result) => del_looper_id_quiet id result) ss ids
  in
    strategy_op (EXCLUDE_LOOPER_EVENT display) without_local
  end

fun apply_exclusion (target,ss) =
  case target of
      ExcludeRule excl => delete_exclusions [excl] ss
    | ExcludeLooper id => del_looper_id_quiet id ss
    | ExcludeSolver solver => remove_solver solver ss
    | ExcludeSplits displays => List.foldl exclude_split_display ss displays
    | ExcludeCase display => strategy_op (EXCLUDE_LOOPER_EVENT display) ss

datatype exclusion_request = datatype simpCommon.exclusion_request

(* Batch adjacent rule deletions, retaining their order and strictness.
   Pending patterns mask rules during extended resolution. Flush before a
   strategy event so history keeps the same order as direct application.
   Literal names never inspect the extended namespaces or strategy stores,
   and even unmatched ones record the same deletion as [-*]. *)
fun apply_exclusions ss requests =
  let
    fun flush (ss,pending) = delete_exclusions (List.rev pending) ss
    fun step (LiteralExclusion name,(ss,pending)) =
          (ss,exclusion_of_name name :: pending)
      | step (ExtendedExclusion name,state as (ss,pending)) =
          case resolve_exclusion {pending=pending} ss name of
              NONE => state
            | SOME (ExcludeRule excl) => (ss,excl::pending)
            | SOME target => (apply_exclusion (target,flush state),[])
  in
    flush (List.foldl step (ss,[]) requests)
  end

fun mk_tactic_solver (name,tac) =
  let
    fun solve ({context_thms,...} : TraverseExt.simp_prover_ctxt) c =
      let
        val g = (map concl context_thms,c)
        val th = case tactic_context () of
                     SOME ctxt => Tactical.TAC_PROOF_in ctxt (g,tac)
                   | NONE => TAC_PROOF (g,tac)
      in
        Lib.itlist PROVE_HYP context_thms th
      end
  in
    {name=name,solve=solve}
  end

 val wk_mk_travrules = simpCommon.wk_mk_travrules

 fun add_weakener (wd as (rels,congs,dp)) (SS s) =
   let
     val history = ADDWEAKENER wd :: #history s
     val travrules =
       merge_travrules [#travrules s,wk_mk_travrules(rels,congs)]
     val dprocs = #dprocs s @ [dp]
   in
     SS {mk_rewrs = #mk_rewrs s, history = history,
         initial_net = #initial_net s, rewrite_sources = #rewrite_sources s,
         native_sources = #native_sources s, dprocs = dprocs,
         travrules = travrules, limit = #limit s,
         excluded = #excluded s, strategy = #strategy s}
   end

(* ----------------------------------------------------------------------
    add_relsimp : {trans,refl,weakenings,subsets} -> simpset -> simpset
    (see simpCommon.relsimp_weakener)
   ---------------------------------------------------------------------- *)

 val rsd_reducer = TraverseExt.lift o simpCommon.rsd_reducer
 val rsd_travrules = simpCommon.rsd_travrules

 fun add_relsimp rsd ss =
   let val (rels, weakenings, reducer) = simpCommon.relsimp_weakener rsd
   in add_weakener (rels, weakenings, TraverseExt.lift reducer) ss end

 val mk_named_rewrs = simpCommon.mk_named_rewrs


 fun is_excluded (SS{excluded,...}) f =
     simpCommon.is_excluded excluded (frag_name f)

 fun compile_native_named event slot component named =
   let
     fun compile _ [] acc = List.rev acc
       | compile conjunct (rw::rest) acc =
           let val next = conjunct + 1
           in
             case mk_rewr_convdata rw of
                 SOME (cd as {source=SOME rewrite,bound,...}) =>
                   let
                     val origin = {event=event, slot=slot, component=component,
                                   conjunct=conjunct}
                     val source = RewriteSource
                       {origin=origin, rewrite=rewrite, bound=bound}
                   in compile next rest ((cd,source)::acc) end
               | _ => compile next rest acc
           end
   in
     compile 1 named []
   end

 fun compile_native event mk_rewrs slot component item =
   compile_native_named event slot component (mk_named_rewrs mk_rewrs item)

 fun compile_native_rewrite event mk_rewrs {item=(nm,th),token} =
   let
     val item as (plain,input_control) = dest_tagged_rewrite th
     val rules = compile_native event mk_rewrs token 0 (nm,item)
     fun owns (_,RewriteSource {bound=NONE,...}) = true
       | owns (_,RewriteSource {bound=SOME (counter,_),...}) =
           case input_control of
               BOUNDED r => Portable.pointer_eq (r,counter)
             | UNBOUNDED => false
   in (plain,rules,List.all owns rules) end

 (* Preserve simpLib's ++ schedule: decode every ordinary tag, derive all
    AC rules, run every rewrite maker, and only then make conversions.
    Carry origins through these stages without allocating new tokens. *)
 fun compile_frag_native event mk_rewrs ac rewrs =
   let
     val crewrs = map
       (fn {item=(nm,th),token} => (token,0,(nm,dest_tagged_rewrite th)))
       rewrs
     fun derive_ac {item,token} acc =
       let
         fun number _ [] = acc
           | number component (rw::rest) =
               (token,component,rw)::number (component + 1) rest
       in number 1 (mk_ac item []) end
     val acrewrs = Lib.itlist derive_ac ac crewrs
     val named = map
       (fn (slot,component,rw) =>
         (slot,component,mk_named_rewrs mk_rewrs rw)) acrewrs
   in
     flatten (map
       (fn (slot,component,rws) =>
         compile_native_named event slot component rws) named)
   end

 datatype rewrite_bundle = RewriteBundle of
   {parts : (ssfrag * int * prepared_native) list,
    rules : (thm * rewrite_source list) list,
    context : thm list}

 fun bundle_events parts =
   List.foldl
     (fn ((_,event,_),events) => Binaryset.add (events,event))
     (Binaryset.empty Int.compare) parts

 (* Compilation alone cannot prime an ambient reducer with supplied facts. *)
 fun prepare_rewrite_bundle (SS data) theorems =
   let
     val fragment = name_ss "PREPARED_REWRITES" (rewrites theorems)
     val event = source_token ()
     fun rule (slot as {item=(_,th),...}) =
       let val (plain,rules,slot_local) =
             compile_native_rewrite event (#mk_rewrs data) slot
       in (th,plain,rules,slot_local) end
     val compiled = map rule (#rewrs (D fragment))
     val native = {rules=List.concat (map #3 compiled),
                   slot_local=List.all #4 compiled}
   in
     RewriteBundle
       {parts=[(fragment,event,native)],
        rules=map (fn (th,_,rules,_) => (th,map #2 rules)) compiled,
        context=map #2 compiled}
   end

 fun rewrite_bundle_rules (RewriteBundle {rules,...}) = rules

 (* Combine already compiled bindings; preserve each event and control. *)
 fun combine_rewrite_bundles bundles =
   let
     val data = map (fn RewriteBundle data => data) bundles
     val parts = List.concat (map #parts data)
     val _ = Binaryset.numItems (bundle_events parts) = length parts orelse
       raise ERR ("combine_rewrite_bundles","duplicate binding")
   in RewriteBundle
        {parts=parts,rules=List.concat (map #rules data),
         context=List.concat (map #context data)} end

 datatype view_sources = BundleSources | AvailableSources

 fun add_frag_native view_sources native_override suspended
       rebind event (ss, f) =
   let
   val SS sset = ss
   val SSFRAG_CON ssf = f
   val mk_rewrs' = #mk_rewrs sset
   val history = #history sset
   val travrules = #travrules sset
   val initial_net = #initial_net sset
   val dprocs' = #dprocs sset
   val {convs,rewrs,filter,ac,views,dprocs,congs,threaded_congs,
        relsimps,...} = ssf
   val mk_rewrs = case filter of
                    SOME f => f oo mk_rewrs'
                  | _ => mk_rewrs'
   val all_native = case native_override of
       SOME {rules,...} => rules
     | NONE => compile_frag_native event mk_rewrs' ac rewrs
   val (retained,removed_native) =
     if null suspended then (all_native,[])
     else
       let val removed = source_finder suspended #2 all_native
       in List.partition (fn (_,source) => not (isSome (removed source)))
            all_native
       end
   val native = case rebind of NONE => retained | SOME bind => bind retained
   val native_sources =
     List.foldr (fn ((_,source),sources) => source::sources)
       (#native_sources sset) native
   fun bind_view NONE compiled = compiled
     | bind_view (bound as SOME (pair as (counter,declared))) compiled =
         case compiled of
             SOME (data as
                {bound=SOME (r,n),thypart,cd,legacy,source,prepared}) =>
               if not (Portable.pointer_eq (r,counter)) then
                 SOME (rebind_convdata data pair)
               else if n = declared then compiled
               else SOME {thypart=thypart,cd=cd,legacy=legacy,source=source,
                          prepared=prepared,bound=bound}
           | SOME data => SOME (rebind_convdata data pair)
           | NONE => NONE
   fun compile_view (source,view,cached)
         (RewriteSource {rewrite=(nm,_),bound,...}) =
     let
       val compiled = case cached of
           NONE =>
             let val control =
                   case bound of NONE => UNBOUNDED | SOME (r,_) => BOUNDED r
             in mk_rewr_convdata (nm,(view,control)) end
         | SOME data => data
       (* A fresh matcher may see a partially spent counter. Retain the
          source's declaration so a later reset replenishes it fully. *)
       val compiled = bind_view bound compiled
     in (compiled,(source,view,SOME compiled)) end
   fun retain_view find (entry as (source,_,_)) =
     case find source of
         NONE => (NONE,entry)
       | SOME current => compile_view entry current
   val compiled_views =
     if null views then []
     else case view_sources of
         BundleSources =>
           let
             val find = source_finder (map #2 native) #1 views
             fun own_view (entry as (source,_,_)) =
               case find source of
                   NONE => NONE
                 | SOME current => SOME (compile_view entry current)
           in List.mapPartial own_view views
           end
       | AvailableSources =>
           if isSome native_override andalso many_source_queries views then
             let
               (* Replay also considers ambient sources when a view's
                  own source is missing or has changed. *)
               val own = source_finder (map #2 native) #1 views
               val ambient = Susp.delay
                 (fn () => source_finder (#native_sources sset) #1 views)
               fun find source =
                 case own source of
                     NONE => Susp.force ambient source
                   | found => found
             in map (retain_view find) views end
           else map (retain_view (source_finder native_sources #1 views)) views
   val view_convs = List.mapPartial #1 compiled_views
   (* Install from the end so fragment conversions retain priority over
      native rewrites, and native rewrites retain priority over views. *)
   val net =
     net_add_convs initial_net view_convs
     |> itlist (net_add_conv o #1) native
     |> (fn net => net_add_convs net convs)
   (* give the existing dprocs the rewrs as additional context -
      assume the provided dprocs in the frag have already been
      primed *)
   val relreducers = map rsd_reducer relsimps
   fun reduced_context slots =
     let
       val affected = List.mapPartial
         (fn (_,source as RewriteSource {origin,...}) =>
           if #component origin = 0 andalso
              Binaryset.member (slots,#slot origin) then SOME source
           else NONE) native
       val retained_slots = grouped_by Int.compare
         (fn RewriteSource {origin,...} => #slot origin) affected
       fun payload (RewriteSource {rewrite=(_,th),bound,...}) =
         case bound of NONE => th
           | SOME (_,declared) => BoundedRewrites.Ntimes th declared
       fun context {item=(_,theorem),token} =
         if Binaryset.member (slots,token) then
           map payload (group_items retained_slots token)
         else [theorem]
     in
       List.concat (map context rewrs)
     end
   (* A slot that lost an ordinary rewrite reconstructs its context facts,
      including validation of their declared bounds. AC components never
      contribute their source theorem to this context. *)
   val new_dprocs =
     if null dprocs' andalso null removed_native then dprocs @ relreducers
     else
       let
         val reduced_slots = List.foldl
           (fn ((_,RewriteSource {origin,...}),slots) =>
             if #component origin = 0 then Binaryset.add (slots,#slot origin)
             else slots)
           (Binaryset.empty Int.compare) removed_native
         val context_thms =
           if Binaryset.isEmpty reduced_slots then map (#2 o #item) rewrs
           else reduced_context reduced_slots
         val context_thms =
           if isSome native_override then
             map (#1 o dest_tagged_rewrite) context_thms
           else context_thms
       in map (TraverseExt.addctxt context_thms) dprocs' @ dprocs @ relreducers
       end

   val strategy = #strategy sset
   val strategy =
     if null (#loopers ssf) andalso null (#unsafe_solvers ssf) andalso
        null (#safe_solvers ssf) then strategy
     else
       strategy
       |> upd_loopers (update_loopers (#loopers ssf))
       |> upd_unsafe_solvers (add_solvers (#unsafe_solvers ssf))
       |> upd_safe_solvers (add_solvers (#safe_solvers ssf))
 in
   let
     val history = ADDFRAG
       (setfrag_views (map #2 compiled_views) f,event,
        native_override,suspended)
       :: history
     fun retain_source ({source,...} : tagged_convdata,sources) =
       case source of NONE => sources | SOME source => source::sources
     val view_rewrites = List.foldr retain_source (#rewrite_sources sset)
       view_convs
     val rewrite_sources =
       List.foldr retain_source
         (List.foldr (fn ((data,_),sources) => retain_source (data,sources))
            view_rewrites native) convs
     val travrules =
       simpCommon.frag_travrules
         {travrules = travrules, congs = congs,
          threaded_congs = threaded_congs, relsimps = relsimps}
   in
     SS {mk_rewrs = mk_rewrs, history = history, initial_net = net,
         rewrite_sources = rewrite_sources, native_sources = native_sources,
         dprocs = new_dprocs, travrules = travrules, limit = #limit sset,
         excluded = #excluded sset, strategy = strategy}
   end
 end

 fun op++ (ss,fragment) =
   (* A prohibited addition preserves the simpset and source serial. *)
   if is_excluded ss fragment then ss
   else add_frag_native AvailableSources NONE [] NONE
          (source_token ()) (ss,fragment)

 fun setexcluded e (SS s) =
   SS {mk_rewrs = #mk_rewrs s, history = #history s,
       initial_net = #initial_net s, rewrite_sources = #rewrite_sources s,
       native_sources = #native_sources s, dprocs = #dprocs s,
       travrules = #travrules s, limit = #limit s,
       excluded = e, strategy = #strategy s}

 fun install_rewrite_bundle (RewriteBundle {parts,...}) views
       (ss as SS data) =
   let
     fun installed_single _ [] = false
       | installed_single event (ADDFRAG (_,previous,_,_)::rest) =
           previous = event orelse installed_single event rest
       | installed_single event (_::rest) = installed_single event rest
     val duplicate =
       case parts of
           [] => false
         | [(_,event,_)] => installed_single event (#history data)
         | _ =>
             let
               val events = bundle_events parts
             in
               List.exists
                 (fn ADDFRAG (_,previous,_,_) =>
                       Binaryset.member (events,previous)
                   | _ => false)
                 (#history data)
             end
     val _ = not duplicate orelse
       raise ERR ("install_rewrite_bundle","binding already installed")
     val views_by_event = grouped_by Int.compare (source_event o #1) views
     fun unexclude name (ss as SS data) =
       if Binaryset.isEmpty (#excluded data) then ss
       else
         setexcluded (Binaryset.delete (#excluded data,name)) ss
         handle NotFound => ss
     fun install ((fragment,event,native),ss) =
       let
         val name = valOf (frag_name fragment)
         val ss = unexclude name ss
         val fragment =
           case group_items views_by_event event of
               [] => fragment
             | views => setfrag_views (map (fn (s,th) => (s,th,NONE)) views)
                          fragment
       in add_frag_native BundleSources (SOME native) [] NONE event
            (ss,fragment) end
   in List.foldl install ss parts end

val mk_simpset = foldl (fn (f,ss) => ss ++ f) empty_ss

fun set_mk_rewrs mk_rewrs (SS s) =
  SS {mk_rewrs = mk_rewrs, history = #history s,
      initial_net = #initial_net s, rewrite_sources = #rewrite_sources s,
      native_sources = #native_sources s, dprocs = #dprocs s,
      travrules = #travrules s, limit = #limit s,
      excluded = #excluded s, strategy = #strategy s}

(* Ordinary replay resets declared quotas, including a quota shared by
   several compiled conjuncts. Prepared shapes need no rewrite-maker call. *)
fun freshen_prepared_native {rules,slot_local} =
  let
    val fresh =
      if slot_local then
        (* Each slot has its own counter and its rules remain contiguous. *)
        let
          val last = ref NONE
          fun next slot declared =
            let val current = ref declared
            in last := SOME (slot,current); current end
        in fn slot => fn _ => fn declared =>
          case !last of
              SOME (previous,current) =>
                if slot = previous then current
                else next slot declared
            | NONE => next slot declared
        end
      else
        (* A custom maker may have shared a counter across distinct slots. *)
        let val counters = ref []
        in fn _ => fn counter => fn declared =>
          case List.find (fn (old,_) => Portable.pointer_eq (old,counter))
                         (!counters) of
              SOME (_,current) => current
            | NONE =>
                let val current = ref declared
                in counters := (counter,current) :: !counters; current end
        end
    fun reset (pair as (data,RewriteSource {origin,rewrite,bound})) =
      case bound of
          NONE => pair
        | SOME (counter,declared) =>
            let
              val current = fresh (#slot origin) counter declared
              val data = rebind_convdata data (current,declared)
            in (data,RewriteSource
                 {origin=origin,rewrite=rewrite,bound=SOME (current,declared)})
            end
  in {rules=map reset rules,slot_local=slot_local} end

fun build_from_history_with rebind h0 =
    let
      fun foldthis (hi, ss) =
          case hi of
              ADDFRAG (sf,event,cached,suspended) =>
                let
                  val native = case rebind of
                      NONE => Option.map freshen_prepared_native cached
                    | SOME _ => cached
                in
                  if is_excluded ss sf then ss
                  else add_frag_native AvailableSources native suspended
                         rebind event (ss,sf)
                end
            | DELETE_EVENT excls =>
                delete_exclusions (map replay_exclusion excls) ss
            | ADDWEAKENER wd => add_weakener wd ss
            | STRATEGY_EVENT event => strategy_op event ss
            | SET_MK_REWRS mk_rewrs =>
                set_mk_rewrs mk_rewrs ss
                |> fupdhistory (fn h => SET_MK_REWRS mk_rewrs::h)
    in
      List.foldl foldthis empty_ss (List.rev h0)
    end

fun build_from_history h0 = build_from_history_with NONE h0

fun rebind_source_controls get_current =
  let
    val current = Susp.delay get_current
    fun rebind index
          (pair as (data,source as RewriteSource {origin,rewrite,...})) =
      if not (source_is_bounded source) then pair
      else
        case Binarymap.peek (index,source) of
            SOME (previous as RewriteSource
                    {bound=bound as SOME (counter,declared),...}) =>
              if not (same_rewrite_source (previous,source)) orelse
                 (case #bound data of
                      SOME (r,_) => Portable.pointer_eq (r,counter)
                    | NONE => false)
              then pair
              else (rebind_convdata data (counter,declared),
                    RewriteSource {origin=origin,rewrite=rewrite,bound=bound})
          | _ => pair
  in
    fn native =>
      if List.exists (source_is_bounded o #2) native then
        map (rebind (Susp.force current)) native
      else native
  end

fun suspend_rewrite_sources [] ss = ss
  | suspend_rewrite_sources requested (ss as SS data) =
    let
      val sources = #native_sources data
      val (current,complete) = queried_source_index requested sources
      fun active source =
        case Binarymap.peek (current,source) of
            SOME installed =>
              if same_rewrite_source (source,installed) then SOME installed
              else NONE
          | NONE => NONE
    in
      case List.mapPartial active requested of
          [] => ss
        | removed =>
            let
              val removed = HOLset.listItems
                (HOLset.addList (HOLset.empty rewrite_source_compare,removed))
              val removed_by_event = grouped_by Int.compare source_event removed
              fun suspend (item as ADDFRAG (fragment,event,prepared,previous)) =
                    (case group_items removed_by_event event of
                         [] => item
                       | removed =>
                           ADDFRAG (fragment,event,prepared,removed @ previous))
                | suspend item = item
              (* Use the full index if a bounded survivor needs it. All
                 entries must participate in last-at-origin selection. *)
              val rebind = rebind_source_controls
                (fn () => if complete then current
                          else source_index (K true) sources)
            in
              build_from_history_with (SOME rebind)
                (map suspend (#history data))
                |> fupdlimit (fn _ => #limit data)
                |> setexcluded (#excluded data)
            end
    end

val history_ops : (simpset,history_item,ssfrag) simpCommon.history_ops =
    {history = fn SS{history,...} => history,
     excluded = fn SS{excluded,...} => excluded,
     added = fn ADDFRAG (f,_,_,_) => SOME f | _ => NONE,
     frag_name = frag_name, setexcluded = setexcluded, add = op ++}

fun replay_with_limit (SS{limit,...}) h =
    build_from_history h |> fupdlimit (fn _ => limit)

fun remove_ssfrags_with_controls preserve names
      (ss as SS{limit,native_sources,...}) =
    let
      fun rebuild history =
        let
          val rebind = if not preserve then NONE else
            SOME (rebind_source_controls
              (fn () => source_index source_is_bounded native_sources))
        in
          build_from_history_with rebind history |> fupdlimit (fn _ => limit)
        end
    in
      simpCommon.remove_ssfrags history_ops rebuild names ss
    end

fun remove_ssfrags names ss = remove_ssfrags_with_controls false names ss

(* An invocation replay shares each compatible surviving native counter. *)
fun remove_ssfrags_preserving_controls names ss =
  remove_ssfrags_with_controls true names ss

(* Drops from every fragment the rewrites a predicate rejects, leaving
   the rest of the simpset's history in place.  Rebuilding a simpset
   from `ssfrags_of` instead keeps the ADDFRAGs alone, so a rewrite the
   simpset had removed by name comes back, and so do its `excluded`
   set, its limit and its rewrite maker: the result is not the simpset
   it was filtered from.  Going through `build_from_history` is what
   `remove_ssfrags` does for the same reason.

   Returns the simpset itself where the predicate rejects nothing, so
   the common case costs no replay, and never raises Conv.UNCHANGED. *)
fun filter_rewrites_with_controls preserve keep
      (ss as SS{history,limit,excluded,native_sources,...}) =
    let
      (* Delay copying the prefix while the predicate keeps every rewrite.
         Copy it by length so the predicate runs once per rewrite. *)
      fun retained_rewrites rewrs =
        let
          fun retain ({item,...} : (thname option * thm) source_slot) =
            keep item
          fun first_removed _ [] = NONE
            | first_removed n (entry::rest) =
                if retain entry then first_removed (n + 1) rest
                else SOME (List.take (rewrs,n) @ List.filter retain rest)
        in first_removed 0 rewrs end
      fun filtered (ADDFRAG (f,event,cached,suspended)) =
            let
              val {rewrs,ac,...} = D f
              fun filter_cached retained {rules,slot_local} =
                let
                  val slots = Binaryset.addList (Binaryset.empty Int.compare,
                    map #token retained @ map #token ac)
                  val rules = List.filter (fn (_,RewriteSource {origin,...}) =>
                    Binaryset.member (slots,#slot origin)) rules
                in {rules=rules,slot_local=slot_local} end
            in
              case retained_rewrites rewrs of
                  NONE => NONE
                | SOME retained =>
                    SOME (ADDFRAG (setfrag_rewrs retained f,event,
                      Option.map (filter_cached retained) cached,suspended))
            end
        | filtered _ = NONE
      fun updated item = Option.getOpt (filtered item,item)
      (* Only build a new history when a rewrite was dropped. *)
      fun first_changed _ [] = NONE
        | first_changed n (item::rest) =
            case filtered item of
                NONE => first_changed (n + 1) rest
              | SOME changed =>
                  SOME (List.take (history,n) @ changed :: map updated rest)
    in
      case first_changed 0 history of
          NONE => ss
        | SOME history' =>
        let
          val rebind = if not preserve then NONE else
            SOME (rebind_source_controls
              (fn () => source_index source_is_bounded native_sources))
        in build_from_history_with rebind history'
             |> fupdlimit (fn _ => limit) |> setexcluded excluded end
    end

val filter_rewrites = filter_rewrites_with_controls false
val filter_rewrites_preserving_controls = filter_rewrites_with_controls true

fun exclude_ssfrags names ss =
    simpCommon.exclude_ssfrags history_ops (replay_with_limit ss) names ss

fun force_add ss f = simpCommon.force_add history_ops ss f

(* [keep] says which fragment additions of the history are replayed. *)
fun lift_history keep ordinary =
    let
      val {history, limit = lim, excluded} = simpLib.dest_simpset ordinary
      fun replay (simpLib.ADDFRAG f, ss) =
            if keep f then ss ++ lift_ssfrag f else ss
        | replay (simpLib.DELETE_EVENT names, ss) = ss -* names
        | replay (simpLib.ADDWEAKENER (rels,thms,r), ss) =
            add_weakener (rels, thms, TraverseExt.lift r) ss
    in
      List.foldl replay empty_ss history
        |> fupdlimit (fn _ => lim)
        |> setexcluded (Binaryset.addList (empty_excluded, excluded))
    end

fun lift_simpset ordinary = lift_history (K true) ordinary

fun lift_simpset_without [] = lift_simpset
  | lift_simpset_without names =
    let
      val member = simpCommon.names_member names
    in
      lift_history
        (fn f => case simpLib.frag_name f of
                     name as SOME _ => not (member name)
                   | NONE => true)
    end

fun clear_rules (SS s) =
  let
    val strategy = upd_loopers (K []) (#strategy s)
    (* Rules and fragment loopers are dropped; every other strategy field is
       retained as one value, so adding a field cannot make replay lose it. *)
    val history =
      [STRATEGY_EVENT (SET_STRATEGY_EVENT strategy),
       SET_MK_REWRS (#mk_rewrs s)]
  in
    SS {mk_rewrs = #mk_rewrs s, history = history, initial_net = empty,
        rewrite_sources = [], native_sources = [], dprocs = [],
        travrules = EQ_tr, limit = #limit s, excluded = #excluded s,
        strategy = strategy}
  end

(* Conversion identities survive replay; deletions affect their keys too. *)
fun rewrite_context_changes (old_ss as SS old,current_ss as SS current) =
  if Portable.pointer_eq (old_ss,current_ss) then
    {keys=[], rebuild=false, context_sensitive=not (null (#dprocs old))}
  else
  let
    val same_history = Portable.pointer_eq (#history old,#history current)
    fun snapshot history =
      let
        fun scan [] _ convs structural makers =
              (convs,structural,makers)
          | scan (item::rest) excluded convs structural makers =
              case item of
                  DELETE_EVENT excls =>
                    scan rest (map #pattern excls @ excluded)
                         convs structural makers
                | ADDFRAG (SSFRAG_CON f,event,_,_) =>
                    let
                      fun add ([],_,found) = found
                        | add ({thypart,cd={name,key,...},...}::cs,i,found) =
                            if entry_name_match (thypart,name) excluded then
                              add (cs,i+1,found)
                            else add (cs,i+1,((event,i),key)::found)
                      val special =
                        not (null (#ac f) andalso null (#dprocs f) andalso
                             null (#congs f) andalso
                             null (#threaded_congs f) andalso
                             null (#relsimps f) andalso
                             null (#views f)) orelse Option.isSome (#filter f)
                    in
                      scan rest excluded (add (#convs f,1,convs))
                        (if special then item::structural else structural)
                        makers
                    end
                | ADDWEAKENER _ =>
                    scan rest excluded convs (item::structural) makers
                | SET_MK_REWRS f =>
                    scan rest excluded convs structural (f::makers)
                | _ => scan rest excluded convs structural makers
      in scan history [] [] [] [] end
    (* Appending a fragment leaves the conversion entries in the shared
       suffix alone. Only the new event contributes to the delta. *)
    fun added_fragment ((item as ADDFRAG _)::rest) previous =
          if Portable.pointer_eq (rest,previous) then SOME item else NONE
      | added_fragment _ _ = NONE
    fun viewless (ADDFRAG (SSFRAG_CON {views,...},_,_,_)) = null views
      | viewless _ = false
    fun changed_histories (old as _::_, current as _::_) =
          (case added_fragment current old of
               SOME item => ([],[item],viewless item)
             | NONE =>
                 case added_fragment old current of
                     SOME item => ([item],[],viewless item)
                   | NONE => (old,current,false))
      | changed_histories (old,current) = (old,current,false)
    val (old_history,new_history,viewless_delta) =
      if same_history then ([],[],false)
      else changed_histories (#history old,#history current)
    val (old_convs,old_structure,old_makers) = snapshot old_history
    val (new_convs,new_structure,new_makers) = snapshot new_history
    (* A view event can survive while its compiled dependency disappears.
       Inspect installed compatibility, not just the event/cache identity.
       Cached rejected shapes and inactive stale handles contribute no view;
       neither inspection nor quota consumption prepares a matcher. *)
    fun active_views history queries sources =
      let
        fun active installed
              (source as RewriteSource {origin,...},_,
               SOME (SOME (data:tagged_convdata))) =
              if Binaryset.member (installed,#event origin) andalso
                 (case Binarymap.peek (sources,source) of
                      SOME current => same_rewrite_source (source,current)
                    | NONE => false)
              then Option.map #2 (#source data) else NONE
          | active _ _ = NONE
        val wanted = List.foldl
          (fn (source,events) => Binaryset.add (events,source_event source))
          (Binaryset.empty Int.compare) queries
        (* A source must already exist when a view is installed. Visit
           the relevant events in installation order, including a view's
           own bundle event. A later reinstall must leave a view stale. *)
        fun select (ADDFRAG (SSFRAG_CON {views,...},event,_,_),selected) =
              let val tracked = Binaryset.member (wanted,event)
              in
                if tracked orelse not (null views)
                then (views,event,tracked)::selected else selected
              end
          | select (_,selected) = selected
        fun add_views _ _ [] _ found = found
          | add_views installed event ((entry as (source,_,_))::rest)
                i found =
              case active installed entry of
                  NONE => add_views installed event rest (i+1) found
                | SOME th => add_views installed event rest (i+1)
                    (((event,i),source,th)::found)
        fun scan [] _ found = List.rev found
          | scan ((views,event,tracked)::rest) installed found =
              let
                val installed =
                  if tracked then Binaryset.add (installed,event)
                  else installed
              in
                scan rest installed (add_views installed event views 1 found)
              end
      in
        scan (List.foldl select [] history) (Binaryset.empty Int.compare) []
      end
    (* The same bundle event may be installed into separate sets with
       different attached views. Compare compiled statements, not proofs. *)
    fun same_view ((a,s,v),(b,t,w)) =
      a = b andalso same_rewrite_source (s,t) andalso
      aconv (concl v) (concl w) andalso HOLset.equal (hypset v,hypset w)
    fun active_views_of history sources =
      let
        fun collect_view ((source,_,SOME (SOME _)),queries) = source::queries
          | collect_view (_,queries) = queries
        fun collect (ADDFRAG (SSFRAG_CON {views,...},_,_,_),queries) =
              List.foldl collect_view queries views
          | collect (_,queries) = queries
      in
        case List.foldl collect [] history of
            [] => []
          | queries =>
              active_views history queries
                (#1 (queried_source_index queries sources))
      end
    fun views_changed () =
      (* A viewless addition introduces its own event's sources only.
         A view in the shared history can only use an earlier source. *)
      not (viewless_delta orelse
           (same_history andalso
            Portable.pointer_eq (#native_sources old,#native_sources current)))
      andalso not (ListPair.allEq same_view
        (active_views_of (#history old) (#native_sources old),
         active_views_of (#history current) (#native_sources current)))
    fun same_prepared (NONE,NONE) = true
      | same_prepared (SOME (a:prepared_native),SOME (b:prepared_native)) =
          Portable.pointer_eq (#rules a,#rules b)
      | same_prepared _ = false
    fun same_structure (ADDFRAG (_,a,p,_),ADDFRAG (_,b,q,_)) =
          a = b andalso same_prepared (p,q)
      | same_structure (a,b) = Portable.pointer_eq (a,b)
    fun only [] _ = []
      | only convs [] = convs
      | only convs others =
          let
            (* A short scan avoids constructing an index for small sets. *)
            val present =
              if length others < 64 then
                fn id => List.exists (fn (other,_) => id = other) others
              else
                let
                  val identities = List.foldl
                    (fn ((id,_),set) => Binaryset.add (set,id))
                    (Binaryset.empty
                      (Lib.pair_compare (Int.compare,Int.compare)))
                    others
                in fn id => Binaryset.member (identities,id) end
          in
            List.filter (not o present o #1) convs
          end
    val changed = only old_convs new_convs @ only new_convs old_convs
    val old_strategy = #strategy old
    val new_strategy = #strategy current
    fun same_option (NONE,NONE) = true
      | same_option (SOME a,SOME b) = Portable.pointer_eq (a,b)
      | same_option _ = false
    val strategy_changed =
      #cond_depth old_strategy <> #cond_depth new_strategy orelse
      not (same_option
        (#subgoaler old_strategy,#subgoaler new_strategy)) orelse
      not (same_option (#term_ord old_strategy,#term_ord new_strategy)) orelse
      not (ListPair.allEq Portable.pointer_eq
        (#unsafe_solvers old_strategy,#unsafe_solvers new_strategy))
    val rebuild =
      #limit old <> #limit current orelse strategy_changed orelse
      not (Portable.pointer_eq (#dprocs old,#dprocs current)) orelse
      not (ListPair.allEq same_structure (old_structure,new_structure)) orelse
      not (ListPair.allEq Portable.pointer_eq (old_makers,new_makers)) orelse
      List.exists (fn (_,key) => not (Option.isSome key)) changed orelse
      views_changed ()
  in
    {keys=List.mapPartial #2 changed, rebuild=rebuild,
     context_sensitive=not (null (#dprocs old) andalso
                            null (#dprocs current))}
  end

(*---------------------------------------------------------------------------*)
(* SIMP_QCONV : simpset -> thm list -> conv                                  *)
(*---------------------------------------------------------------------------*)

 exception CONVNET of net;

 (* Invocation-supplied bounded rewrites are decoded once, then compiled
    against each marker-adjusted simpset without allocating fresh controls. *)
 type prepared_rewrites = controlled_thm list

 fun prepare_rewrites thms : prepared_rewrites =
   map dest_tagged_rewrite thms

 fun source_thms (prepared : prepared_rewrites) = map #1 prepared

 fun context_convdata _ _ [] = []
   | context_convdata name mk_rewrs (prepared : prepared_rewrites) =
     let
       (* Finish the rewrite makers before constructing any conversions. *)
       val groups = map mk_rewrs prepared
       val rule_name = SOME {Thy = "", Name = name}
       fun compile (rw,acc) =
         case mk_rewr_convdata (rule_name,rw) of
             SOME data => data::acc
           | NONE => acc
     in
       List.rev (List.foldl (fn (rules,acc) => List.foldl compile acc rules)
                            [] groups)
     end

 (* Both extension projections use this setup once. Collectors
    continue compiling facts at their original consumption stage. *)
 fun rewriter_context_for_ss_prepared
       (SS{mk_rewrs,initial_net,...}) prepared = let
   val prepared_net =
     net_add_convs initial_net
       (context_convdata "rewrite: prepared context" mk_rewrs prepared)
   fun addcontext (context,thms) = let
     val net = (raise context) handle CONVNET net => net
     val cthms = map dest_tagged_rewrite thms
     val data = context_convdata "rewrite: from context" mk_rewrs cthms
   in
     CONVNET (net_add_convs net data)
   end
   in {initial=CONVNET prepared_net,addcontext=addcontext} end;

 fun legacy_rewriter_for_ss_prepared ss prepared = let
   val {initial,addcontext} = rewriter_context_for_ss_prepared ss prepared
   fun apply {solver,conv,context,stack,relation} tm = let
     val net = (raise context) handle CONVNET net => net
   in
     tryfind (fn {ci = {conval,...},...} => conval solver stack tm)
             (lookup tm net)
   end
   in lift (Traverse.REDUCER
        {name=SOME "rewriter_for_ss", addcontext=addcontext,
         apply=apply, initial=initial}) end;

 fun configured_rewriter_for_ss_prepared check_abort traversal ss prepared = let
   val {initial,addcontext} = rewriter_context_for_ss_prepared ss prepared
   exception PolicyAbort of exn
   fun apply {solver,conv,context,stack,cond_depth,term_ord,relation} tm = let
     val net = (raise context) handle CONVNET net => net
     val ctxt = {solver=solver, stack=stack, cond_depth=cond_depth,
                 term_ord=term_ord}
     (* Only the policy check is an abort; conversion exceptions remain
        candidate rejection. Transport an abort as a successful search
        result, then rethrow OUTSIDE tryfind so no later callback runs. *)
     fun keep policy =
       TraverseExt.keep_abstraction policy tm
       handle e => raise PolicyAbort e
     fun apply_entry
           ({ci = {name,...},configured={conval,...},...} : net_conv_info) =
       case traversal of
           ChildFirst policy =>
             if name = "ETA_CONV (eta reduction)" andalso
                is_comb tm andalso is_abs (rand tm) andalso
                keep policy then
               raise UNCHANGED
             else conval ctxt tm
         | ParentFirst => conval ctxt tm
     fun attempt entry =
       case Exn.capture check_abort () of
           Exn.Exn e => Exn.Exn e
         | Exn.Res () => Exn.Res (apply_entry entry)
             handle PolicyAbort e => Exn.Exn e
   in
     case traversal of
         ParentFirst => tryfind apply_entry (lookup tm net)
       | ChildFirst _ => Exn.release (tryfind attempt (lookup tm net))
   end
   in CONFIG_REDUCER
        {name=SOME"rewriter_for_ss", addcontext=addcontext, apply=apply,
         initial=initial}
   end;

 fun configured_traversedata_for_ss_prepared check_abort traversal
       (ss as (SS ssdata)) (prepared : prepared_rewrites)
       : TraverseExt.traverse_data =
   let
     val existing_dprocs = #dprocs ssdata
     val dprocs =
       if null existing_dprocs orelse null prepared then existing_dprocs
       else map (TraverseExt.addctxt (source_thms prepared)) existing_dprocs
   in
      {rewriters=[configured_rewriter_for_ss_prepared
                    check_abort traversal ss prepared],
       dprocs=dprocs,
       relation= boolSyntax.equality,
       travrules= #travrules ssdata,
       limit = #limit ssdata}
   end;

 (* The tracked default projection omits traversal-strategy settings and
    forwards extension decision procedures unchanged. Both projections share
    installed matchers and their actual controls; neither promotes a set. *)
 fun default_traversedata_for_ss (ss as SS data) : TraverseExt.traverse_data =
   {rewriters=[legacy_rewriter_for_ss_prepared ss []],
    dprocs= #dprocs data, relation=boolSyntax.equality,
    travrules= #travrules data, limit= #limit data};

 (* Settings used only by the explicit configured projection. *)
 fun traverseconfig_for_ss (SS ssdata) : TraverseExt.traverse_config =
   let
     val strategy = #strategy ssdata
   in
      {subgoaler= #subgoaler strategy,
       solvers= #unsafe_solvers strategy,
       cond_depth= #cond_depth strategy,
       term_ord= #term_ord strategy}
   end;

 fun xtraversedata_with_abort check_abort traversal ss prepared
       : TraverseExt.xtraverse_data =
   (configured_traversedata_for_ss_prepared check_abort traversal ss prepared,
    traverseconfig_for_ss ss);

 fun xtraversedata_for_ss_prepared traversal ss prepared =
   xtraversedata_with_abort (fn () => ()) traversal ss prepared;

 fun traversedata_for_ss ss = default_traversedata_for_ss ss;
 fun xtraversedata_for_ss ss = xtraversedata_for_ss_prepared ParentFirst ss [];

 fun SIMP_QCONV_WITH_XDATA traversal xdata reducer_context solver_context =
   TraverseExt.TRAVERSE_WITH_CONTEXT traversal xdata
     {reducer_context=reducer_context,solver_context=solver_context};

 (* Only settings consumed by conversions opt into the extended engine.
    Tactic-only loopers and safe solvers do not change context lifetime. *)
 fun traversal_for_ss ss =
   case traverseconfig_for_ss ss of
       {subgoaler=NONE,solvers=[],cond_depth=NONE,term_ord=NONE} =>
         (traversedata_for_ss ss, TraverseExt.TRAVERSE)
     | config =>
         (configured_traversedata_for_ss_prepared (fn () => ()) ParentFirst
            ss [],
          fn data => TraverseExt.XTRAVERSE (data,config));

 fun SIMP_QCONV ss =
   let val (data, traverse) = traversal_for_ss ss in traverse data end;

val Cong   = markerLib.Cong
val Split  = markerLib.Split
val AC     = markerLib.AC;
val Excl   = markerLib.Excl
val ExclX  = markerLib.ExclX
val ExclSF = markerLib.ExclSF
val Req0   = markerLib.mk_Req0
val ReqD   = markerLib.mk_ReqD

local open markerLib
in
val frag_of = simpCommon.frag_of lookup_named_frag

(* SF registers its fragment unless this registry has the name, even when
   simpLib's has it *)
val SF = simpCommon.SF {frag_name = frag_name,
                        lookup_named_frag =
                          simpCommon.lookup_named_frag ssfragDB_slot,
                        register_frag = register_frag}

(* A [Split] marker whose theorem cannot be turned into a split rule --
   one that is not shaped like a split rule at all -- drops the marker
   instead of aborting.  [process_tags] is applied to the goal's own
   assumptions as well as to a rule list (see [counted_psr] and the
   implication rebuild in [GEN_GLOBAL_SIMP_TAC]), and there a
   marker-headed assumption is a term the user is reasoning about rather
   than an instruction to the simplifier; the tactics that scan
   assumptions are documented never to fail.  Where the marker was
   written explicitly the drop is reported, because silently ignoring a
   rule that was asked for is worse than a warning. *)
fun add_split_marker report split ss =
    add_split split ss
    handle HOL_ERR e =>
      (if report then
         HOL_WARNING "simpExtLib" "process_tags"
                     ("Ignoring unusable Split rule: " ^ message_of e)
       else ();
       ss)


fun process_tags0 {report,preserve} ss thl =
    simpCommon.process_tags
      {frag_of = frag_of,
       remove_ssfrags = remove_ssfrags_with_controls preserve,
       add = op ++, force_add = force_add,
       cong_ac = fn congs => fn acs =>
         SSFRAG_CON
           {name=SOME "Cong and/or AC", convs=[], rewrs=[],
            ac=map source_slot acs, views=[], filter=NONE,
            dprocs=[], congs=congs, threaded_congs=[], relsimps=[],
            loopers=[], unsafe_solvers=[], safe_solvers=[]},
       extension = SOME {report = report, add_split = add_split_marker report},
       exclude = apply_exclusions}
      ss thl

(* [process_tags] handles a rule list the user wrote; [process_asm_tags]
   handles theorems taken from the goal's assumptions, where a marker is
   an accident of the terms being reasoned about. *)
fun process_tags ss thl =
  process_tags0 {report=true,preserve=false} ss thl
fun process_asm_tags ss thl =
  process_tags0 {report=false,preserve=true} ss thl

(* Bind survivors while processing removal, not by replaying the resulting
   history a second time. Direct exclusions already retain actual controls. *)
fun prepare_rewrite_arguments ss thl =
  process_tags0 {report=true,preserve=true} ss thl

(* Inspection only. Marker processing is explicit construction, performed by
   prepare_rewrite_arguments before calling this getter. Decode a supplied
   bound without allocating a throwaway control. *)
fun rewrite_sources (SS data) thl =
  let
    fun supplied th =
      let
        val plain = #1 (BoundedRewrites.DEST_BOUNDED th)
                    handle HOL_ERR _ => th
        val _ = case markerLib.dest_directive plain of
                    NONE => ()
                  | SOME _ => raise ERR ("rewrite_sources",
                      "prepare directives with prepare_rewrite_arguments")
      in plain end
  in (#rewrite_sources data, map supplied thl) end

fun SIMP_CONV ss =
    simpCommon.SIMP_CONV {process_tags = process_tags, qconv = SIMP_QCONV} ss

(* Policy HOL_ERR is an abort, not a failed rewrite/eta candidate. The
   traversal and native ETA entry must share this guard. Scope it per call,
   restoring an enclosing failure even when a callback reenters a saved
   preparation. Pretests need the same lifetime, but no quota changes. *)
fun protect_child_first_callback failure callback argument =
  case !failure of
      SOME e => raise e
    | NONE => callback argument
        handle e => (failure := SOME e; raise e)

fun check_child_first_abort failure () =
  case !failure of NONE => () | SOME e => raise e

fun with_child_first_callbacks failure operation argument =
  let
    val previous = !failure
    fun run argument =
      let
        val _ = failure := NONE
        val result = operation argument
      in case !failure of NONE => result | SOME e => raise e end
      handle e =>
        (case !failure of NONE => raise e | SOME original => raise original)
  in
    Portable.finally (fn () => failure := previous) run argument
  end

fun SIMP_CONV_CHILD_FIRST
      (policy : TraverseExt.child_first_policy) ss l tm =
  let
    val (ss', l') = process_tags ss l
    val failure = ref (NONE : exn option)
    val policy =
      {charge=protect_child_first_callback failure (#charge policy),
       keep_abstraction=
         protect_child_first_callback failure (#keep_abstraction policy)}
  in
    with_child_first_callbacks failure
      (TRY_CONV
        (TraverseExt.CHILD_FIRST_WITH_ABORT
           (check_child_first_abort failure) NONE policy
           (xtraversedata_with_abort (check_child_first_abort failure)
              (ChildFirst policy) ss' [])
           {reducer_context=l',solver_context=[]})) tm
  end;

fun prepare_child_first_with_observer observer
      (policy : TraverseExt.child_first_policy) (ss as SS data) =
  let
    val callback_failure = ref (NONE : exn option)
    fun protected callback argument =
      protect_child_first_callback callback_failure callback argument
    val policy =
      {charge=protected (#charge policy),
       keep_abstraction=protected (#keep_abstraction policy)}
    val observer = Option.map protected observer
    val check_abort = check_child_first_abort callback_failure
    val xdata = xtraversedata_with_abort check_abort (ChildFirst policy) ss []
    val bounds = Ho_Net.fold'
      (fn ({configured={bound,...},...} : net_conv_info) => fn found =>
        case bound of NONE => found | SOME allowance => allowance :: found)
      (#initial_net data) []
    fun scoped conversion tm =
      let
        val saved = map (fn (r, _) => (r, !r)) bounds
        fun restore () = List.app (fn (r, n) => r := n) saved
        fun run argument =
          (List.app (fn (r, declared) => r := declared) bounds;
           with_child_first_callbacks callback_failure conversion argument)
      in
        Portable.finally restore run tm
      end
    fun traversal premises =
      TraverseExt.CHILD_FIRST_WITH_ABORT check_abort observer policy xdata
        {reducer_context=premises,solver_context=[]}
    fun child premises = QCONV (TRY_CONV (traversal premises))
    fun observed conversion tm =
      case observer of
          NONE => conversion tm
        | SOME visit =>
            let
              val _ = visit tm
              val theorem = conversion tm
              val _ = visit (boolSyntax.rhs (concl theorem))
            in theorem end
    fun opaque_event
          (ADDFRAG (SSFRAG_CON {congs,threaded_congs,relsimps,...},_,_,_)) =
          not (null congs andalso null threaded_congs andalso null relsimps)
      | opaque_event _ = false
    val opaque = not (null (#dprocs data)) orelse
                 List.exists opaque_event (#history data)
    fun reducible tm =
      not (null (Ho_Net.lookup tm (#initial_net data))) orelse
      (is_comb tm andalso
       (is_abs (rator tm) orelse
        reducible (rator tm) orelse reducible (rand tm))) orelse
      (is_abs tm andalso reducible (#2 (dest_abs tm)))
    fun arguments_reducible tm =
      if is_comb tm then
        (is_abs (rand tm) andalso
         not (TraverseExt.keep_abstraction policy tm)) orelse
        reducible (rand tm) orelse arguments_reducible (rator tm)
      else if is_abs tm then reducible (#2 (dest_abs tm))
      else false
  in
    {normalize = fn premises => scoped (observed (child premises)),
     arguments = fn premises => scoped (observed
       (TraverseExt.NORMALIZE_ARGUMENTS policy (child premises))),
     may_reduce_arguments = with_child_first_callbacks callback_failure
       (fn tm => opaque orelse arguments_reducible tm)}
  end;

fun prepare_child_first policy =
  prepare_child_first_with_observer NONE policy;

fun prepare_child_first_observed observe policy =
  prepare_child_first_with_observer (SOME observe) policy;

fun SIMP_PROVE ss =
    simpCommon.SIMP_PROVE {process_tags = process_tags, qconv = SIMP_QCONV} ss

infix &&;

fun (ss && thl) =
    simpCommon.add_rewrites
      {process_tags = process_tags, add = op ++, rewrites = rewrites}
      (ss, thl)

end;

(*---------------------------------------------------------------------------*)
(*   SIMP_TAC      : simpset -> thm list -> tactic                           *)
(*   ASM_SIMP_TAC  : simpset -> thm list -> tactic                           *)
(*   FULL_SIMP_TAC : simpset -> thm list -> tactic                           *)
(*                                                                           *)
(* FAILURE CONDITIONS                                                        *)
(*                                                                           *)
(* These tactics never fail, though they may diverge.                        *)
(* --------------------------------------------------------------------------*)


fun SIMP_RULE ss l = CONV_RULE (SIMP_CONV ss l)

fun ASM_SIMP_RULE ss = simpCommon.ASM_SIMP_RULE SIMP_RULE ss

type simp_mode = {safe : bool}

fun reconcile_hyps asl th =
  let
    val hypotheses = hyp th
    val find_asm =
      if HOLset.numItems (hypset th) < 64 orelse length asl < 128 then
        (fn h => List.find (aconv h) asl)
      else
        let
          (* Index assumptions only as far as needed. Termtab compares
             up to alpha equivalence, and default keeps the first match. *)
          val unindexed = ref asl
          val index = ref Termtab.empty
          fun advance h [] = (unindexed := []; NONE)
            | advance h (asm::rest) =
                (index := Termtab.default (asm,asm) (!index);
                 if aconv h asm then (unindexed := rest; SOME asm)
                 else advance h rest)
          fun lookup h =
            case Termtab.lookup (!index) h of
                NONE => advance h (!unindexed)
              | found => found
        in lookup end
    fun asm_for h =
      case find_asm h of
          SOME a => a
        | NONE => raise ERR ("GEN_SIMP_TAC", "Solver introduced a hypothesis")
    fun replace_hyp h result = PROVE_HYP (ASSUME (asm_for h)) result
  in
    Lib.itlist ADD_ASSUM asl (Lib.itlist replace_hyp hypotheses th)
  end

fun simp_conv_with_xdata traversal xdata reducer_context solver_context =
  TRY_CONV
    (SIMP_QCONV_WITH_XDATA traversal xdata reducer_context solver_context)

fun first_tactic enabled apply entries =
  let
    fun first [] g ctxt = NO_TAC g ctxt
      | first (entry::rest) g ctxt =
          if enabled entry then
            (apply entry g ctxt handle HOL_ERR _ => first rest g ctxt)
          else first rest g ctxt
  in first entries end

fun final_solver_tac traversal xdata (mode : simp_mode) ss
      reducer_context solver_context =
  let
    val s = strategy_of ss
    val solvers =
      if #safe mode then #safe_solvers s else #unsafe_solvers s
    fun solve_with prover_ctxt ({solve,...} : TraverseExt.ssolver) (asl,w) =
      let
        val th = solve prover_ctxt w
        val _ = aconv (concl th) w orelse
                raise ERR ("GEN_SIMP_TAC", "Solver proved the wrong term")
      in
        ACCEPT_TAC (reconcile_hyps asl th) (asl,w)
      end
  in
    if null solvers then NO_TAC
    else fn g => fn ctxt =>
      let
        val prover_ctxt =
          {stack=[], context_thms=reducer_context @ solver_context,
           recurse=QCONV
             (simp_conv_with_xdata traversal xdata
                reducer_context solver_context)}
      in
        first_tactic (K true) (solve_with prover_ctxt) solvers g ctxt
      end
  end

fun looper_tac ss =
  let
    val s = strategy_of ss
    (* Suppression displays belong to the split/case namespaces, not to
       ordinary user loopers that happen to have the same literal name. *)
    fun enabled (LooperEntry {kind=OrdinaryLooper,...}) = true
      | enabled entry =
          not (Binaryset.member (#excl_loopers s,looper_display entry))
    (* An UNCHANGED raised before context application declines this looper. *)
    fun apply (LooperEntry {apply,...}) g =
      apply ss g
      handle Conv.UNCHANGED => NO_TAC g
  in
    first_tactic enabled apply (#loopers s)
  end

fun bounded_looper rounds tac g =
  case !rounds of
      SOME n =>
        if n <= 0 then NO_TAC g
        else
          let val result = tac g
          in
            rounds := SOME (n - 1);
            result
          end
    | NONE => tac g

(* [xdata_of] extracts traversal data from a marker-adjusted tracked set. *)
fun gen_simp_tac_with_rounds rounds traversal
      xdata_of solver_context (mode : simp_mode) ss ths =
  with_tactic_context (fn g =>
    let
      fun start supplied recur =
        let
          val (base,rules) = prepare_rewrite_arguments ss supplied
          (* A supplied allowance belongs to the invocation, not to each
             looper branch or solver recursion. Solver facts are untagged. *)
          val bundle = prepare_rewrite_bundle base rules
          val invocation = if null rules then base
            else install_rewrite_bundle bundle [] base
          val RewriteBundle {context,...} = bundle
          val solver_context = context @ solver_context
          fun main tagged_thms =
            let
              val (invocation_ss,context_thms) =
                process_asm_tags invocation tagged_thms
              val xdata = xdata_of invocation_ss
              val rewr_tac =
                CONV_TAC
                  (simp_conv_with_xdata traversal xdata
                     context_thms solver_context)
              val solve_tac =
                final_solver_tac traversal xdata mode invocation_ss
                                 context_thms solver_context
              val loop_tac =
                bounded_looper rounds (looper_tac invocation_ss)
            in
              rewr_tac THEN
              (solve_tac ORELSE
               TRY (loop_tac THEN_LT ALLGOALS (recur main)))
            end
        in
          main
        end
    in
      markerLib.process_taclist_then_bind {arg=ths} start g
    end)

fun gen_simp_tac_with_xdata traversal xdata solver_context mode ss ths g =
  gen_simp_tac_with_rounds (ref (getlimit ss)) traversal
    xdata solver_context mode ss ths g

fun GEN_SIMP_TAC mode =
  gen_simp_tac_with_xdata ParentFirst xtraversedata_for_ss [] mode

fun GEN_SIMP_TAC_CHILD_FIRST policy mode =
  gen_simp_tac_with_xdata (ChildFirst policy)
    (fn ss => xtraversedata_for_ss_prepared (ChildFirst policy) ss []) [] mode

(* Plain tactic entry points retain simpLib's marker processing and pass
   schedule unless the invocation opts into a traversal strategy. *)
fun strategy_free ss ths =
  let
    val s = strategy_of ss
    fun frag_free (SSFRAG_CON {loopers,unsafe_solvers,safe_solvers,...}) =
      null loopers andalso null unsafe_solvers andalso null safe_solvers
    (* Req0/ReqD and successful bounded removal preserve concl; a failed
       bound falls through to that same head. Do not build proofs or run
       monitor hooks here, nor inspect payloads underneath AC or Cong. *)
    fun arg_free th =
      if (same_const markerSyntax.Split_tm
            (#1 (strip_comb (concl th))) handle HOL_ERR _ => false) then
        false
      else
        case markerLib.destFRAG th of
            NONE => true
          | SOME nm =>
              (case lookup_named_frag nm of
                   NONE => true (* Defer errors to the old lookup stage. *)
                 | SOME frag => frag_free frag)
  in
    null (#loopers s) andalso null (#unsafe_solvers s) andalso
    null (#safe_solvers s) andalso not (Option.isSome (#subgoaler s)) andalso
    not (Option.isSome (#cond_depth s)) andalso
    not (Option.isSome (#term_ord s)) andalso List.all arg_free ths
  end

fun ASM_SIMP_TAC ss ths gl =
    if strategy_free ss ths then
      markerLib.process_taclist_then{arg=ths} (CONV_TAC o SIMP_CONV ss) gl
    else GEN_SIMP_TAC {safe=false} ss ths gl
val asm_simp_tac = ASM_SIMP_TAC
fun SIMP_TAC ss ths = ASM_SIMP_TAC ss (markerLib.NoAsms::ths)
val simp_tac = SIMP_TAC

type simptac_config = simpCommon.simptac_config
val BF_ASSUME_TAC = simpCommon.BF_ASSUME_TAC

local
  val tacs = simpCommon.full_simp_tacs {simp_rule = SIMP_RULE,
                                        asm_simp_tac = ASM_SIMP_TAC}
  fun wrap tac ss ths = with_tactic_context (tac ss ths)
in
  val FULL_SIMP_TAC = wrap (#FULL_SIMP_TAC tacs)
  val REV_FULL_SIMP_TAC = wrap (#REV_FULL_SIMP_TAC tacs)
  val NO_STRIP_FULL_SIMP_TAC = wrap (#NO_STRIP_FULL_SIMP_TAC tacs)
  val NO_STRIP_REV_FULL_SIMP_TAC = wrap (#NO_STRIP_REV_FULL_SIMP_TAC tacs)
end
val full_simp_tac = FULL_SIMP_TAC
val rev_full_simp_tac = REV_FULL_SIMP_TAC

val stdcon = simpCommon.stdcon

val popper_of = simpCommon.popper_of

fun psr (cfg : simptac_config) ss =
    with_tactic_context
      (popper_of cfg (fn th =>
         ASSUM_LIST (fn asms => stdcon cfg (SIMP_RULE ss asms th))))

fun allasms cfg ss (g as (asl,_)) = ntac (length asl) (psr cfg ss) g

type xsimptac_config =
     {base : simptac_config, concl_in_fixpoint : bool, imp_rebuild : bool,
      imp_premises : bool}

fun same_goals (goals1,goals2) = boolSyntax.goals_eq goals1 goals2

(* Apply a continuation independently to annotated goals, retaining all
   validation functions. *)
fun map_annotated next annotated ctxt =
    let
      val (outputs,validations) =
          ListPair.unzip (map (fn (g,state) => next state g ctxt) annotated)
      val output = List.concat outputs
      val lengths = map length outputs
      val validate = mapshape lengths validations
    in
      (output,validate)
    end

fun bind_annotated (annotated,validation) next ctxt =
    let val (output,validate) = map_annotated next annotated ctxt
    in (output,validation o validate)
    end

fun continue_annotated (annotated,validation) next ctxt =
    let
      fun tag_result state g ctxt =
        let val (goals,validate) = next state g ctxt
        in (map (fn goal => (goal,())) goals,validate)
        end
      val (tagged,validate) = map_annotated tag_result annotated ctxt
    in
      (map #1 tagged,validation o validate)
    end

(* Continue from an unannotated tactic result. *)
fun then_annotated (goals,validation) next ctxt =
    continue_annotated
      (map (fn g => (g,())) goals,validation) (fn () => next) ctxt

fun rotate_assumption cfg =
    popper_of cfg (BF_ASSUME_TAC (not (#oldestfirst cfg)))

fun counted_psr traversal cfg ss xdata_of solver_context assumptions g ctxt =
    let
      (* [simplify] runs inside a callback, so what it learns about the
         assumption is smuggled out through this cell. *)
      val outcome = ref (NONE : {changed:bool, expected:goal list} option)
      fun simplify th =
        assumptions
          (fn asms => fn popped_goal => fn ctxt =>
             let
               val (invocation_ss,reducer_context) =
                 process_asm_tags ss asms
               val simplified =
                 CONV_RULE
                   (simp_conv_with_xdata traversal (xdata_of invocation_ss)
                      reducer_context solver_context) th
               val ordinary =
                 BF_ASSUME_TAC
                   (not (#oldestfirst cfg)) simplified popped_goal ctxt
               val _ =
                 outcome :=
                   SOME {changed=not (aconv (concl th) (concl simplified)),
                         expected= #1 ordinary}
             in
               stdcon cfg simplified popped_goal ctxt
             end)
      val (goals,validation) = popper_of cfg simplify g ctxt
      val {changed,expected} =
        case !outcome of
            SOME outcome => outcome
          | NONE => raise ERR ("counted_psr", "missing assumption")
      val structural = not (same_goals (goals,expected))
      val info = {changed=changed orelse structural,
                  structural=structural}
    in
      (map (fn goal => (goal,info)) goals,validation)
    end

fun counted_pass traversal cfg ss xdata_of solver_context assumptions initial_k
                 (g as (asl,_)) ctxt =
    let
      val n = length asl
      val initial =
        {last= ~1, structural=false, k=initial_k, index=0}
      fun loop state goal ctxt =
        if #index state = n then ([(goal,state)],hd)
        else
          let
            val step =
              if #k state = 0 then
                let
                  val (goals,validation) = rotate_assumption cfg goal ctxt
                    val info = {changed=false,structural=false}
                in (map (fn g => (g,info)) goals,validation)
                end
              else counted_psr traversal cfg ss xdata_of
                     solver_context assumptions goal ctxt
            fun next {changed,structural} =
              let
                val k =
                  if changed then ~1
                  else if #k state < 0 then ~1
                  else Int.max (0,#k state - 1)
                val state' =
                  {last=if changed then #index state else #last state,
                   structural= #structural state orelse structural,
                   k=k, index= #index state + 1}
              in
                loop state'
              end
          in
            bind_annotated step next ctxt
          end
    in
      loop initial g ctxt
    end

fun gen_global_simp_tac_with_bound traversal bound mode
      ({base,concl_in_fixpoint,imp_rebuild,imp_premises} : xsimptac_config)
      ss0 =
  let
    val bound_context = case bound of
        NONE => []
      | SOME (RewriteBundle {context,...}) => context
    (* Local directives preserve all installed controls in one replay.
       In particular the already installed bundle must not be reconstructed
       as supplied arguments, or repaired by a second history replay. *)
  in
    with_tactic_context o markerLib.mk_require_tac (
      markerLib.ABBRS_THEN (
        markerLib.LLABEL_RES_THEN (
          fn thl =>
             let
               (* Tactic-only assumption controls are not rewrite tags.
                  Retain them for every changing proof context. *)
               val assumption_controls = List.filter
                     (fn th => case markerLib.dest_directive
                                      (markerLib.strip_wrappers th) of
                         SOME markerLib.DNoAsms => true
                       | SOME (markerLib.DIgnAsm _) => true
                       | _ => false) thl
               val assumptions =
                 if null assumption_controls then ASSUM_LIST
                 else fn next => markerLib.process_taclist_then_bind
                   {arg=assumption_controls} (fn _ => fn _ => next)
               fun selected_context context target ctxt =
                 if null assumption_controls then context
                 else
                   let
                     val selected = ref []
                     val _ = assumptions
                       (fn ths => (selected := ths; ALL_TAC))
                       (map concl context,target) ctxt
                   in !selected end
               val (ss1,thl') = prepare_rewrite_arguments ss0 thl
               val prepared = prepare_rewrites thl'
               val solver_context = bound_context @ source_thms prepared
               (* Each local marker-adjusted simpset compiles these prepared
                  rules while retaining their invocation-wide controls. *)
               val ss = ss1

               fun strip_implications (g as (_,w)) ctxt =
                 if can boolSyntax.dest_imp_only w then
                   (DISCH_TAC THEN strip_implications) g ctxt
                 else ALL_TAC g ctxt

               val pop_head_mp = POP_ASSUM MP_TAC

               (* Every assumption, fixpoint pass, conclusion pass and
                  rebuild-scan suffix asks for a traversal state, and
                  compiling one costs a pass over the invocation's rules.
                  Markers among the assumptions are the exception, so the
                  requests almost always present the same simpset and get
                  the same state back; the state is a function of that
                  simpset and of the prepared rules alone, so one built for
                  an earlier request serves a later one.

                  The key test is [Portable.pointer_eq], so the hits
                  depend on [process_tags0] handing back its argument
                  simpset itself on the marker-free path.  A version that
                  rebuilt the simpset unconditionally would turn every hit
                  into a miss and recompile the rules on every request, with
                  no test failing. *)
               val traversal_cache = ref NONE
               fun traversal_state invocation_ss =
                 let
                   fun build () =
                     let
                       val data =
                         xtraversedata_for_ss_prepared
                           traversal invocation_ss prepared
                     in
                       traversal_cache := SOME (invocation_ss,data);
                       data
                     end
                 in
                   case !traversal_cache of
                       SOME (cached_ss,data) =>
                         if Portable.pointer_eq (cached_ss,invocation_ss)
                         then data else build ()
                     | NONE => build ()
                 end

               (* Conclusion/fixpoint reentry and sibling branches belong
                  to this same global invocation's looper budget. *)
               val rounds = ref (getlimit ss)
               val conclusion_tac =
                 gen_simp_tac_with_rounds rounds
                   traversal traversal_state solver_context mode ss
                   assumption_controls

               fun root_rewrite_of context target ctxt =
                 let
                   val context = selected_context context target ctxt
                   val (invocation_ss,reducer_context) =
                     process_asm_tags ss context
                   val root_rewrite =
                     TraverseExt.ROOT_REWRITE_WITH_CONTEXT
                       (traversal_state invocation_ss)
                 in
                   SOME (root_rewrite
                           {reducer_context=reducer_context,
                            solver_context=solver_context} target)
                   handle HOL_ERR _ => NONE
                        | Conv.UNCHANGED => NONE
                 end

               (* A rule stated on the whole implication is a redex of the
                  conclusion as it stands, and [strip_implications] takes
                  that term apart before the traversal has seen it: the
                  traversal's own order is outside-in, so the rules are
                  owed the root before the premises leave it.  [rebuild]
                  recovers a root rewrite once the fixpoint has finished,
                  but on the conclusion the fixpoint has left -- and an
                  equation whose right-hand side simplified away is no
                  longer the term the rule is stated on. *)
               fun root_first (goal as (asl,w)) ctxt =
                 if not (can boolSyntax.dest_imp_only w) then ALL_TAC goal ctxt
                 else
                   case root_rewrite_of (map ASSUME asl) w ctxt of
                       NONE => ALL_TAC goal ctxt
                     | SOME eq =>
                         let
                           val _ = aconv (lhs (concl eq)) w orelse
                             raise ERR ("GEN_GLOBAL_SIMP_TAC",
                                        "bad root rewrite")
                         in
                           CONV_TAC (K eq) goal ctxt
                         end

               (* [outer] is a suffix of the assumption list and [assumed]
                  the matching suffix of its theorems, so that the scan
                  does not re-[ASSUME] the tail it is about to walk. *)
               fun find_rebuild nested (outer,assumed) count ctxt =
                 case (outer,assumed) of
                     (a::rest, _::assumed_rest) =>
                       let
                         val target = mk_imp (a,nested)
                       in
                         case root_rewrite_of assumed_rest target ctxt of
                             SOME eq => SOME (count,target,eq)
                           | NONE =>
                               find_rebuild target (rest,assumed_rest)
                                            (count + 1) ctxt
                       end
                   | _ => NONE

               fun fixpoint k goal ctxt =
                 let
                   val pass as (annotated,validation) =
                     counted_pass traversal base ss traversal_state
                       solver_context assumptions k goal ctxt
                   val unchanged =
                     same_goals (map #1 annotated,[goal])
                   fun clear_change state =
                     if unchanged then
                       {last= ~1,structural=false,k= #k state,
                        index= #index state}
                     else state
                   val pass' =
                     (map (fn (g,state) => (g,clear_change state)) annotated,
                      validation)
                 in
                   continue_annotated pass' after_pass ctxt
                 end

               and after_pass state goal ctxt =
                 if concl_in_fixpoint then
                   let
                     val result as (goals,_) = conclusion_tac goal ctxt
                     fun continue next = then_annotated result next ctxt
                   in
                     if not (same_goals (goals,[goal])) then
                       continue (fixpoint ~1)
                     else if #structural state then
                       continue (fixpoint ~1)
                     else if #last state > 0 then
                       continue (fixpoint (#last state))
                     else if imp_rebuild then continue rebuild
                     else result
                   end
                 else if #structural state then fixpoint ~1 goal ctxt
                 else if #last state > 0 then fixpoint (#last state) goal ctxt
                 else final_conclusion goal ctxt

               and final_conclusion goal ctxt =
                 let
                   val result = conclusion_tac goal ctxt
                 in
                   if imp_rebuild then then_annotated result rebuild ctxt
                   else result
                 end

               and rebuild (goal as (asl,w)) ctxt =
                 case find_rebuild w (asl,map ASSUME asl) 1 ctxt of
                     NONE => ALL_TAC goal ctxt
                   | SOME (count,target,eq) =>
                       let
                         val _ = aconv (lhs (concl eq)) target orelse
                           raise ERR ("GEN_GLOBAL_SIMP_TAC",
                                      "bad root rewrite")
                       in
                         (ntac count pop_head_mp THEN
                          CONV_TAC (K eq) THEN strip_implications THEN
                          fixpoint ~1) goal ctxt
                       end
             in
               if imp_premises then
                 root_first THEN strip_implications THEN fixpoint ~1
               else fixpoint ~1
             end
        )
      )
    )
  end

fun gen_global_simp_tac_with traversal =
  gen_global_simp_tac_with_bound traversal NONE

fun GEN_GLOBAL_SIMP_TAC mode =
  gen_global_simp_tac_with ParentFirst mode

fun GEN_GLOBAL_SIMP_TAC_CHILD_FIRST policy mode =
  gen_global_simp_tac_with (ChildFirst policy) mode

fun GEN_GLOBAL_SIMP_TAC_CHILD_FIRST_BOUND policy mode cfg ss bundle =
  gen_global_simp_tac_with_bound (ChildFirst policy) (SOME bundle)
    mode cfg ss

fun global_simp_tac cfg ss0 thl gl =
    if strategy_free ss0 thl then
      simpCommon.global_simp_tac
        {process_tags = process_tags,
         add_rewrites = fn (ss,thl) => ss ++ rewrites thl,
         allasms = fn () => allasms,
         asm_simp_tac = ASM_SIMP_TAC}
        cfg ss0 thl gl
    else
      GEN_GLOBAL_SIMP_TAC {safe=false}
        {base=cfg,concl_in_fixpoint=false,imp_rebuild=false,
         imp_premises=false} ss0 thl gl





(* The ordinary engine's tracking extent, not a copy: Cond_rewrExt reports
   through Cond_rewr.note_rewrite, so both engines feed one list, in firing
   order. *)
val track = Cond_rewr.with_tracking

(* ----------------------------------------------------------------------
    creating per-type ssdata values
   ---------------------------------------------------------------------- *)

fun tyi_to_ssdata tyinfo =
    let
      val {name, thy, convs, rewrs} = simpCommon.tyi_frag_parts tyinfo
      val convs = map (lift_conv (SOME thy)) convs
      val rewrs = map source_slot rewrs
    in
      SSFRAG_CON
        {name=SOME name, convs=convs, rewrs=rewrs, ac=[], views=[],
         filter=NONE, dprocs=[], congs=[], threaded_congs=[], relsimps=[],
         loopers=[], unsafe_solvers=[], safe_solvers=[]}
    end

fun type_ssfrag ty = simpCommon.type_ssfrag tyi_to_ssdata ty


(*---------------------------------------------------------------------------*)
(* Pretty printers for ssfrags and simpsets                                  *)
(*---------------------------------------------------------------------------*)

val reducer_data = TraverseExt.reducer_data

fun dest_convdata tcd  =
    let
      val {thypart,source,prepared,bound,legacy,
           cd={name,key,...} : contextual_convdata} = tcd
    in
      (thypart,name,Option.map #2 key)
    end

fun pp_ssfrag (SSFRAG_CON {name,convs,rewrs,ac,views,dprocs,congs,
                         threaded_congs,...}) =
    simpCommon.pp_ssfrag
      {name = name, convs = map dest_convdata convs,
       dprocs = map (#name o reducer_data) dprocs,
       thm_blocks = [("Congruence rules",congs),
                     ("Threaded congruence rules",threaded_congs)],
       ac = map #item ac,
       named_blocks =
         [("Rewrite rules",map #item rewrs),
          ("Rewrite views",
           map (fn (s,th,_) => (#1 (source_rewrite s),th)) views)]}

fun pp_simpset (ss as SS {initial_net,strategy,...}) =
  let
    val {loopers,unsafe_solvers,safe_solvers,...} = strategy
    fun foldthis {thypart, ci = {name,...},...} nms =
      opttheory thypart name::nms
  in
    simpCommon.pp_simpset
      {net_names = Ho_Net.fold' foldthis initial_net [],
       frag_names = map frag_name (ssfrags_of ss),
       extra_sections =
         List.filter (not o null o #2)
           [("Loopers:",map looper_display loopers),
            ("Unsafe solvers:",map #name unsafe_solvers),
            ("Safe solvers:",map #name safe_solvers)]}
  end

end (* struct *)
