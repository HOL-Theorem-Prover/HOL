(*===========================================================================*)
(* FILE          : simpLib.sml                                               *)
(* DESCRIPTION   : A programmable, contextual, conditional simplifier        *)
(*                                                                           *)
(* AUTHOR        : Donald Syme                                               *)
(*                 Based loosely on original HOL rewriting by                *)
(*                 Larry Paulson et al,                                      *)
(*                 and not-so-loosely on the Isabelle simplifier.            *)
(*===========================================================================*)

structure simpLib :> simpLib =
struct

infix oo;

open Abbrev

local
open Feedback Lib Type Term Thm boolSyntax Drule Tactical
     Tactic Conv BoundedRewrites liteLib Trace
     Cond_rewr Travrules Traverse Ho_Net
in

type controlled_thm = BoundedRewrites.controlled_thm

structure Set = Binaryset

type thname = KernelSig.kernelname

local open markerTheory in end;

fun ERR x      = STRUCT_ERR "simpLib" x ;
fun WRAP_ERR x = STRUCT_WRAP "simpLib" x;

val option_cases = simpCommon.option_cases
val op oo = simpCommon.oo

(*---------------------------------------------------------------------------*)
(* Representation of conversions manipulated by the simplifier.              *)
(*---------------------------------------------------------------------------*)


type convdata = simpCommon.convdata
type tagged_convdata = {thypart : string option, cd : convdata}
val opttheory = simpCommon.opttheory

type stdconvdata = simpCommon.stdconvdata

(*---------------------------------------------------------------------------*)
(* Make a rewrite rule into a conversion.                                    *)
(*---------------------------------------------------------------------------*)

(* boolean argument to c is whether or not the rewrite is bounded *)
fun appconv (c,UNBOUNDED) = c false (* do not eta expand! *)
  | appconv (c,BOUNDED r) =
    let
      val c = c true (* do not inline! *)
    in
      fn solver => fn stk => Cond_rewr.bounded_apply r (c solver stk)
    end

fun mk_rewr_convdata rw : tagged_convdata option =
  simpCommon.mk_rewr_convdata
    (fn {thypart,name,key,th,tag,...} =>
        {thypart = thypart,
         cd = {name = name, key = key,
               trace = 100, (* no need to provide extra tracing here;
                               COND_REWR_CONV provides enough tracing itself *)
               conv = appconv (COND_REWR_CONV (name,th), tag)}})
    rw

(*---------------------------------------------------------------------------*)
(* Composable simpset fragments                                              *)
(*---------------------------------------------------------------------------*)

type relsimpdata = simpCommon.relsimpdata

datatype ssfrag = SSFRAG_CON of {
    name     : string option,
    convs    : tagged_convdata list,
    rewrs    : (thname option * thm) list,
    ac       : (thm * thm) list,
    filter   : (controlled_thm -> controlled_thm list) option,
    dprocs   : Traverse.reducer list,
    congs    : thm list,
    relsimps : relsimpdata list
}

fun frag_name (SSFRAG_CON {name,...}) = name

val normCong = simpCommon.normCong

fun SSFRAG {name,convs,rewrs,ac,filter,dprocs,congs} =
  SSFRAG_CON {name = name, rewrs = rewrs, ac = ac,
              convs = map (fn c => {thypart=NONE, cd = c}) convs,
              filter = filter, dprocs = dprocs, congs = map normCong congs,
              relsimps = []}

val empty_ssfrag = SSFRAG{name = NONE, rewrs = [], convs = [], ac = [],
                          filter = NONE, dprocs = [], congs = []}
fun ssf_upd_rewrs f (SSFRAG_CON s) =
    let
      val {name,rewrs,convs,ac,filter,dprocs,congs, relsimps} = s
    in
      SSFRAG_CON {name = name, rewrs = f rewrs, convs = convs, ac = ac,
                  filter = filter, dprocs = dprocs, congs = congs,
                  relsimps = relsimps}
    end

(* ----------------------------------------------------------------------
    maintain a global database of (named) ssfrags
   ---------------------------------------------------------------------- *)

val ssfragDB_slot : ssfrag Symtab.table Context.Data.slot =
    simpCommon.new_fragDB "simpLib.ssfragDB"
fun register_frag ssf = simpCommon.register_frag ssfragDB_slot frag_name ssf
fun lookup_named_frag n = simpCommon.lookup_named_frag ssfragDB_slot n
fun all_named_frags() = simpCommon.all_named_frags ssfragDB_slot

(*---------------------------------------------------------------------------*)
(* Operation on ssfrag values                                                *)
(*---------------------------------------------------------------------------*)

fun name_ss s (SSFRAG_CON {convs,rewrs,filter,ac,dprocs,congs,relsimps,...}) =
  SSFRAG_CON {name=SOME s, convs=convs,rewrs=rewrs,filter=filter,
              ac=ac,dprocs=dprocs,congs=congs, relsimps = relsimps};

fun rewrites rewrs =
   SSFRAG_CON {name=NONE, relsimps = [],
               convs=[],
               rewrs=map (fn th => (NONE, th)) rewrs,
               filter=NONE,ac=[],dprocs=[],congs=[]};

fun rewrites_with_names rewrs =
   SSFRAG_CON {name=NONE, relsimps=[], convs=[], rewrs = map (apfst SOME) rewrs,
               filter=NONE,ac=[],dprocs=[],congs=[]};

fun dproc_ss dproc =
   SSFRAG_CON {name=NONE, relsimps = [],
           convs=[],rewrs=[],filter=NONE,ac=[],dprocs=[dproc],congs=[]};

fun ac_ss aclist =
   SSFRAG_CON {name=NONE, relsimps = [],
           convs=[],rewrs=[],filter=NONE,ac=aclist,dprocs=[],congs=[]};

fun conv_ss conv =
   SSFRAG_CON {name=NONE, relsimps = [],rewrs=[],filter=NONE,ac=[],dprocs=[],
               convs=[{thypart = NONE, cd = conv}],congs=[]};

fun relsimp_ss rsdata =
    SSFRAG_CON {name = NONE, relsimps = [rsdata],
                convs=[],rewrs=[],filter=NONE,ac=[],dprocs=[],congs=[]};

fun D (SSFRAG_CON s) = s;
val dest_ssfrag = D
fun frag_rewrites ssf = map #2 (#rewrs (D ssf))

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
      rewrs    = flatten (map (#rewrs o D) s),
      filter   = merge_filters s,
      ac       = flatten (map (#ac o D) s),
      dprocs   = flatten (map (#dprocs o D) s),
      congs    = flatten (map (#congs o D) s),
      relsimps = flatten (map (#relsimps o D) s)
    }

fun named_rewrites name = (name_ss name) o rewrites;
fun named_rewrites_with_names name = (name_ss name) o rewrites_with_names;
fun named_merge_ss name = (name_ss name) o merge_ss;

val std_conv_ss =
    simpCommon.std_conv_ss {conv_ss = conv_ss, merge_ss = merge_ss}

fun partition_ssfrags names frags =
    simpCommon.partition_ssfrags frag_name names frags

(*---------------------------------------------------------------------------*)
(* Simpsets and basic operations on them. Simpsets contain enough            *)
(* information to spark off term traversal quickly and efficiently. In       *)
(* theory the net need not be stored (and the code would look neater if it   *)
(* wasn't), but in practice it has to be.                                    *)
(* --------------------------------------------------------------------------*)

type conv_info = {name : string,
                  conval : (term list -> term -> thm) -> term list -> conv}
type net_conv_info = {thypart : string option, ci : conv_info}
type net = net_conv_info Ho_Net.net

type weakener_data = Travrules.preorder list * thm list * Traverse.reducer


datatype history_item = ADDFRAG of ssfrag
                      | DELETE_EVENT of string list
                      | ADDWEAKENER of weakener_data

datatype simpset =
     SS of {mk_rewrs    : (controlled_thm -> controlled_thm list),
            history     : history_item list,
            initial_net : net,
            dprocs      : reducer list,
            travrules   : travrules,
            limit       : int option,
            (* Names of fragments that are forbidden from being added by ++.
               Set by `exclude_ssfrags`; cleared per-name by `force_add`. *)
            excluded    : string Binaryset.set}

val empty_excluded : string Binaryset.set = Binaryset.empty String.compare

fun ssupd_net f (SS{mk_rewrs,history,initial_net,dprocs,travrules,limit,
                    excluded}) =
    SS{mk_rewrs = mk_rewrs, history = history, initial_net = f initial_net,
       dprocs = dprocs, travrules = travrules, limit = limit,
       excluded = excluded}

 val empty_ss = SS {mk_rewrs=fn x => [x],
                    history = [], limit = NONE,
                    initial_net=empty,
                    dprocs=[],travrules=EQ_tr,
                    excluded = empty_excluded};

 fun ssfrags_of (SS x) =
     List.mapPartial (fn ADDFRAG sf => SOME sf | _ => NONE) (#history x)

fun optprint NONE = "NONE"
  | optprint (SOME s) = "SOME "^s
fun filter_net_by_patterns pats net =
    let
      val matches = simpCommon.prepare_entry_name_match pats
      fun retained ({thypart,ci}:net_conv_info) =
          not (matches thypart (#name ci))
    in Ho_Net.vfilter retained net end

fun filter_net_by_names [name] net =
    let val pat = simpCommon.munge_simpset_name name
    in
      if Portable.pointer_eq (net,Ho_Net.empty) then
        Ho_Net.vfilter (K true) net
      else filter_net_by_patterns [pat] net
    end
  | filter_net_by_names nms net =
    filter_net_by_patterns (map simpCommon.munge_simpset_name nms) net

fun filter_dprocs_by_names nms =
    simpCommon.drop_named (fn REDUCER {name,...} => name) nms

fun (ss as SS{mk_rewrs,history,initial_net,dprocs,travrules,limit,
              excluded}) -* nms =
    if null nms then ss
    else
      SS{initial_net = filter_net_by_names nms initial_net,
         history = DELETE_EVENT nms :: history, (* stored in reverse order *)
         mk_rewrs = mk_rewrs,
         dprocs = filter_dprocs_by_names nms dprocs,
         travrules = travrules,
         limit = limit,
         excluded = excluded}
fun remove_simps nms ss = ss -* nms


  (* ---------------------------------------------------------------------
   * USER_CONV keeps the conversion and its tracing in one closure per
   * installed rule.
   *
   * net_add_convs (internal function) adds conversions to the
   * initial context net.
   * ---------------------------------------------------------------------*)

 fun USER_CONV {name,key,trace,conv} =
  let val traced = simpCommon.user_conv {name=name,trace=trace}
  in fn solver => fn stack => traced (conv solver stack) end;

 val any = simpCommon.any

 fun net_add_conv {thypart,cd = data as {name,key,trace,conv}:convdata} =
     enter (option_cases #1 [] key,
            option_cases #2 any key,
            {thypart = thypart, ci = {name = name, conval = USER_CONV data}})

(* itlist is like foldr, so that theorems get added to the context starting
   from the end of the list *)
 fun net_add_convs net convs = itlist net_add_conv convs net;


 val ac_rewrites = simpCommon.ac_rewrites

 fun same_frag f1 f2 = simpCommon.same_frag frag_name f1 f2

 fun ssfrag_names_of ss = simpCommon.frag_names frag_name (ssfrags_of ss)

 fun fupdlimit f (SS{mk_rewrs,history,travrules,initial_net,dprocs,limit,
                     excluded}) =
     SS{mk_rewrs = mk_rewrs, history = history, travrules = travrules,
        initial_net = initial_net, dprocs = dprocs, limit = f limit,
        excluded = excluded}

 fun limit n = fupdlimit (fn _ => SOME n)

val unlimit = fupdlimit (fn _ => NONE)

fun getlimit (SS ss) = #limit ss

 val wk_mk_travrules = simpCommon.wk_mk_travrules

 fun add_weakener (wd as (rels,congs,dp)) simpset = let
   val SS {mk_rewrs,history,travrules,initial_net,dprocs,limit,excluded} =
       simpset
 in
   SS {mk_rewrs = mk_rewrs, history = ADDWEAKENER wd :: history,
       travrules = merge_travrules [travrules, wk_mk_travrules(rels,congs)],
       initial_net = initial_net, dprocs = dprocs @ [dp], limit = limit,
       excluded = excluded}
 end

(* ----------------------------------------------------------------------
    add_relsimp : {trans,refl,weakenings,subsets} -> simpset -> simpset
    (see simpCommon.relsimp_weakener)
   ---------------------------------------------------------------------- *)

 val rsd_reducer = simpCommon.rsd_reducer
 val rsd_travrules = simpCommon.rsd_travrules

 fun add_relsimp rsd ss = add_weakener (simpCommon.relsimp_weakener rsd) ss

 val mk_named_rewrs = simpCommon.mk_named_rewrs


 fun is_excluded (SS{excluded,...}) f =
     case frag_name f of
         SOME n => Binaryset.member(excluded, n)
       | NONE => false

 fun op++(ss as SS sset, f as SSFRAG_CON ssf) = if is_excluded ss f then ss else
   let
   val {mk_rewrs=mk_rewrs',history,travrules,initial_net,dprocs=dprocs',limit,
        excluded}= sset
   val {convs,rewrs,filter,ac,dprocs,congs,relsimps,...} = ssf
   val mk_rewrs = case filter of
                    SOME f => f oo mk_rewrs'
                  | _ => mk_rewrs'
   val crewrs = map (fn (nmopt,th) => (nmopt, dest_tagged_rewrite th)) rewrs
   val rewrs' : (thname option * controlled_thm) list =
       flatten (map (mk_named_rewrs mk_rewrs') (ac_rewrites ac @ crewrs))
   val newconvdata = convs @ List.mapPartial mk_rewr_convdata rewrs'
   val net = net_add_convs initial_net newconvdata
   (* give the existing dprocs the rewrs as additional context -
      assume the provided dprocs in the frag have already been
      primed *)
   val relreducers = map rsd_reducer relsimps
   val existing_dprocs =
       if null dprocs' then []
       else map (Traverse.addctxt (map #2 rewrs)) dprocs'
   val new_dprocs = existing_dprocs @ dprocs @ relreducers
 in
   SS {
       mk_rewrs    = mk_rewrs,
       history     = ADDFRAG f :: history,
       initial_net = net,
       limit       = limit,
       dprocs      = new_dprocs,
       excluded    = excluded,
       travrules   = simpCommon.frag_travrules
                       {travrules = travrules, congs = congs,
                        threaded_congs = [], relsimps = relsimps}
   }
 end

val mk_simpset = foldl (fn (f,ss) => ss ++ f) empty_ss

fun build_from_history h0 =
    let
      fun foldthis (hi, ss) =
          case hi of
              ADDFRAG sf => ss ++ sf
            | DELETE_EVENT sl => ss -* sl
            | ADDWEAKENER wd => add_weakener wd ss
    in
      List.foldl foldthis empty_ss (List.rev h0)
    end

fun dest_simpset (SS{history,limit,excluded,...}) =
    {history = List.rev history, limit = limit,
     excluded = Binaryset.listItems excluded}

fun setexcluded e (SS{mk_rewrs,history,initial_net,dprocs,travrules,limit,
                       excluded=_}) =
    SS{mk_rewrs=mk_rewrs, history=history, initial_net=initial_net,
       dprocs=dprocs, travrules=travrules, limit=limit, excluded=e}

val history_ops : (simpset,history_item,ssfrag) simpCommon.history_ops =
    {history = fn SS{history,...} => history,
     excluded = fn SS{excluded,...} => excluded,
     added = fn ADDFRAG f => SOME f | _ => NONE,
     frag_name = frag_name, setexcluded = setexcluded, add = op ++}

fun replay_with_limit (SS{limit,...}) h =
    build_from_history h |> fupdlimit (fn _ => limit)

fun remove_ssfrags names ss =
    simpCommon.remove_ssfrags history_ops (replay_with_limit ss) names ss

fun exclude_ssfrags names ss =
    simpCommon.exclude_ssfrags history_ops (replay_with_limit ss) names ss

fun force_add ss f = simpCommon.force_add history_ops ss f

(*---------------------------------------------------------------------------*)
(* SIMP_QCONV : simpset -> thm list -> conv                                  *)
(*---------------------------------------------------------------------------*)

 exception CONVNET of net;

 (* the rewrites a context theorem adds, in the order they are added *)
 fun context_rewrites_convdata rwts =
     List.mapPartial mk_rewr_convdata
       (map (fn th => (SOME {Thy = "", Name = "rewrite: from context"}, th))
            rwts)
 fun context_convdata mk_rewrs th =
     context_rewrites_convdata (mk_rewrs (dest_tagged_rewrite th))

 fun rewriter_with convdata (SS{mk_rewrs,travrules,initial_net,...}) = let
   fun addcontext (context,thms) = let
     val net = (raise context) handle CONVNET net => net
   in
     CONVNET
       (net_add_convs net (List.concat (map (convdata mk_rewrs) thms)))
   end
   fun apply {solver,conv,context,stack,relation} tm = let
     val net = (raise context) handle CONVNET net => net
   in
     tryfind (fn {ci = {conval,...},...} => conval solver stack tm)
             (lookup tm net)
   end
   in REDUCER {name=SOME"rewriter_for_ss",
               addcontext=addcontext, apply=apply,
               initial=CONVNET initial_net}
   end;

 fun traversedata_with convdata (ss as (SS ssdata)) =
      {rewriters=[rewriter_with convdata ss],
       dprocs= #dprocs ssdata,
       relation= boolSyntax.equality,
       travrules= #travrules ssdata,
       limit = #limit ssdata};

 val traversedata_for_ss = traversedata_with context_convdata

 fun SIMP_QCONV ss = TRAVERSE (traversedata_for_ss ss);

val Cong   = markerLib.Cong
val AC     = markerLib.AC;
val Excl   = markerLib.Excl
val ExclSF = markerLib.ExclSF
val Req0   = markerLib.mk_Req0
val ReqD   = markerLib.mk_ReqD

local open markerLib
in
val frag_of = simpCommon.frag_of lookup_named_frag

val SF = simpCommon.SF {frag_name = frag_name,
                        lookup_named_frag = lookup_named_frag,
                        register_frag = register_frag}


fun process_tags ss thl =
    simpCommon.process_tags
      {frag_of = frag_of, remove_ssfrags = remove_ssfrags, add = op ++,
       force_add = force_add,
       cong_ac = fn congs => fn acs =>
         SSFRAG_CON{name=SOME"Cong and/or AC", relsimps = [],
                    ac=acs, congs=congs,
                    convs=[],rewrs=[],filter=NONE,dprocs=[]},
       extension = NONE,
       (* ExclX is refused before any exclusion is applied. *)
       exclude = fn ss => fn excludes =>
         ss -* map (fn simpCommon.LiteralExclusion nm => nm
                     | simpCommon.ExtendedExclusion nm => nm) excludes}
      ss thl

fun SIMP_CONV ss =
    simpCommon.SIMP_CONV {process_tags = process_tags, qconv = SIMP_QCONV} ss

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

fun ASM_SIMP_TAC ss ths =
    markerLib.process_taclist_then{arg=ths} (CONV_TAC o SIMP_CONV ss)
val asm_simp_tac = ASM_SIMP_TAC
fun SIMP_TAC ss ths = ASM_SIMP_TAC ss (markerLib.NoAsms::ths)
val simp_tac = SIMP_TAC

type simptac_config = simpCommon.simptac_config

val {FULL_SIMP_TAC, REV_FULL_SIMP_TAC, NO_STRIP_FULL_SIMP_TAC,
     NO_STRIP_REV_FULL_SIMP_TAC} =
    simpCommon.full_simp_tacs {simp_rule = SIMP_RULE,
                               asm_simp_tac = ASM_SIMP_TAC}
val full_simp_tac = FULL_SIMP_TAC
val rev_full_simp_tac = REV_FULL_SIMP_TAC

val stdcon = simpCommon.stdcon

(* SIMP_RULE ss l, with the context rewrites of each assumption in l
   derived once per `rws` and reused.  They are a function of the theorem,
   and a theorem whose only hypothesis is its untagged conclusion is
   ASSUME of that conclusion, so they are kept for such theorems only,
   by conclusion, and only while process_tags leaves ss as it is.  A
   bounded rewrite counts its uses in its conversion, so rewrites are kept
   only when none of them is bounded. *)
fun simp_rule_reusing rws ss l =
    let
      fun convdata mk_rewrs th =
          let
            val t = concl th
            fun unbounded (_, UNBOUNDED) = true
              | unbounded _ = false
            fun derive () =
                let
                  val rwts = mk_rewrs (dest_tagged_rewrite th)
                  val cds = context_rewrites_convdata rwts
                in
                  if List.all unbounded rwts then
                    rws := Redblackmap.insert (!rws, t, (t, cds))
                  else ();
                  cds
                end
          in
            case (hyp th, Tag.isEmpty (Thm.tag th)) of
                ([h], true) =>
                if not (Portable.pointer_eq (h, t)) then
                  context_convdata mk_rewrs th
                else
                  (case Redblackmap.peek (!rws, t) of
                       SOME (t', cds) =>
                       if Portable.pointer_eq (t', t) then cds else derive ()
                     | NONE => derive ())
              | _ => context_convdata mk_rewrs th
          end
      fun conv tm =
          let
            val (ss', l') = process_tags ss l
            val data = if Portable.pointer_eq (ss', ss) then
                         traversedata_with convdata ss'
                       else traversedata_for_ss ss'
          in
            TRY_CONV (TRAVERSE data l') tm
          end
    in
      CONV_RULE conv
    end

(* SIMP_RULE's result depends only on the simpset, the context's assumptions
   in order and the assumption simplified, so an assumption it left
   unchanged under a context needs no second attempt under the same
   context.  `seen` records those (assumption, context) pairs, found by
   the assumption and compared by pointer, for one simpset. *)
fun psr0 (seen, rws) (cfg : simptac_config) ss =
    let
      val popper = simpCommon.popper_of cfg
      fun simp th asl =
          let
            val t = concl th
            val tried = getOpt (Redblackmap.peek (!seen, t), [])
            fun same (t', asl') =
                Portable.pointer_eq (t', t) andalso
                ListPair.allEq Portable.pointer_eq (asl', asl)
          in
            if List.exists same tried then th
            else
              let
                val th' = simp_rule_reusing rws ss (map ASSUME asl) th
              in
                if Portable.pointer_eq (concl th', t) then
                  seen := Redblackmap.insert (!seen, t, (t, asl) :: tried)
                else ();
                th'
              end
          end
    in
      popper (fn th => fn (g as (asl, _)) => stdcon cfg (simp th asl) g)
    end

fun new_memo () =
    (ref (Redblackmap.mkDict Term.compare),
     ref (Redblackmap.mkDict Term.compare))

fun psr cfg ss g = psr0 (new_memo ()) cfg ss g

fun allasms0 memo cfg ss (g as (asl,_)) =
    ntac (length asl) (psr0 memo cfg ss) g

fun allasms cfg ss g = allasms0 (new_memo ()) cfg ss g

fun global_simp_tac cfg =
    simpCommon.global_simp_tac
      {process_tags = process_tags,
       add_rewrites = fn (ss,thl) => ss ++ rewrites thl,
       allasms = fn () => allasms0 (new_memo ()),
       asm_simp_tac = ASM_SIMP_TAC}
      cfg





val track = with_tracking

(* ----------------------------------------------------------------------
    creating per-type ssdata values
   ---------------------------------------------------------------------- *)

fun tyi_to_ssdata tyinfo =
    let
      val {name, thy, convs, rewrs} = simpCommon.tyi_frag_parts tyinfo
    in
      SSFRAG_CON {name = SOME name,
                  convs = map (fn c => {thypart=SOME thy,cd = c}) convs,
                  rewrs = rewrs, filter = NONE,
                  dprocs = [], ac = [], congs = [], relsimps = []}
    end

fun type_ssfrag ty = simpCommon.type_ssfrag tyi_to_ssdata ty


(*---------------------------------------------------------------------------*)
(* Pretty printers for ssfrags and simpsets                                  *)
(*---------------------------------------------------------------------------*)

fun dest_reducer (Traverse.REDUCER x) = x;

fun dest_convdata tcd  =
    let
      val {thypart,cd={name,key,...} : convdata} = tcd
    in
      (thypart,name,Option.map #2 key)
    end

fun pp_ssfrag (SSFRAG_CON {name,convs,rewrs,ac,dprocs,congs,...}) =
    simpCommon.pp_ssfrag
      {name = name, convs = map dest_convdata convs,
       dprocs = map (#name o dest_reducer) dprocs,
       thm_blocks = [("Congruence rules",congs)], ac = ac,
       named_blocks = [("Rewrite rules",rewrs)]}

fun pp_simpset (ss as SS {initial_net,...}) =
  let
    fun foldthis {thypart, ci = {name,...}} nms = opttheory thypart name::nms
  in
    simpCommon.pp_simpset
      {net_names = Ho_Net.fold' foldthis initial_net [],
       frag_names = map frag_name (ssfrags_of ss),
       extra_sections = []}
  end

end

end (* struct *)
