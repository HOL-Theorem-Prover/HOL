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

open HolKernel boolLib liteLib Trace Cond_rewr Travrules Traverse Ho_Net

structure Set = Binaryset

local open markerTheory in end;

fun ERR x      = STRUCT_ERR "simpLib" x ;
fun WRAP_ERR x = STRUCT_WRAP "simpLib" x;

fun option_cases f e (SOME x) = f x
  | option_cases f e NONE = e;

fun f oo g = fn x => flatten (map f (g x));

(*---------------------------------------------------------------------------*)
(* Representation of conversions manipulated by the simplifier.              *)
(*---------------------------------------------------------------------------*)

type convdata = {name  : string,
                 key   : (term list * term) option,
                 trace : int,
                 conv  : (term list -> term -> thm) -> term list -> conv};
type tagged_convdata = {thypart : string option, cd : convdata}
fun opttheory NONE s = s | opttheory (SOME thy) s = thy ^ "." ^ s

type stdconvdata = { name: string,
                     pats: term list,
                     conv: conv}

(*---------------------------------------------------------------------------*)
(* Make a rewrite rule into a conversion.                                    *)
(*---------------------------------------------------------------------------*)

(* boolean argument to c is whether or not the rewrite is bounded *)
fun appconv (c,UNBOUNDED) solver stk tm = c false solver stk tm
  | appconv (c,BOUNDED r) solver stk tm = if !r = 0 then failwith "exceeded rewrite bound"
                                          else c true solver stk tm before
                                            Portable.dec r

fun split_name s =
    case String.fields (equal #".") s of
        [s1,s2] => if CharVector.all Char.isDigit s2 then (NONE, s)
                   else (SOME s1, s2) (* somewhat unusual *)
      | [thypart,bname,digits] => (SOME thypart, bname ^ "." ^ digits)
      | _ => (NONE, s)

fun mk_rewr_convdata (nmopt,(thm,tag)) : tagged_convdata option = let
  val th = SPEC_ALL thm
  val (thypart,nm) =
      case Option.map split_name nmopt of
          NONE => (NONE, "rewrite:<anonymous>")
        | SOME (thypart,b) => (thypart, "rewrite:"^b)
in
  SOME {thypart = thypart,
        cd = {name  = nm,
              key   = SOME (free_varsl (hyp th), lhs(#2 (strip_imp(concl th)))),
              trace = 100, (* no need to provide extra tracing here;
                              COND_REWR_CONV provides enough tracing itself *)
              conv  = appconv (COND_REWR_CONV (nm,th), tag)}
       } before
  trace(2, LZ_TEXT(fn () => "New rewrite: " ^ thm_to_string th))
  handle HOL_ERR _ =>
         (trace (2, LZ_TEXT(fn () =>
                               thm_to_string th ^
                               " dropped (conversion to rewrite failed)"));
          NONE)
end

(*---------------------------------------------------------------------------*)
(* Composable simpset fragments                                              *)
(*---------------------------------------------------------------------------*)

type relsimpdata = {refl: thm, trans:thm, weakenings:thm list,
                    subsets : thm list, rewrs : thm list}

datatype ssfrag = SSFRAG_CON of {
    name     : string option,
    convs    : tagged_convdata list,
    rewrs    : (string option * thm) list,
    ac       : (thm * thm) list,
    filter   : (controlled_thm -> controlled_thm list) option,
    dprocs   : Traverse.reducer list,
    congs    : thm list,
    relsimps : relsimpdata list
}

fun frag_name (SSFRAG_CON {name,...}) = name

fun SSFRAG {name,convs,rewrs,ac,filter,dprocs,congs} =
  SSFRAG_CON {name = name, rewrs = rewrs, ac = ac,
              convs = map (fn c => {thypart=NONE, cd = c}) convs,
              filter = filter, dprocs = dprocs, congs = congs,
              relsimps = []}

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
fun frag_rewrites ssf = map #2 (#rewrs (D ssf))


fun merge_names list =
  itlist (fn (SOME x) =>
              (fn NONE => SOME x
                | SOME y => SOME (x^", "^y))
           | NONE =>
              (fn NONE => NONE
                | SOME y => SOME y))
         list NONE;

(*---------------------------------------------------------------------------*)
(* Possibly need to suppress duplicates in the merge?                        *)
(*---------------------------------------------------------------------------*)

fun merge_ss (s:ssfrag list) =
  SSFRAG_CON
    { name     = merge_names (map (#name o D) s),
      convs    = flatten (map (#convs o D) s),
      rewrs    = flatten (map (#rewrs o D) s),
      filter   = SOME (end_foldr (op oo) (mapfilter (the o #filter o D) s))
                 handle HOL_ERR _ => NONE,
      ac       = flatten (map (#ac o D) s),
      dprocs   = flatten (map (#dprocs o D) s),
      congs    = flatten (map (#congs o D) s),
      relsimps = flatten (map (#relsimps o D) s)
    }

fun named_rewrites name = (name_ss name) o rewrites;
fun named_rewrites_with_names name = (name_ss name) o rewrites_with_names;
fun named_merge_ss name = (name_ss name) o merge_ss;

fun std_conv_ss {name,conv,pats} =
  let
    fun cnv k = conv_ss {conv = K (K conv), trace = 2, name = name, key = k}
  in
    if null pats then
      cnv NONE
    else
      merge_ss (map (fn p => cnv (SOME([],p))) pats)
  end

fun ssfrag_name (SSFRAG_CON s) = #name s

fun partition_ssfrags names ssdata =
     List.partition
       (fn SSFRAG_CON s =>
          case #name s
          of SOME name => Lib.mem name names
           | NONE => false) ssdata

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
            limit       : int option}

fun ssupd_net f (SS{mk_rewrs,history,initial_net,dprocs,travrules,limit}) =
    SS{mk_rewrs = mk_rewrs, history = history, initial_net = f initial_net,
       dprocs = dprocs, travrules = travrules, limit = limit}

 val empty_ss = SS {mk_rewrs=fn x => [x],
                    history = [], limit = NONE,
                    initial_net=empty,
                    dprocs=[],travrules=EQ_tr};

 fun ssfrags_of (SS x) =
     List.mapPartial (fn ADDFRAG sf => SOME sf | _ => NONE) (#history x)

fun optprint NONE = "NONE"
  | optprint (SOME s) = "SOME "^s
fun name_match ({thypart,ci}:net_conv_info) (* thing in simpset's net *) pats =
    let (* true will lead to removal *)
      val ssnm = #name ci
      fun check1 (patthyopt, patbase) =
          let
            val checknamepart =
                patbase = ssnm orelse
                "rewrite:" ^ patbase = ssnm orelse
                String.isPrefix ("rewrite:" ^ patbase ^ ".") ssnm
            val checkthypart =
                case patthyopt of NONE => true | _ => patthyopt = thypart
          in
            checkthypart andalso checknamepart
          end
    in
      List.exists check1 pats
    end

fun filter_net_by_names nms net =
    let
      fun munge_pat p =
          case String.fields (equal #".") p of
              [_] => (NONE, p)
            | [s1,s2] =>
                if CharVector.all Char.isDigit s2 then (NONE, p)
                else if mem s1 (ancestry "-") then (SOME s1, s2)
                else raise ERR ("-*", "bad theory name: "^s1)
            | [s1,s2,s3] => (SOME s1, s2 ^ "." ^ s3)
            | _ => raise ERR ("-*", "User key has too many dots")
      val munged_pats = map munge_pat nms
    in
      Ho_Net.vfilter (fn nd => not (name_match nd munged_pats)) net
    end

fun (ss as SS{mk_rewrs,history,initial_net,dprocs,travrules,limit}) -* nms =
    if null nms then ss
    else
      SS{initial_net = filter_net_by_names nms initial_net,
         history = DELETE_EVENT nms :: history, (* stored in reverse order *)
         mk_rewrs = mk_rewrs,
         dprocs = dprocs,
         travrules = travrules,
         limit = limit}


  (* ---------------------------------------------------------------------
   * USER_CONV wraps a bit of tracing around a user conversion.
   *
   * net_add_convs (internal function) adds conversions to the
   * initial context net.
   * ---------------------------------------------------------------------*)

 fun USER_CONV {name,key,trace=trace_level,conv} =
  let val trace_string1 = "trying "^name^" on"
      val trace_string2 = name^" ineffectual"
      val trace_string3 = name^" left term unchanged"
      val trace_string4 = name^" raised an unusual exception (ignored)"
  in fn solver => fn stack => fn tm =>
      let val _ = trace(trace_level+2,REDUCE(trace_string1,tm))
          val thm = conv solver stack tm
      in
        trace(trace_level,PRODUCE(tm,name,thm));
        thm
      end
      handle e as HOL_ERR _ =>
             (trace (trace_level+2,TEXT trace_string2); raise e)
           | e as Conv.UNCHANGED =>
             (trace (trace_level+2,TEXT trace_string3); raise e)
           | e => (trace (trace_level, TEXT trace_string4); raise e)
  end;

 val any = mk_var("x",Type.alpha);

 fun net_add_conv {thypart,cd = data as {name,key,trace,conv}:convdata} =
     enter (option_cases #1 [] key,
            option_cases #2 any key,
            {thypart = thypart, ci = {name = name, conval = USER_CONV data}})

(* itlist is like foldr, so that theorems get added to the context starting
   from the end of the list *)
 fun net_add_convs net convs = itlist net_add_conv convs net;


 fun mk_ac p A =
   let val (a,b,c) = Drule.MK_AC_LCOMM p
       val opn = a |> concl |> strip_forall |> #2 |> lhs |> strip_comb |> #1
       val nm = let val {Name,Thy,...} = dest_thy_const opn
                in
                  "AC " ^ Thy ^ "$" ^ Name
                end handle HOL_ERR _ => "AC <some-term>"
   in (SOME nm, (a, UNBOUNDED))::(SOME nm, (b, UNBOUNDED))::
      (SOME nm, (c,UNBOUNDED))::A
   end handle HOL_ERR _ => A;

 fun ac_rewrites aclist = Lib.itlist mk_ac aclist [];

 fun same_frag (SSFRAG_CON{name=SOME n1, ...})
               (SSFRAG_CON{name=SOME n2, ...}) = n1=n2
   | same_frag other wise = false;

 fun ssfrag_names_of ss =
       ss |> ssfrags_of
          |> List.mapPartial ssfrag_name
          |> Lib.mk_set

 fun fupdlimit f (SS{mk_rewrs,history,travrules,initial_net,dprocs,limit}) =
     SS{mk_rewrs = mk_rewrs, history = history, travrules = travrules,
        initial_net = initial_net, dprocs = dprocs, limit = f limit}

 fun limit n = fupdlimit (fn _ => SOME n)

val unlimit = fupdlimit (fn _ => NONE)

fun getlimit (SS ss) = #limit ss

 fun wk_mk_travrules (rels, congs) = let
   fun cong2proc th = let
     open Opening Travrules
     fun mk_refl (x as {Rinst=rel,arg= t}) = let
       val PREORDER(_,_,refl) = find_relation rel rels
     in
       refl x
     end
   in
     CONGPROC mk_refl th
   end
 in
   TRAVRULES {relations = rels,
              congprocs = [],
              weakenprocs = map cong2proc congs}
 end

 fun add_weakener (wd as (rels,congs,dp)) simpset = let
   val SS {mk_rewrs,history,travrules,initial_net,dprocs,limit} = simpset
 in
   SS {mk_rewrs = mk_rewrs, history = ADDWEAKENER wd :: history,
       travrules = merge_travrules [travrules, wk_mk_travrules(rels,congs)],
       initial_net = initial_net, dprocs = dprocs @ [dp], limit = limit}
 end

(* ----------------------------------------------------------------------
    add_relsimp : {trans,refl,weakenings,subsets} -> simpset -> simpset

    trans and refl are the transitivity and reflexivity theorems for the
    relation.  weakenings are theorems for turning (at least) equality goals
    into goals over the new relation.  subsets are theorems that help the
    munger: they say that certain forms imply rules for the relation.  For
    example, if using RTC R as the relation, then RTC_R, which states
      !x y. R x y ==> RTC R x y
    is a good subset theorem
   ---------------------------------------------------------------------- *)

 fun dest_binop t = let
   val (fx,y) = dest_comb t
   val (f,x) = dest_comb fx
 in
   (f,x,y)
 end

 fun vperm(tm1,tm2) =
     case (dest_term tm1, dest_term tm2) of
       (VAR v1,VAR v2)   => (snd v1 = snd v2)
     | (LAMB t1,LAMB t2) => vperm(snd t1, snd t2)
     | (COMB t1,COMB t2) => vperm(fst t1,fst t2) andalso vperm(snd t1,snd t2)
     | (x,y) => aconv tm1 tm2

 fun is_var_perm(tm1,tm2) =
     vperm(tm1,tm2) andalso
     HOLset.equal(FVL [tm1] empty_tmset, FVL [tm2] empty_tmset)

 datatype munge_action = TH of thm | POP

 fun munge base subsets asms (thlistlist, n) = let
   val munge = munge base subsets
   val isbase = can (match_term base)
 in
   case thlistlist of
     [] => n
   | [] :: rest => munge asms (rest, n)
   | (TH th :: ths) :: rest => let
     in
       case CONJUNCTS (SPEC_ALL th) of
         [] => raise Fail "munge: Can't happen"
       | [th] => let
           open Net
         in
           if is_imp (concl th) then
             munge (#1 (dest_imp (concl th)) :: asms)
                   ((TH (UNDISCH th)::POP::ths)::rest, n)
           else
             case total dest_binop (concl th) of
               SOME (R,from,to) => let
                 fun foldthis (t,th) = DISCH t th
                 fun insert (t,th0) n = let
                   val (th,bound) = dest_tagged_rewrite th0
                   val looksloopy = aconv from to orelse
                                    (is_var_perm (from,to) andalso
                                     case bound of UNBOUNDED => true
                                                 | _ => false)
                 in
                   if looksloopy then n
                   else
                     Net.insert (t, (bound, List.foldl foldthis th asms)) n
                 end

               in
                 if isbase R then
                   munge asms (ths :: rest, insert (mk_comb(R,from),th) n)
                 else
                   case List.find (fn (t,_) => aconv R t) subsets of
                     NONE => munge asms (ths :: rest, n)
                   | SOME (_, sub_th) => let
                       val new_th = MATCH_MP sub_th th
                     in
                       munge asms ((TH new_th :: ths) :: rest, n)
                     end
               end
             | NONE => munge asms (ths :: rest, n)
         end
       | thlist => munge asms (map TH thlist :: ths :: rest, n)
     end
   | (POP :: ths) :: rest => munge (tl asms) (ths::rest, n)
 end

 fun po_rel (Travrules.PREORDER(r,_,_)) = r

 fun mk_reducer rel_t subsets initial_rewrites = let
   exception redExn of (control * thm) Net.net
   fun munge_subset_th th = let
     val (_, impn) = strip_forall (concl th)
     val (a, _) = dest_imp impn
     val (f, _, _) = dest_binop a
   in
     (f, th)
   end
   val subsets = map munge_subset_th subsets
   fun addcontext (ctxt, thms) = let
     val n = case ctxt of redExn n => n
                        | _ => raise ERR ("mk_reducer.addcontext",
                                          "Wrong sort of ctxt")
     val n' = munge rel_t subsets [] ([map TH thms], n)
   in
     redExn n'
   end
   val initial_ctxt = addcontext (redExn Net.empty, initial_rewrites)
   fun applythm solver t (bound, th) = let
     val _ =
         trace(7, LZ_TEXT (fn () => "Attempting rewrite: "^thm_to_string th))
     fun dec() = case bound of
                   BOUNDED r =>
                     let val n = !r in
                       if n > 0 then r := n - 1
                       else raise ERR ("mk_reducer.applythm",
                                       "Bound exceeded on rwt.")
                     end
                 | UNBOUNDED => ()
     val matched = PART_MATCH (rator o #2 o strip_imp) th t
     open Trace
     fun do_sideconds th =
         if is_imp (concl th) then let
           val (h,c) = dest_imp (concl th)
           val _ = trace(3,SIDECOND_ATTEMPT h)
           val scond = solver h
           val _ = trace(2,SIDECOND_SOLVED scond)
         in
           do_sideconds (MP th scond)
         end
       else (dec(); trace(2,REWRITING("?",t,th)); th)
   in
     do_sideconds matched
   end

   fun mk_icomb(f, x) = let
     val (f_domty, _) = dom_rng (type_of f)
     val xty = type_of x
     val theta = match_type f_domty xty
   in
     mk_comb(Term.inst theta f, x)
   end

   fun apply {solver,conv,context,stack,relation = (relation,_)} t = let
     val _ = can (match_term rel_t) relation orelse
             raise ERR ("mk_reducer.apply", "Wrong relation")
     val n = case context of redExn n => n
                           | _ => raise ERR ("apply", "Wrong sort of ctxt")
     val lookup_t = mk_icomb(relation,t)
     val _ = trace(7, LZ_TEXT(fn () => "Looking up "^term_to_string lookup_t))
     val matches = Net.match lookup_t n
     val _ = trace(7, LZ_TEXT(fn () => "Found "^Int.toString (length matches)^
                                       " matches"))
   in
     tryfind (applythm (solver stack) lookup_t) matches
   end
 in
   Traverse.REDUCER {name = SOME ("reducer for "^term_to_string rel_t),
                     addcontext = addcontext,
                     apply = apply,
                     initial = initial_ctxt}
 end

 val equality_po = let
   open Travrules
   val TRAVRULES {relations,...} = EQ_tr
 in
   hd relations
 end

 fun rsd_rel {refl,trans,weakenings,subsets,rewrs} =
     #1 (dest_binop (#2 (strip_forall (concl refl))))
 fun rsd_po {refl,trans,weakenings,subsets,rewrs} =
     Travrules.mk_preorder(trans,refl)

 fun rsd_travrules (rsd as {refl,trans,weakenings,subsets,rewrs}) =
     wk_mk_travrules([rsd_po rsd, equality_po], weakenings)

 fun rsd_reducer rsd =
     mk_reducer (rsd_rel rsd) (#subsets rsd) (#rewrs rsd)


 fun add_relsimp (rsd as {refl,trans,weakenings,subsets,rewrs}) ss = let
   val rel_t = rsd_rel rsd
   val rel_po = rsd_po rsd
   val reducer = mk_reducer rel_t subsets rewrs
 in
   add_weakener ([rel_po, equality_po], weakenings, reducer) ss
 end

 fun mk_named_rewrs mk_rewrs (nmopt, th) =
     let
       val ths = mk_rewrs th
       fun reduce s th (i,A) =
           (i + 1, (SOME (s ^ "." ^ Int.toString i), th) :: A)
     in
       case nmopt of
           NONE => map (fn th => (NONE, th)) ths
         | SOME s => (1,[]) |> Portable.foldl' (reduce s) ths |> #2 |> List.rev
     end


 fun op++(SS sset, f as SSFRAG_CON ssf) = let
   val {mk_rewrs=mk_rewrs',history,travrules,initial_net,dprocs=dprocs',limit}=
       sset
   val {convs,rewrs,filter,ac,dprocs,congs,relsimps,...} = ssf
   val mk_rewrs = case filter of
                    SOME f => f oo mk_rewrs'
                  | _ => mk_rewrs'
   val crewrs = map (fn (nmopt,th) => (nmopt, dest_tagged_rewrite th)) rewrs
   val rewrs' =
       flatten (map (mk_named_rewrs mk_rewrs') (ac_rewrites ac @ crewrs))
   val newconvdata = convs @ List.mapPartial mk_rewr_convdata rewrs'
   val net = net_add_convs initial_net newconvdata
   fun travrel (TRAVRULES{relations,...}) = relations
   val sset_rels = travrel travrules
   (* give the existing dprocs the rewrs as additional context -
      assume the provided dprocs in the frag have already been
      primed *)
   val relreducers = map rsd_reducer relsimps
   val new_dprocs = map (Traverse.addctxt (map #2 rewrs)) dprocs' @ dprocs @
                    relreducers

   val reltravs = map rsd_travrules relsimps
   val relrels = List.concat (map travrel reltravs)
   val relations = sset_rels @ relrels
 in
   SS {
       mk_rewrs    = mk_rewrs,
       history     = ADDFRAG f :: history,
       initial_net = net,
       limit       = limit,
       dprocs      = new_dprocs,
       travrules   = merge_travrules
                         (travrules::mk_travrules relations congs::reltravs)
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

fun remove_ssfrags (ss as SS{history,limit,...}) names =
    let
      val s = Set.addList (Binaryset.empty String.compare, names)
      val nil_included = Set.member(s, "")
      fun member (SSFRAG_CON{name = SOME n,...}) = Binaryset.member(s,n)
        | member (SSFRAG_CON{name = NONE,...}) = nil_included
      fun mapthis (hi as ADDFRAG f) = if member f then NONE else SOME hi
        | mapthis hi = SOME hi
      val history' = List.mapPartial mapthis history
    in
      build_from_history history' |> fupdlimit (fn _ => limit)
    end

(*---------------------------------------------------------------------------*)
(* SIMP_QCONV : simpset -> thm list -> conv                                  *)
(*---------------------------------------------------------------------------*)

 exception CONVNET of net;

 fun rewriter_for_ss (SS{mk_rewrs,travrules,initial_net,...}) = let
   fun addcontext (context,thms) = let
     val net = (raise context) handle CONVNET net => net
     val cthms = map dest_tagged_rewrite thms
     val new_rwts0 = flatten (map mk_rewrs cthms)
     val new_rwts = map (fn th => (SOME "rewrite: from context", th)) new_rwts0
   in
     CONVNET
       (net_add_convs net (List.mapPartial mk_rewr_convdata new_rwts))
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

 fun traversedata_for_ss (ss as (SS ssdata)) =
      {rewriters=[rewriter_for_ss ss],
       dprocs= #dprocs ssdata,
       relation= boolSyntax.equality,
       travrules= #travrules ssdata,
       limit = #limit ssdata};

 fun SIMP_QCONV ss = TRAVERSE (traversedata_for_ss ss);

val Cong = markerLib.Cong
val AC   = markerLib.AC;
val Excl = markerLib.Excl
val Req0 = markerLib.mk_Req0
val ReqD = markerLib.mk_ReqD

local open markerSyntax markerLib
  fun is_AC thm = same_const(fst(strip_comb(concl thm))) AC_tm
  fun is_Cong thm = same_const(fst(strip_comb(concl thm))) Cong_tm

  fun extract_excls (excls, rest) l =
      case l of
          [] => (List.rev excls, List.rev rest)
        | th::ths => case markerLib.destExcl th of
                         NONE => extract_excls (excls, th::rest) ths
                       | SOME nm => extract_excls (nm::excls, rest) ths

  fun process_tags ss thl =
    let val (Congs,rst) = Lib.partition is_Cong thl
        val (ACs,rst) = Lib.partition is_AC rst
        val (excludes, rst) = extract_excls ([],[]) rst
    in
     if null Congs andalso null ACs andalso null excludes then (ss,thl)
     else (
       ss ++ SSFRAG_CON{name=SOME"Cong and/or AC", relsimps = [],
                             ac=map unAC ACs, congs=map unCong Congs,
                             convs=[],rewrs=[],filter=NONE,dprocs=[]}
          -* excludes,
       rst
     )
    end
in
fun SIMP_CONV ss l tm =
  let val (ss', l') = process_tags ss l
  in TRY_CONV (SIMP_QCONV ss' l') tm
  end;

fun SIMP_PROVE ss l t =
  let val (ss', l') = process_tags ss l
  in EQT_ELIM (SIMP_QCONV ss' l' t)
  end;

infix &&;

fun (ss && thl) =
  let val (ss',thl') = process_tags ss thl
  in ss' ++ rewrites thl'
  end;

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

fun ASM_SIMP_RULE ss l th = SIMP_RULE ss (l@map ASSUME (hyp th)) th;

fun SIMP_TAC0 ss l = markerLib.ABBRS_THEN (CONV_TAC o SIMP_CONV ss) l;
fun SIMP_TAC ss = markerLib.mk_require_tac (SIMP_TAC0 ss)
val simp_tac = SIMP_TAC

fun ASM_SIMP_TAC0 ss =
   markerLib.ABBRS_THEN
    (fn thl => fn gl as (asl,_) =>
         SIMP_TAC ss (markerLib.LLABEL_RESOLVE thl asl) gl);
fun ASM_SIMP_TAC ss = markerLib.mk_require_tac (ASM_SIMP_TAC0 ss)
val asm_simp_tac = ASM_SIMP_TAC

local
   (* differs only in that it doesn't call OPPOSITE_TAC or DISCARD_TAC *)
   fun caa_tac th = FIRST [CONTR_TAC th, ACCEPT_TAC th, ASSUME_TAC th]
   val STRIP_ASSUME_TAC' = REPEAT_TCL STRIP_THM_THEN caa_tac
   fun drop r =
      fn n =>
         POP_ASSUM_LIST
           (fn l =>
              MAP_EVERY ASSUME_TAC
                 (Lib.with_exn (r o List.take) (l, List.length l - n)
                   (Feedback.mk_HOL_ERR "simpLib" "drop" "Bad cut off number")))
   fun GEN_FULL_SIMP_TAC (drop, r) tac =
      fn ss => fn thms =>
         let
            fun simp_asm (t, l') = SIMP_RULE ss (l' @ thms) t :: l'
            fun f asms = MAP_EVERY tac (List.foldl simp_asm [] (r asms))
                         THEN drop (List.length asms)
         in
            markerLib.ABBRS_THEN
               (fn l => ASSUM_LIST f THEN ASM_SIMP_TAC ss l) thms
         end
   val full_tac = GEN_FULL_SIMP_TAC (drop List.rev, Lib.I)
   val rev_full_tac = GEN_FULL_SIMP_TAC (drop Lib.I, List.rev)
in
   val FULL_SIMP_TAC = markerLib.mk_require_tac o full_tac STRIP_ASSUME_TAC'
   val full_simp_tac = FULL_SIMP_TAC
   val REV_FULL_SIMP_TAC =
       markerLib.mk_require_tac o rev_full_tac STRIP_ASSUME_TAC'
   val rev_full_simp_tac = REV_FULL_SIMP_TAC
   val NO_STRIP_FULL_SIMP_TAC = markerLib.mk_require_tac o full_tac caa_tac
   val NO_STRIP_REV_FULL_SIMP_TAC =
       markerLib.mk_require_tac o rev_full_tac caa_tac
end

fun track f x =
 let val _ = (used_rewrites := [])
     val res = Lib.with_flag(track_rewrites,true) f x
 in used_rewrites := rev (!used_rewrites)
  ; res
 end;

(* ----------------------------------------------------------------------
    creating per-type ssdata values
   ---------------------------------------------------------------------- *)

fun tyi_to_ssdata tyinfo =
    let
      val (thy,tyop) = TypeBasePure.ty_name_of tyinfo
      val tyname = thy ^ "$" ^ tyop
      val {rewrs = rws0, convs} = TypeBasePure.simpls_of tyinfo;
      fun reduce (th, (i,A)) =
          (i + 1, (SOME (tyname ^ " simpl. " ^ Int.toString i), th) :: A)
      val (_, rewrs) = foldl reduce (1,[]) rws0
    in
      SSFRAG_CON {name = SOME("Datatype "^tyname),
                  convs = map (fn c => {thypart=SOME thy,cd = c}) convs,
                  rewrs = rewrs, filter = NONE,
                  dprocs = [], ac = [], congs = [], relsimps = []}
    end

fun type_ssfrag ty =
    case TypeBase.fetch ty of
        NONE => raise ERR ("type_ssfrag", "No TypeBase info for type")
      | SOME tyi => tyi_to_ssdata tyi


(*---------------------------------------------------------------------------*)
(* Pretty printers for ssfrags and simpsets                                  *)
(*---------------------------------------------------------------------------*)

val CONSISTENT   = Portable.CONSISTENT
val INCONSISTENT = Portable.INCONSISTENT;

fun dest_reducer (Traverse.REDUCER x) = x;

fun merge_names list =
  itlist (fn (SOME x) =>
              (fn NONE => SOME x
                | SOME y => SOME (x^", "^y))
           | NONE =>
              (fn NONE => NONE
                | SOME y => SOME y))
         list NONE;

fun dest_convdata tcd  =
    let
      val {thypart,cd={name,key,...} : convdata} = tcd
    in
      (thypart,name,Option.map #2 key)
    end

fun pp_ssfrag (SSFRAG_CON {name,convs,rewrs,ac,dprocs,congs,...}) =
 let open Portable smpp
     val name = (case name of SOME s => s | NONE => "<anonymous>")
     val convs = map dest_convdata convs
     val dps = case merge_names (map (#name o dest_reducer) dprocs)
                of NONE => []
                 | SOME n => [n]
     val pp_term = lift (Parse.term_pp_with_delimiters Hol_pp.pp_term)
     val pp_thm = lift pp_thm
     fun pp_named_thm (nmopt, th) =
         let
           val nmstr = case nmopt of NONE => "<anon>" | SOME s => s
         in
           block CONSISTENT 0 (
             add_string ("[" ^ nmstr ^ "]") >> add_break(2,2) >> pp_thm th
           )
         end
     fun pp_thm_pair (th1,th2) =
        block CONSISTENT 0 (pp_thm th1 >> add_break(2,0) >> pp_thm th2)
     fun pp_conv_info (thypart,n,SOME tm) =
          block CONSISTENT 0 (
            add_string (opttheory thypart n ^ ", keyed on pattern") >>
            add_break(2,0) >> pp_term tm
          )
       | pp_conv_info (thypart,n,NONE) = add_string (opttheory thypart n)
     val nl2 = add_newline >> add_newline
     fun vspace l = if null l then nothing else nl2
     fun vblock(header, ob_pr, obs) =
       if null obs then nothing
       else
         block CONSISTENT 3 (
          add_string (header^":") >>
          add_newline >>
          pr_list ob_pr add_newline obs
         ) >> add_break(1,0)
 in
   block CONSISTENT 0 (
     add_string ("Simplification set fragment: "^name) >> add_newline >>
     vblock("Conversions",pp_conv_info,convs) >>
     vblock("Decision procedures",add_string,dps) >>
     vblock("Congruence rules",pp_thm,congs) >>
     vblock("AC rewrites",pp_thm_pair,ac) >>
     vblock("Rewrite rules",pp_named_thm,rewrs)
   )
 end

fun pp_simpset (ss as SS {initial_net,...}) =
  let
    open Portable smpp
    val empty_strset = Set.empty String.compare
    fun foldthis {thypart, ci = {name,...}} nms = opttheory thypart name::nms
    val keysl = Ho_Net.fold' foldthis initial_net []
    val keys = Listsort.sort String.compare keysl
    val (rewrites0,others0) = Lib.partition (String.isPrefix "rewrite:") keys
    val rewrites = map (fn s => String.extract(s, 8, NONE)) rewrites0
    val (anons, real_rewrites) = Lib.partition (equal "<anonymous>") rewrites
    val anon_string = case length anons of
                          0 => ""
                        | 1 => " (with 1 anonymous rewrite)"
                        | n => " (with " ^ Int.toString n ^
                               " anonymous rewrites)"
    val (fragname_set,anonfrag_count) =
        List.foldl (fn (ssf,(s,c)) =>
                       case ssfrag_name ssf of
                           NONE => (s,c+1)
                         | SOME n => (Set.add(s,n), c))
                   (empty_strset, 0)
                   (ssfrags_of ss)
    val rmstring = ""
    fun count n s = case n of 1 => "1" ^ s | n => Int.toString n ^ s ^ "s"
    val anon_fragstring = case anonfrag_count of
                              0 => ":"
                            | c => " (with " ^ count c " anonymous fragment" ^
                                   " [remove using name \"\"]):"
    fun titled_strlist (title, l) =
      block CONSISTENT 0 (
        add_string title >> add_break(1,3) >>
        block INCONSISTENT 0 (
          pr_list add_string (add_string "," >> add_break(1,0)) l
        )
      )
    val others = Set.listItems (Set.addList (empty_strset, others0))
  in
    block CONSISTENT 0 (
      pr_list titled_strlist (add_break(1,0)) [
        ("Included fragments"^anon_fragstring, Set.listItems fragname_set),
        ("Rewrites"^anon_string, real_rewrites),
        ("Other net names/keys:", others)
      ]
    )
  end;

val pp_ssfrag = Parse.mlower o pp_ssfrag
val pp_simpset = Parse.mlower o pp_simpset

end (* struct *)
