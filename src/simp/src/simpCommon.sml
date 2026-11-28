(*===========================================================================*)
(* FILE          : simpCommon.sml                                            *)
(* DESCRIPTION   : The parts of the simplifier that do not depend on the     *)
(*                 representation of fragments and simpsets, shared by       *)
(*                 simpLib and simpExtLib.                                   *)
(*                                                                           *)
(* AUTHOR        : Donald Syme (from simpLib)                                *)
(*===========================================================================*)

structure simpCommon :> simpCommon =
struct

open Abbrev

local
open Feedback Lib Term Thm boolSyntax Drule BoundedRewrites
in

type control = BoundedRewrites.control
type controlled_thm = BoundedRewrites.controlled_thm

infix oo

val trace = Trace.trace

val dest_imp = liteLib.dest_imp
val is_imp = liteLib.is_imp
val strip_imp = liteLib.strip_imp
val op |> = liteLib.|>

type thname = KernelSig.kernelname

fun ERR x = liteLib.STRUCT_ERR "simpLib" x

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
fun opttheory NONE s = s | opttheory (SOME thy) s = thy ^ "." ^ s

type stdconvdata = { name: string,
                     pats: term list,
                     conv: conv}

type relsimpdata = {refl: thm, trans:thm, weakenings:thm list,
                    subsets : thm list, rewrs : thm list}

(*---------------------------------------------------------------------------*)
(* Make a rewrite rule into a conversion.                                    *)
(*---------------------------------------------------------------------------*)

fun split_name {Thy,Name} = (SOME Thy, Name)
fun mk_rewr_convdata build (nmopt,(thm,tag)) = let
  val th = SPEC_ALL thm
  val (thypart,nm) =
      case Option.map split_name nmopt of
          NONE => (NONE, "rewrite:<anonymous>")
        | SOME (thypart,b) => (thypart, "rewrite:"^b)
in
  SOME (build {thypart = thypart, name = nm,
               key = SOME (free_varsl (hyp th),
                           lhs(#2 (strip_imp(concl th)))),
               nmopt = nmopt, th = th, tag = tag}) before
  trace(2, Trace.LZ_TEXT(fn () =>
                           "New rewrite: " ^ Hol_pp.thm_to_string th))
  handle HOL_ERR _ =>
         (trace (2, Trace.LZ_TEXT(fn () =>
                               Hol_pp.thm_to_string th ^
                               " dropped (conversion to rewrite failed)"));
          NONE)
end

(*---------------------------------------------------------------------------*)
(* Composable simpset fragments                                              *)
(*---------------------------------------------------------------------------*)

fun normCong cong_th =
  Rewrite.PURE_REWRITE_RULE [Conv.GSYM boolTheory.AND_IMP_INTRO] cong_th

(* ----------------------------------------------------------------------
    maintain a global database of (named) ssfrags
   ---------------------------------------------------------------------- *)

fun new_fragDB name : 'a Symtab.table Context.Data.slot =
    Context.Data.new {name = name, empty = Symtab.empty,
                      pp = fn _ => "<" ^ name ^ ">"}
fun fragDB slot = Context.Data.get slot (Context.snapshot())
fun register_frag slot name_of ssf =
    case name_of ssf of
        NONE => raise ERR ("register_frag", "Can only register named ssfrags")
      | SOME n =>
        (case Symtab.lookup (fragDB slot) n of
             NONE => (Context.Data.modify slot (Symtab.update(n,ssf)); ssf)
           | SOME _ => (HOL_WARNING "simpLib" "register_frag"
                                    ("Discarding existing entry for "^n);
                        Context.Data.modify slot (Symtab.update(n,ssf));
                        ssf))
fun lookup_named_frag slot n = Symtab.lookup (fragDB slot) n
fun all_named_frags slot = Symtab.keys (fragDB slot)

(*---------------------------------------------------------------------------*)
(* Operation on ssfrag values                                                *)
(*---------------------------------------------------------------------------*)

(* A singleton keeps its payload and gets a fresh option. *)
fun merge_options combine project [] = NONE
  | merge_options combine project [x] =
      (case project x of NONE => NONE | SOME y => SOME y)
  | merge_options combine project xs =
      case List.mapPartial project xs of
          [] => NONE
        | [x] => SOME x
        | xs => SOME (combine xs)

fun merge_names_by name_of xs =
    merge_options (fn names => String.concatWith ", " names) name_of xs

fun merge_filters_by filter_of xs =
    merge_options (fn filters => liteLib.end_foldr (op oo) filters) filter_of xs

val merge_names = merge_names_by I
fun merge_filters filters = merge_filters_by I filters

fun std_conv_ss {conv_ss, merge_ss} {name,conv,pats} =
  let
    fun cnv k = conv_ss {conv = K (K conv), trace = 2, name = name, key = k}
  in
    if null pats then
      cnv NONE
    else
      merge_ss (map (fn p => cnv (SOME([],p))) pats)
  end

fun same_frag name_of f1 f2 =
    case (name_of f1, name_of f2) of
        (SOME n1, SOME n2) => n1=n2
      | _ => false

(* Fragment-name sets: "" stands for the anonymous fragments *)
fun name_set_member s =
    let val nil_included = Binaryset.member(s, "")
    in
      fn SOME n => Binaryset.member(s,n)
       | NONE => nil_included
    end
fun names_member [] = K false
  | names_member [name] =
    let val anonymous = name = ""
    in fn SOME n => n = name | NONE => anonymous end
  (* These names are read repeatedly during a history scan. Sort once for
     larger batches, and use direct comparisons for short lists. *)
  | names_member (names as first::_::_::_::_) =
    if List.all (fn name => name = first) names then names_member [first]
    else
    (let
      val keys = Vector.fromList (Lib.uniq (Listsort.sort String.compare names))
      fun member key =
        let
          fun search lo hi =
            if lo >= hi then false
            else
              let val mid = lo + (hi - lo) div 2
              in
                case String.compare (key, Vector.sub (keys,mid)) of
                    LESS => search lo mid
                  | EQUAL => true
                  | GREATER => search (mid + 1) hi
              end
        in search 0 (Vector.length keys) end
      val anonymous = member ""
    in fn SOME n => member n | NONE => anonymous end
    handle Size =>
      name_set_member (Binaryset.addList (Binaryset.empty String.compare,
                                          names)))
  | names_member names =
    let val anonymous = Lib.mem "" names
    in fn SOME n => Lib.mem n names | NONE => anonymous end

fun partition_ssfrags name_of names frags =
  let
    fun at_least 0 _ = true
      | at_least _ [] = false
      | at_least n (_::rest) = at_least (n - 1) rest
  in
    case names of
        [selected] =>
          List.partition
            (fn f => case name_of f of
                         SOME name =>
                           Portable.pointer_eq (name,selected) orelse
                           name = selected
                       | NONE => false) frags
      | _ =>
          (* Sorting the names pays off only for a large enough scan. *)
          if at_least 16 names andalso at_least 64 frags then
            let val member = names_member names
            in
              List.partition
                (fn f => case name_of f of n as SOME _ => member n
                                         | NONE => false) frags
            end
          else
            List.partition
              (fn f => case name_of f of SOME name => Lib.mem name names
                                       | NONE => false) frags
  end

fun is_excluded excluded nameopt =
    case nameopt of
        SOME n => Binaryset.member(excluded, n)
      | NONE => false

fun include_name excluded nameopt =
    case nameopt of
        SOME n => (Binaryset.delete(excluded, n)
                   handle NotFound => excluded)
      | NONE => excluded

(*---------------------------------------------------------------------------*)
(* Names of the conversions in a simpset's net                               *)
(*---------------------------------------------------------------------------*)

fun entry_name_match (thypart, ssnm) pats =
    let (* true will lead to removal *)
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

fun prepare_entry_pattern (pattern as (thy,base)) =
    let
      val rewrite = "rewrite:" ^ base
      val prefix = rewrite ^ "."
      fun matches name =
          base = name orelse rewrite = name orelse String.isPrefix prefix name
    in
      case thy of
          NONE => K matches
        | SOME _ => fn thypart => if thy = thypart then matches else K false
    end
    handle Size =>
      fn thypart => fn name => entry_name_match (thypart,name) [pattern]

datatype entry_patterns =
    Pending of (string option * string) list
  | Ready of string option * string * string * string * entry_patterns ref
  | Oversized of (string option * string) list

fun prepare_entry_name_match [] = K (K false)
  | prepare_entry_name_match [pattern] = prepare_entry_pattern pattern
  | prepare_entry_name_match pats =
    let
      (* Prepare and cache each pattern only as far as a match requires. *)
      val first = ref (Pending pats)
      fun matches current thypart name =
          case !current of
              Ready (thy,base,rewrite,prefix,next) =>
                ((not (isSome thy) orelse thy = thypart) andalso
                 (base = name orelse rewrite = name orelse
                  String.isPrefix prefix name)) orelse matches next thypart name
            | Pending [] => false
            | Pending (remaining as (thy,base)::rest) =>
                let
                  val ready =
                      (let val rewrite = "rewrite:" ^ base
                       in Ready (thy,base,rewrite,rewrite ^ ".",
                                 ref (Pending rest)) end)
                      handle Size => Oversized remaining
                in
                  current := ready;
                  matches current thypart name
                end
            | Oversized remaining => entry_name_match (thypart,name) remaining
    in
      matches first
    end

fun munge_simpset_name p =
    let
      val n = String.size p
      fun next_dot i =
          if i = n orelse String.sub (p,i) = #"." then i else next_dot (i + 1)
      val first = next_dot 0
    in
      if first = n then (NONE,p)
      else
        let
          val start = first + 1
          val second = next_dot start
          fun digits i =
              i = n orelse (Char.isDigit (String.sub (p,i)) andalso
                            digits (i + 1))
        in
          if second = n then
            if digits start then (NONE,p)
            else
              let val thy = String.substring (p,0,first)
              in
                if mem thy (Theory.ancestry "-") then
                  (SOME thy,String.extract (p,start,NONE))
                else raise ERR ("-*", "bad theory name: "^thy)
              end
          else if next_dot (second + 1) = n then
            (SOME (String.substring (p,0,first)),String.extract (p,start,NONE))
          else raise ERR ("-*", "User key has too many dots")
        end
    end

(* ---------------------------------------------------------------------
 * USER_CONV wraps a bit of tracing around a user conversion: [enter]
 * before applying it, [leave] with its result and [failed] with the
 * exception it raised.
 * ---------------------------------------------------------------------*)

fun user_conv_tracing {name,trace=trace_level} =
  let val trace_string1 = "trying "^name^" on"
      val trace_string2 = name^" ineffectual"
      val trace_string3 = name^" left term unchanged"
      val trace_string4 = name^" raised an unusual exception (ignored)"
  in
    {enter = fn tm => trace(trace_level+2,Trace.REDUCE(trace_string1,tm)),
     leave = fn (tm, thm) =>
       (trace(trace_level,Trace.PRODUCE(tm,name,thm)); thm),
     failed =
       fn e as HOL_ERR _ =>
            (trace (trace_level+2,Trace.TEXT trace_string2); raise e)
        | e as Conv.UNCHANGED =>
            (trace (trace_level+2,Trace.TEXT trace_string3); raise e)
        | e => (trace (trace_level, Trace.TEXT trace_string4); raise e)}
  end

 val any = mk_var("x",Type.alpha);

 fun mk_ac p A =
   let val (a,b,c) = Drule.MK_AC_LCOMM p
       val opn = a |> concl |> strip_forall |> #2 |> lhs |> strip_comb |> #1
       val nm = let val {Name,Thy,...} = dest_thy_const opn
                in
                  SOME {Thy = Thy, Name = "AC " ^ Name}
                end handle HOL_ERR _ => NONE
   in (nm, (a, UNBOUNDED))::(nm, (b, UNBOUNDED))::(nm, (c, UNBOUNDED))::A
   end handle HOL_ERR _ => A;

 fun ac_rewrites aclist = Lib.itlist mk_ac aclist [];

 fun wk_mk_travrules (rels, congs) = let
   fun cong2proc th = let
     open Opening Travrules
     fun mk_refl (x as {Rinst=rel,arg= t}) = let
       val PREORDER(_,_,refl) = find_relation rel rels
     in
       refl x
     end
     val congproc = CONGPROC mk_refl th (* do not inline *)
   in
     (fn rel => Conv.QCHANGED_CONV o congproc rel) (* do not eta expand *)
   end
 in
   Travrules.TRAVRULES {relations = rels,
                       congprocs = [],
                       weakenprocs = map cong2proc congs}
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
                                    (Cond_rewr.is_var_perm (from,to) andalso
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
         trace(7, Trace.LZ_TEXT (fn () =>
           "Attempting rewrite: " ^ Hol_pp.thm_to_string th))
     fun dec() = case bound of
                   BOUNDED r =>
                     let val n = !r in
                       if n > 0 then r := n - 1
                       else raise ERR ("mk_reducer.applythm",
                                       "Bound exceeded on rwt.")
                     end
                 | UNBOUNDED => ()
     val matched = PART_MATCH (rator o #2 o strip_imp) th t
     fun do_sideconds th =
         if is_imp (concl th) then let
           val (h,c) = dest_imp (concl th)
           val _ = trace(3,Trace.SIDECOND_ATTEMPT h)
           val scond = solver h
           val _ = trace(2,Trace.SIDECOND_SOLVED scond)
         in
           do_sideconds (MP th scond)
         end
       else (dec(); trace(2,Trace.REWRITING("?",t,th)); th)
   in
     do_sideconds matched
   end

   fun mk_icomb(f, x) = let
     val (f_domty, _) = Type.dom_rng (type_of f)
     val xty = type_of x
     val theta = Type.match_type f_domty xty
   in
     mk_comb(Term.inst theta f, x)
   end

   fun apply {solver,conv,context,stack,relation = (relation,_)} t = let
     val _ = can (match_term rel_t) relation orelse
             raise ERR ("mk_reducer.apply", "Wrong relation")
     val n = case context of redExn n => n
                           | _ => raise ERR ("apply", "Wrong sort of ctxt")
     val lookup_t = mk_icomb(relation,t)
     val _ = trace(7, Trace.LZ_TEXT(fn () =>
                     "Looking up " ^ Hol_pp.term_to_string lookup_t))
     val matches = Net.match lookup_t n
     val _ = trace(7, Trace.LZ_TEXT(fn () =>
                     "Found "^Int.toString (length matches)^" matches"))
   in
     tryfind (applythm (solver stack) lookup_t) matches
   end
 in
   Traverse.REDUCER {name = SOME ("reducer for "^Hol_pp.term_to_string rel_t),
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

 fun relsimp_weakener (rsd as {refl,trans,weakenings,subsets,rewrs}) = let
   val rel_t = rsd_rel rsd
   val rel_po = rsd_po rsd
   val reducer = mk_reducer rel_t subsets rewrs
 in
   ([rel_po, equality_po], weakenings, reducer)
 end

 fun mk_named_rewrs mk_rewrs (nmopt, th) =
     let
       val ths = mk_rewrs th
       fun reduce {Thy,Name=s} th (i,A) =
           (i + 1, (SOME {Thy = Thy, Name = s ^ "." ^ Int.toString i}, th) :: A)
     in
       case nmopt of
           NONE => map (fn th => (NONE, th)) ths
         | SOME s => (1,[]) |> Portable.foldl' (reduce s) ths |> #2 |> List.rev
     end

(*---------------------------------------------------------------------------*)
(* Theorem-list arguments                                                    *)
(*---------------------------------------------------------------------------*)

fun frag_of lookup fragnm =
    case lookup fragnm of
        NONE => raise ERR ("process_tags", "No frag called " ^ fragnm)
      | SOME sf => sf

fun SF {frag_name, lookup_named_frag, register_frag} ssfrag =
    case frag_name ssfrag of
        NONE => raise ERR ("SF",
                           "Can't use anonymous ssfrags in thm list arguments")
      | SOME nm => ((case lookup_named_frag nm of
                         NONE => (ignore (register_frag ssfrag);
                                  HOL_WARNING "simpLib" "SF"
                                              ("Registering ssfrag " ^ nm ^
                                               "; this doesn't persist after "^
                                               "theory export!"))
                       | _ => ());
                    markerLib.FRAG nm)

fun tactic_only name =
    raise ERR ("process_tags",
               name ^ " is a tactic directive; it cannot be honoured by a " ^
               "conversion or rule")

fun SIMP_CONV {process_tags, qconv} ss l tm =
  let val (ss', l') = process_tags ss l
  in Conv.TRY_CONV (qconv ss' l') tm
  end;

fun SIMP_PROVE {process_tags, qconv} ss l t =
  let val (ss', l') = process_tags ss l
  in EQT_ELIM (qconv ss' l' t)
  end;

fun add_rewrites {process_tags, add, rewrites} (ss, thl) =
  let val (ss',thl') = process_tags ss thl
  in add (ss', rewrites thl')
  end;

fun ASM_SIMP_RULE simp_rule ss l th = simp_rule ss (l@map ASSUME (hyp th)) th;

(*---------------------------------------------------------------------------*)
(* Tactics                                                                   *)
(*---------------------------------------------------------------------------*)

(* differs from default strip_assume_tac base in that it doesn't call
   OPPOSITE_TAC or DISCARD_TAC.

   Both are reasonable omissions: OPPOSITE_TAC detects mutually
   contradictory assumptions; we'd hope that simplification will turn
   one or the other into F, which is then caught by CONTR_TAC.
   DISCARD_TAC drops duplicates. This should turn into T, which we can
   discard if droptrues is true.
*)

type simptac_config =
     {strip : bool, elimvars : bool, droptrues : bool, oldestfirst : bool}

local
open Tactical Tactic
in

(* back/front assume_tac; backp is true if the new assumption should go at the
   back of the list *)
fun BF_ASSUME_TAC backp th (g as (asl,w)) ctxt =
    if backp then ([(asl @ [concl th], w)],
                   fn resths => PROVE_HYP th (hd resths))
    else ASSUME_TAC th g ctxt

(* contr/accept/assume *)
fun caa_tac0 backp (c : simptac_config) th =
    let
      val base = FIRST [CONTR_TAC th, ACCEPT_TAC th,
                        BF_ASSUME_TAC backp th]
    in
      if #droptrues c andalso concl th ~~ boolSyntax.T then ALL_TAC
      else base
    end

fun full_simp_tacs {simp_rule, asm_simp_tac} =
let
   val caa_tac =
       caa_tac0 false {elimvars = false, droptrues = false, strip = false,
                       oldestfirst = true}
   val STRIP_ASSUME_TAC' = Thm_cont.STRIP_ALL_THEN caa_tac
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
            fun simp_asm (t, l') = simp_rule ss (l' @ thms) t :: l'
            fun f asms = MAP_EVERY tac (List.foldl simp_asm [] (r asms))
                         THEN drop (List.length asms)
         in
            markerLib.ABBRS_THEN
               (fn l => ASSUM_LIST f THEN asm_simp_tac ss l) thms
         end
   val full_tac = GEN_FULL_SIMP_TAC (drop List.rev, Lib.I)
   val rev_full_tac = GEN_FULL_SIMP_TAC (drop Lib.I, List.rev)
in
   {FULL_SIMP_TAC = markerLib.mk_require_tac o full_tac STRIP_ASSUME_TAC',
    REV_FULL_SIMP_TAC =
       markerLib.mk_require_tac o rev_full_tac STRIP_ASSUME_TAC',
    NO_STRIP_FULL_SIMP_TAC = markerLib.mk_require_tac o full_tac caa_tac,
    NO_STRIP_REV_FULL_SIMP_TAC =
       markerLib.mk_require_tac o rev_full_tac caa_tac}
end

fun stdcon (c : simptac_config) th =
    if #elimvars c andalso eliminable (concl th) then VSUBST_TAC th
    else
      (if #strip c then Thm_cont.STRIP_ALL_THEN else I)
        (caa_tac0 (not (#oldestfirst c)) c)
        th

fun global_simp_tac {prepare, allasms, asm_simp_tac} cfg ss0 =
    markerLib.mk_require_tac (
      markerLib.ABBRS_THEN (
        markerLib.LLABEL_RES_THEN (
          fn thl =>
             let
               val ss = prepare ss0 thl
               val allasms = allasms ()
             in
               rpt (CHANGED_TAC (allasms cfg ss)) THEN
               asm_simp_tac ss []
             end
        )
      )
    )

end

(* ----------------------------------------------------------------------
    creating per-type ssdata values
   ---------------------------------------------------------------------- *)

fun tyi_frag_parts tyinfo =
    let
      val (thy,tyop) = TypeBasePure.ty_name_of tyinfo
      val tyname = thy ^ "$" ^ tyop
      val {rewrs = rws0, convs} = TypeBasePure.simpls_of tyinfo;
      fun name_of th i =
          case DB.revlookup th of
              DB_dtype.Stored {Thy, Name} :: _ => {Thy = Thy, Name = Name}
            | _ => {Thy = "", Name = tyname ^ " simpl. " ^ Int.toString i}
      fun reduce (th, (i,A)) =
          (i + 1, (SOME (name_of th i), th) :: A)
      val (_, rewrs) = liteLib.foldl reduce (1,[]) rws0
    in
      {name = "Datatype "^tyname, thy = thy, convs = convs, rewrs = rewrs}
    end

fun type_ssfrag tyi_to_ssdata ty =
    case TypeBase.fetch ty of
        NONE => raise ERR ("type_ssfrag", "No TypeBase info for type")
      | SOME tyi => tyi_to_ssdata tyi

(*---------------------------------------------------------------------------*)
(* Pretty printers for ssfrags and simpsets                                  *)
(*---------------------------------------------------------------------------*)

fun pp_text s = HOLPP.add_stringsz (s,UTF8.size s)

(* Keep the outer block that Parse.mlower added to both printers. *)
fun pp_ssfrag {name, convs, dprocs, thm_blocks, ac, named_blocks} =
 let open HOLPP
     val name = (case name of SOME s => s | NONE => "<anonymous>")
     val dps = case merge_names dprocs
                of NONE => []
                 | SOME n => [n]
     val pp_term = Parse.term_pp_with_delimiters Hol_pp.pp_term
     fun pp_named_thm (nmopt, th) =
         let
           val nmstr = case nmopt of
                           NONE => "<anon>"
                         | SOME {Thy,Name} => if Thy = "" then Name
                                              else Thy ^ "$" ^ Name
         in block CONSISTENT 0
              [pp_text ("[" ^ nmstr ^ "]"), add_break (2,2), Hol_pp.pp_thm th]
         end
     fun pp_thm_pair (th1,th2) =
       block CONSISTENT 0
         [Hol_pp.pp_thm th1, add_break (2,0), Hol_pp.pp_thm th2]
     fun pp_conv_info (thypart,n,SOME tm) =
          block CONSISTENT 0
            [pp_text (opttheory thypart n ^ ", keyed on pattern"),
             add_break (2,0), pp_term tm]
       | pp_conv_info (thypart,n,NONE) = pp_text (opttheory thypart n)
     fun section pr (header,obs) =
       if null obs then []
       else
         [block CONSISTENT 3
            (pp_text (header ^ ":") :: NL :: pr_list pr [NL] obs),
          add_break (1,0)]
     fun sections pr = List.concat o map (section pr)
 in
   block CONSISTENT 0
     [block CONSISTENT 0
        (pp_text ("Simplification set fragment: " ^ name) :: NL ::
         List.concat
           [section pp_conv_info ("Conversions",convs),
            section pp_text ("Decision procedures",dps),
            sections Hol_pp.pp_thm thm_blocks,
            section pp_thm_pair ("AC rewrites",ac),
            sections pp_named_thm named_blocks])]
 end

fun pp_simpset {net_names = keysl, frag_names, extra_sections} =
  let
    open HOLPP
    val empty_strset = Binaryset.empty String.compare
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
        List.foldl (fn (nmopt,(s,c)) =>
                       case nmopt of
                           NONE => (s,c+1)
                         | SOME n => (Binaryset.add(s,n), c))
                   (empty_strset, 0)
                   frag_names
    fun count n s = case n of 1 => "1" ^ s | n => Int.toString n ^ s ^ "s"
    val anon_fragstring = case anonfrag_count of
                              0 => ":"
                            | c => " (with " ^ count c " anonymous fragment" ^
                                   " [remove using name \"\"]):"
    fun titled_strlist (title, l) =
      block CONSISTENT 0
        [pp_text title, add_break (1,3),
         block INCONSISTENT 0 (pr_list pp_text [pp_text ",",add_break (1,0)] l)]
    val others = Binaryset.listItems (Binaryset.addList (empty_strset, others0))
  in
    block CONSISTENT 0
      [block CONSISTENT 0
         (pr_list titled_strlist [add_break (1,0)]
            ([("Included fragments" ^ anon_fragstring,
               Binaryset.listItems fragname_set),
              ("Rewrites" ^ anon_string, real_rewrites),
              ("Other net names/keys:", others)] @ extra_sections))]
  end;

end

end (* struct *)
