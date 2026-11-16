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

open HolKernel boolLib liteLib Trace Cond_rewr Travrules

infix oo

type thname = KernelSig.kernelname

fun ERR x = STRUCT_ERR "simpLib" x

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

fun normCong cong_th = PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] cong_th

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

fun merge_names list =
  itlist (fn (SOME x) =>
              (fn NONE => SOME x
                | SOME y => SOME (x^", "^y))
           | NONE =>
              (fn NONE => NONE
                | SOME y => SOME y))
         list NONE;

fun merge_filters filters =
    SOME (end_foldr (op oo) (mapfilter the filters))
    handle HOL_ERR _ => NONE

fun std_conv_ss {conv_ss, merge_ss} {name,conv,pats} =
  let
    fun cnv k = conv_ss {conv = K (K conv), trace = 2, name = name, key = k}
  in
    if null pats then
      cnv NONE
    else
      merge_ss (map (fn p => cnv (SOME([],p))) pats)
  end

fun partition_ssfrags name_of names ssdata =
     List.partition
       (fn f =>
          case name_of f
          of SOME name => Lib.mem name names
           | NONE => false) ssdata

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
fun names_member names =
    name_set_member (Binaryset.addList (Binaryset.empty String.compare, names))

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

fun munge_simpset_name p =
    case String.fields (equal #".") p of
        [_] => (NONE, p)
      | [s1,s2] =>
          if CharVector.all Char.isDigit s2 then (NONE, p)
          else if mem s1 (ancestry "-") then (SOME s1, s2)
          else raise ERR ("-*", "bad theory name: "^s1)
      | [s1,s2,s3] => (SOME s1, s2 ^ "." ^ s3)
      | _ => raise ERR ("-*", "User key has too many dots")

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
    {enter = fn tm => trace(trace_level+2,REDUCE(trace_string1,tm)),
     leave = fn (tm, thm) => (trace(trace_level,PRODUCE(tm,name,thm)); thm),
     failed =
       fn e as HOL_ERR _ =>
            (trace (trace_level+2,TEXT trace_string2); raise e)
        | e as Conv.UNCHANGED =>
            (trace (trace_level+2,TEXT trace_string3); raise e)
        | e => (trace (trace_level, TEXT trace_string4); raise e)}
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
     (fn rel => QCHANGED_CONV o congproc rel) (* do not eta expand *)
   end
 in
   TRAVRULES {relations = rels,
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
  in TRY_CONV (qconv ss' l') tm
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
   val STRIP_ASSUME_TAC' = STRIP_ALL_THEN caa_tac
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
      (if #strip c then STRIP_ALL_THEN else I)
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
      val (_, rewrs) = foldl reduce (1,[]) rws0
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

val CONSISTENT   = Portable.CONSISTENT
val INCONSISTENT = Portable.INCONSISTENT;

fun pp_ssfrag0 {name, convs, dprocs, thm_blocks, ac, named_blocks} =
 let open Portable smpp
     val name = (case name of SOME s => s | NONE => "<anonymous>")
     val dps = case merge_names dprocs
                of NONE => []
                 | SOME n => [n]
     val pp_term = lift (Parse.term_pp_with_delimiters Hol_pp.pp_term)
     val pp_thm = lift pp_thm
     fun pp_named_thm (nmopt, th) =
         let
           val nmstr = case nmopt of
                           NONE => "<anon>"
                         | SOME {Thy,Name} => if Thy = "" then Name
                                              else Thy ^ "$" ^ Name
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
     fun vblocks pr = List.foldl (fn ((h,obs),p) => p >> vblock(h,pr,obs))
                                 nothing
 in
   block CONSISTENT 0 (
     add_string ("Simplification set fragment: "^name) >> add_newline >>
     vblock("Conversions",pp_conv_info,convs) >>
     vblock("Decision procedures",add_string,dps) >>
     vblocks pp_thm thm_blocks >>
     vblock("AC rewrites",pp_thm_pair,ac) >>
     vblocks pp_named_thm named_blocks
   )
 end

fun pp_simpset0 {net_names = keysl, frag_names, extra_sections} =
  let
    open Portable smpp
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
    val others = Binaryset.listItems (Binaryset.addList (empty_strset, others0))
  in
    block CONSISTENT 0 (
      pr_list titled_strlist (add_break(1,0)) ([
        ("Included fragments"^anon_fragstring,
         Binaryset.listItems fragname_set),
        ("Rewrites"^anon_string, real_rewrites),
        ("Other net names/keys:", others)
      ] @ extra_sections)
    )
  end;

val pp_ssfrag = Parse.mlower o pp_ssfrag0
val pp_simpset = Parse.mlower o pp_simpset0

end (* struct *)
