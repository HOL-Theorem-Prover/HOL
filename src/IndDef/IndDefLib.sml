structure IndDefLib :> IndDefLib =
struct

local open IndDefRules in end;

open HolKernel Abbrev;

type monoset = InductiveDefinition.monoset;

val ERR = mk_HOL_ERR "IndDefLib";
val ERRloc = mk_HOL_ERRloc "IndDefLib";

local open Absyn
      fun head clause =
         let val appl = last (strip_imp (snd(strip_forall clause)))
         in fst(strip_app appl)
         end
      fun determ M =
          fst(Term.dest_var M handle HOL_ERR _ => Term.dest_const M)
           handle HOL_ERR _ => raise ERR "determ" "Non-atom in antiquote"
      fun dest (AQ (_,tm)) = determ tm
        | dest (IDENT (_,s)) = s
        | dest other = raise ERRloc "names_of.reln_names.dest"
                                    (locn_of_absyn other) "Unexpected structure"
in
fun term_of_absyn absyn = let
  val clauses   = strip_conj absyn
  fun checkcl a = let
    val nm = dest (head a)
  in
    if mem nm ["/\\", "\\/", "!", "?", UnicodeChars.conj,
               UnicodeChars.disj, UnicodeChars.forall, UnicodeChars.exists]
    then
      raise ERRloc "term_of_absyn" (locn_of_absyn a)
                   ("Abstract syntax looks to be trying to redefine "^nm^". "^
                     "This is probably an error.\nIf you must, define with \
                     \another name and use overload_on")
    else nm
  end
  val names     = mk_set (map checkcl clauses)
  val resdata   = List.map (fn s => (s, Parse.hide s)) names
  fun restore() =
      List.app (fn (s,d) => Parse.update_overload_maps s d) resdata
  val tm =
      Parse.absyn_to_term (Parse.term_grammar()) absyn
      handle e => (restore(); raise e)
in
  restore();
  (tm, map locn_of_absyn clauses)
end

fun term_of q = term_of_absyn (Parse.Absyn q)

end;

(* ----------------------------------------------------------------------
    Store all rule inductions
   ---------------------------------------------------------------------- *)

val term_rule_map : ({Name:string,Thy:string},thm list)Binarymap.dict ref =
    ref (Binarymap.mkDict KernelSig.name_compare)

fun listdict_add (d, k, e) =
    case Binarymap.peek(d, k) of
      NONE => Binarymap.insert(d,k,[e])
    | SOME l => Binarymap.insert(d,k,e::l)

fun rule_induction_map() = !term_rule_map

fun ind_thm_to_consts thm = let
  open boolSyntax
  val c = concl thm
  val (_, bod) = strip_forall c
  val (_, con) = dest_imp bod
  val cons = strip_conj con
  fun to_kname {Name,Thy,...} = {Name = Name, Thy = Thy}
in
  map (fn t => t |> strip_forall |> #2 |> dest_imp |> #1 |> strip_comb |> #1
                 |> dest_thy_const |> to_kname)
      cons
end

fun add_rule_induction th = let
  val nm = current_theory()
  val ts = ind_thm_to_consts th
in
  term_rule_map := List.foldl (fn (t,d) => listdict_add(d,t,th))
                              (!term_rule_map)
                              ts
end

(* making it exportable *)
val {export = export_rule_induction, dest, ...} =
    ThmSetData.new_exporter "rule_induction" (K (app add_rule_induction))

fun thy_rule_inductions thyname = let
  val segdata =
    LoadableThyData.segment_data {thy = thyname, thydataty = "rule_induction"}
in
  case segdata of
    NONE => []
  | SOME d => map #2 (valOf (dest d))
end

(* ----------------------------------------------------------------------
    the built-in monoset, that users can update as they prove new
    monotonicity results about their constants
   ---------------------------------------------------------------------- *)

val the_monoset = ref InductiveDefinition.bool_monoset

fun mono_name th = let
  open boolLib
  val (_, con) = dest_imp (concl th)
in
  #1 (dest_const (#1 (strip_comb (#1 (dest_imp con)))))
end

fun add_mono_thm th = the_monoset := (mono_name th, th) :: (!the_monoset)

(* making it exportable *)
val {export = export_mono, dest, ...} =
    ThmSetData.new_exporter "mono" (K (app add_mono_thm))

fun thy_monos thyname =
    case LoadableThyData.segment_data {thy = thyname, thydataty = "mono"} of
      NONE => []
    | SOME d => map #2 (valOf (dest d))

(*---------------------------------------------------------------------------
  given a case theorem of the sort returned by new_inductive_definition
  return the name of the first new constant mentioned
  form is
        (!x y z.  (C x y z = ...)) /\
        (!u v w.  (D u v w = ...))
   in which case we return ["C", "D"]
 ---------------------------------------------------------------------------*)

open InductiveDefinition

fun names_from_casethm thm = let
  open HolKernel boolSyntax
  val forallbod = #2 o strip_forall
  val eqns = thm |> concl |> forallbod |> strip_conj |> map forallbod
  val cnsts = map (#1 o strip_comb o lhs) eqns
in
  map (#1 o dest_const) cnsts
end

val derive_mono_strong_induction = IndDefRules.derive_mono_strong_induction;
fun derive_strong_induction (rules,ind) =
    IndDefRules.derive_mono_strong_induction (!the_monoset) (rules, ind)

fun save_theorems name (rules, indn, strong_ind, cases) = let
in
  save_thm(name^"_rules", rules);
  save_thm(name^"_ind", indn);
  save_thm(name^"_strongind", strong_ind);
  save_thm(name^"_cases", cases);
  export_rule_induction (name ^ "_strongind")
end

fun Hol_mono_reln name monoset tm = let
  val _ = Lexis.ok_sml_identifier (name ^ !boolLib.def_suffix) orelse
          raise ERR "Hol_mono_reln"
                    ("Bad name for definition: "^ Lib.mlquote name^
                     " (use xHol_reln to specify a better)")
  val (rules, indn, cases) = new_inductive_definition monoset name tm
      (* not! InductiveDefinition.bool_monoset tm *)
  val strong_ind = derive_strong_induction (rules, indn)
in
  save_theorems name (rules, indn, strong_ind, cases);
  (rules, indn, cases)
end
handle e => raise (wrap_exn "IndDefLib" "Hol_mono_reln" e);


(* ----------------------------------------------------------------------
    the standard entry-points
   ---------------------------------------------------------------------- *)

fun xHol_reln name q = Hol_mono_reln name (!the_monoset) (term_of q)

fun name_from_def t = let
  open boolSyntax
  val cs = strip_conj t
in
  hd cs |> strip_forall |> #2 |> strip_imp |> #2 |> strip_comb |> #1 |>
  dest_var |> #1
end

fun Hol_reln q = let
  val parse = term_of |> trace ("syntax_error", 0)
                      |> trace ("show_typecheck_errors", 0)
              (* turn off verbiage because the Raise below will redisplay any
                 exceptions *)
  val def as (def_t,_) = parse q
  val name = name_from_def def_t
in
  Hol_mono_reln name (!the_monoset) def
end handle e => Raise (wrap_exn "IndDefLib" "Hol_reln" e);

end
