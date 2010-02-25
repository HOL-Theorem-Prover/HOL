structure IndDefLib :> IndDefLib =
struct

local open IndDefRules in end;

open HolKernel Abbrev;

type monoset = InductiveDefinition.monoset;

val ERR = mk_HOL_ERR "IndDefLib";
val ERRloc = mk_HOL_ERRloc "IndDefLib";

local open Absyn
      fun head clause =
         let val appl = last (strip_imp (snd(strip_forall(snd(strip_tyforall clause)))))
         in fst(strip_tyapp(fst(strip_app appl)))
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
    if mem nm ["/\\", "\\/", "!", "!:"] then
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


(*---------------------------------------------------------------------------
  given a case theorem of the sort returned by new_inductive_definition
  return the name of the first new constant mentioned
  form is
        (!x y z.  (C x y z = ...)) /\
        (!u v w.  (D u v w = ...))
   in which case we return ["C", "D"]
 ---------------------------------------------------------------------------*)

fun names_from_casethm thm =
 let open HolKernel boolSyntax
     val eqns = map (#2 o strip_forall) (strip_conj (concl thm))
     val cnsts = map (#1 o strip_comb o lhs) eqns
 in
    map (#1 o dest_const) cnsts
 end;

fun Hol_mono_reln monoset tm =
 let val (rules, indn, cases) =
        InductiveDefinition.new_inductive_definition monoset tm
                  (* not! InductiveDefinition.bool_monoset tm *)
     val names = names_from_casethm cases
     val name = hd names
     val _ = save_thm(name^"_rules", rules)
     val _ = save_thm(name^"_ind", indn)
     val _ = save_thm(name^"_cases", cases)
in
  (rules, indn, cases)
end
handle e => raise (wrap_exn "IndDefLib" "Hol_mono_reln" e);

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
open LoadableThyData
val (mk,dest) = ThmSetData.new "mono"
fun onload thyname =
    case segment_data {thy = thyname, thydataty = "mono"} of
      NONE => ()
    | SOME d => let
        val thms = valOf (dest d)
      in
        the_monoset := map (fn (_,th) => (mono_name th, th)) thms @
                       !the_monoset
      end
val _ = register_onload onload
val _ = List.app onload (ancestry "-")

fun export_mono s = let
  val (data, thms) = mk [s]
  val th = #2 (hd thms)
in
  add_mono_thm th;
  write_data_update {thydataty = "mono", data = data}
end

fun thy_monos thyname =
    case segment_data {thy = thyname, thydataty = "mono"} of
      NONE => []
    | SOME d => map #2 (valOf (dest d))

(* ----------------------------------------------------------------------
    the standard entry-point
   ---------------------------------------------------------------------- *)

fun Hol_reln q =
    Hol_mono_reln (!the_monoset) (term_of q)
    handle e => Raise (wrap_exn "IndDefLib" "Hol_reln" e);

val derive_mono_strong_induction = IndDefRules.derive_mono_strong_induction;
fun derive_strong_induction (rules,ind) =
    IndDefRules.derive_mono_strong_induction (!the_monoset) (rules, ind)

end
