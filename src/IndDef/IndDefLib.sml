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
    if mem nm ["/\\", "\\/", "!"] then
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

fun add_mono_thm th = let
  open boolLib InductiveDefinition
  val (ant, con) = dest_imp (concl th)
  val hdc_name = #1 (dest_const (#1 (strip_comb (#1 (dest_imp con)))))
in
  the_monoset := (hdc_name, th) :: (!the_monoset)
end

fun export_mono s = let
  val th = DB.fetch "-" s
  fun sps pps = (PP.add_string pps "val _ =";
                 PP.add_break pps (1,0);
                 PP.add_string pps "IndDefLib.add_mono_thm";
                 PP.add_break pps (1,0);
                 PP.add_string pps s;
                 PP.add_string pps ";";
                 PP.add_newline pps)
in
  add_mono_thm th; (* do this first so that if it fails, nothing gets added to
                      the theory *)
  adjoin_to_theory {sig_ps = NONE, struct_ps = SOME sps}
end

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
