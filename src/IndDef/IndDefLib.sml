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
fun term_of_absyn absyn =
  let val clauses   = strip_conj absyn
      val heads     = mk_set (map head clauses)
      val names     = map dest heads
      val resdata   = List.map (fn s => (s, Parse.hide s)) names
      fun restore() =
        List.app (fn (s,d) => Parse.update_overload_maps s d) resdata
      val tm =
        Parse.absyn_to_term (Parse.term_grammar()) absyn
        handle e => (restore(); raise e)
  in
    restore();
    tm
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

fun prim_Hol_reln monoset tm = 
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
handle e => raise (wrap_exn "IndDefLib" "prim_Hol_reln" e);


fun Hol_reln q =
    prim_Hol_reln InductiveDefinition.bool_monoset (term_of q)
    handle e => Raise (wrap_exn "IndDefLib" "Hol_reln" e);

val prim_derive_strong_induction = IndDefRules.prim_derive_strong_induction;
val derive_strong_induction = IndDefRules.derive_strong_induction;

end
