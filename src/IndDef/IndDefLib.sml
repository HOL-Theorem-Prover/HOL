structure IndDefLib :> IndDefLib =
struct

local open IndDefRules in end;

open HolKernel Abbrev;

type monoset = InductiveDefinition.monoset;

val ERR = mk_HOL_ERR "IndDefLib";

local open Absyn
      fun head clause = 
         let val appl = last (strip_imp (snd(strip_forall clause)))
         in fst(strip_app appl)
         end
      fun determ M = 
          fst(Term.dest_var M handle HOL_ERR _ => Term.dest_const M)
           handle HOL_ERR _ => raise ERR "determ" "Non-atom in antiquote"
      fun dest (AQ tm) = determ tm
        | dest (IDENT s) = s
        | dest other = raise ERR "names_of.reln_names.dest" 
                                 "Unexpected structure"
in
fun term_of q = 
  let val absyn   = Parse.Absyn q
      val clauses = strip_conj absyn
      val heads   = mk_set (map head clauses)
      val names   = map dest heads
      val kcs     = Parse.known_constants()
      val  _      = List.app Parse.hide names
  in
    Parse.absyn_to_term (Parse.term_grammar()) absyn
    handle e => (Parse.set_known_constants kcs; raise e)
  end
end;


fun prim_Hol_reln monoset q =
  InductiveDefinition.new_inductive_definition monoset (term_of q)
  handle e => raise (wrap_exn "IndDefLib" "prim_Hol_reln" e);

fun Hol_reln q =
  InductiveDefinition.new_inductive_definition 
     InductiveDefinition.bool_monoset (term_of q)
  handle e => raise (wrap_exn "IndDefLib" "Hol_reln" e);

end
