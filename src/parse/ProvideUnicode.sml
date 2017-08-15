structure ProvideUnicode :> ProvideUnicode =
struct

open HolKernel Feedback

open term_grammar

type term = Term.term

datatype uni_version =
         RuleUpdate of {newrule : term_grammar.grule}
       | OverloadUpdate of { u : string, ts : term list }

(* This uni_version type encodes a number of different options for
   the way in which a Unicode string can be an alternative for a
   syntactic form.

   If it's a RuleUpdate{u,term_name,newrule,oldtok} form, then u is the
   list of tokens appearing in newrule, which maps to term_name,
   and oldtok is an ASCII token of the old rule (if any).

   If it's a OverloadUpdate{u,ts} then u is to be put in as an
   additional overload from u to the terms ts.
*)

fun getrule G term_name = let
  fun tok_of0 es =
      case es of
        [] => raise Fail "Unicode.getrule: should never happen"
      | RE (TOK s) :: _ => s
      | _ :: rest => tok_of0 rest
  fun tok_of {elements, ...} = tok_of0 elements

  fun rreplace rf {term_name,paren_style,elements,timestamp,block_style} s =
      {term_name=term_name, paren_style = paren_style,
       pp_elements = map (fn (RE (TOK _)) => RE (TOK s) | x => x)
                         elements,
       block_style = block_style,
       fixity = rf}
  fun search_rrlist rf tfopt k (rrlist : rule_record list) =
      case rrlist of
        [] => k tfopt
      | r :: rest => let
        in
          if #term_name r = term_name then let
              val tfopt' =
                  case tfopt of
                    NONE => SOME(#timestamp r, (rreplace rf r, tok_of r))
                  | SOME (t', _) =>
                    if #timestamp r > t' then
                      SOME(#timestamp r, (rreplace rf r, tok_of r))
                    else tfopt
            in
              search_rrlist rf tfopt' k rest
            end
          else search_rrlist rf tfopt k rest
        end

  fun breplace s = binder_grule {term_name = term_name, tok = s}
  fun search_bslist tfopt k blist =
      case blist of
        [] => k tfopt
      | LAMBDA :: rest => search_bslist tfopt k rest
      | BinderString {timestamp, term_name = nm, tok} :: rest =>
        if nm = term_name then let
            val tfopt' =
                case tfopt of
                  NONE => SOME (timestamp, (breplace, tok))
                | SOME (t', _) => if timestamp > t' then
                                    SOME (timestamp, (breplace, tok))
                                  else tfopt
          in
            search_bslist tfopt' k rest
          end
        else search_bslist tfopt k rest

  fun get_rule_data tf_opt  rs =
      case rs of
        [] => Option.map #2 tf_opt
      | (fixopt, grule) :: rest => let
        in
          case grule of
            PREFIX (BINDER blist) => let
            in
              search_bslist tf_opt
                            (fn tfopt => get_rule_data tfopt rest)
                            blist
            end
          | PREFIX (STD_prefix rrlist) =>
            search_rrlist (Prefix (valOf fixopt)) tf_opt
                          (fn tfopt => get_rule_data tfopt rest)
                          rrlist
          | SUFFIX TYPE_annotation => get_rule_data tf_opt rest
          | SUFFIX (STD_suffix rrlist) =>
            search_rrlist (Suffix (valOf fixopt)) tf_opt
                          (fn tfopt => get_rule_data tfopt rest)
                          rrlist
          | INFIX (STD_infix (rrlist, assoc)) =>
            search_rrlist (Infix(assoc, valOf fixopt)) tf_opt
                          (fn tfopt => get_rule_data tfopt rest)
                          rrlist
          | INFIX _ => get_rule_data tf_opt rest
          | CLOSEFIX _ => get_rule_data tf_opt rest
             (* only support single token overloads and a closefix form must
                involve two tokens at once *)
        end
in
  get_rule_data NONE (rules G)
end

fun sd_to_deltas sd =
  case sd of
      RuleUpdate {newrule = r} => [GRULE r]
    | OverloadUpdate{u,ts} => map (fn t => OVERLOAD_ON(u,t)) ts

fun mk_unicode_version {u,tmnm} G = let
  val oi = term_grammar.overload_info G
  val sd =
      case getrule G tmnm of
        NONE => let
        in
          case Overload.info_for_name oi tmnm of
            NONE => raise mk_HOL_ERR "Unicode" "mk_unicode_version"
                                     ("No data for term with name "^tmnm)
          | SOME ops => OverloadUpdate{u = u, ts = #actual_ops ops}
        end
      | SOME(f,s) => RuleUpdate{newrule = f u}
in
  sd_to_deltas sd
end

end (* struct *)
