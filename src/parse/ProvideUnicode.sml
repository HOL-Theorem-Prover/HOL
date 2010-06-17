structure ProvideUnicode :> ProvideUnicode =
struct

structure UChar = UnicodeChars

open HolKernel Feedback

open term_grammar

type term = Term.term
type gopns = {prefer_form_with_tok : {term_name:string, tok:string} -> unit,
              setG : grammar -> unit,
              overload_on : (string * term) -> unit,
              remove_termtok : {term_name:string,tok:string} -> unit,
              master_unicode_switch : bool}
type urule = {u:string list, term_name : string,
              newrule : term_grammar.user_delta,
              oldtok : string option}

datatype stored_data =
         RuleUpdate of urule
       | OverloadUpdate of { u : string, ts : term list }

(* This stored data record encodes a number of different options for
   the way in which a Unicode string can be an alternative for a
   syntactic form.

   If it's a RuleUpdate{u,term_name,newrule,oldtok} form, then u is the
   list of tokens appearing in newrule, which maps to term_name,
   and oldtok is an ASCII token of the old rule (if any).

   If it's a OverloadUpdate{u,ts} then u is to be put in as an
   additional overload from u to the terms ts.
*)

val term_table = ref ([] : stored_data list)
fun stored_data () = !term_table

fun getrule G term_name = let
  fun tok_of0 es =
      case es of
        [] => raise Fail "Unicode.getrule: should never happen"
      | RE (TOK s) :: _ => s
      | _ :: rest => tok_of0 rest
  fun tok_of {elements, ...} = tok_of0 elements

  fun rreplace rf {term_name,paren_style,elements,timestamp,block_style} s =
      GRULE {term_name=term_name, paren_style = paren_style,
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

  fun breplace s = BRULE {term_name = term_name, tok = s}
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
            search_rrlist (TruePrefix (valOf fixopt)) tf_opt
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
          | LISTRULE _ => get_rule_data tf_opt rest (* likewise *)
        end
in
  get_rule_data NONE (rules G)
end


fun constid t = let
  val {Name,Thy,Ty} = dest_thy_const t
in
  {Name = Name, Thy = Thy}
end

fun mktemp_resb s = "_" ^ s ^ "resb"

fun enable_one g0 sd =
    case sd of
      RuleUpdate {u,term_name,newrule = r,oldtok} => let
        open term_grammar
      in
        g0 |> add_delta r
      end
    | OverloadUpdate{u,ts} => let
        fun foldthis (t,g) =
            fupdate_overload_info (Overload.add_overloading(u,t)) g
      in
        List.foldl foldthis g0 ts
      end

fun fupd_restrs f {type_intro,lambda,endbinding,restr_binders,res_quanop} =
    {type_intro = type_intro, lambda = lambda, endbinding = endbinding,
     restr_binders = f restr_binders, res_quanop = res_quanop}

fun remove_uoverload G s =
    #1 (term_grammar.mfupdate_overload_info
            (Overload.remove_overloaded_form s)
            G)


fun disable_one G sd =
    case sd of
      RuleUpdate{u,term_name,newrule,oldtok} => let
      in
        G |> remove_form_with_toklist {toklist = u, term_name = term_name}
          |> (case oldtok of
                NONE => (fn g => g)
              | SOME s =>
                prefer_form_with_tok { tok = s, term_name = term_name})
      end
    | OverloadUpdate{u,ts} => remove_uoverload G u

fun new_action switch G a =
  (if switch then enable_one G a else G) before
  term_table := a :: !term_table

fun temp_unicode_version switch {u,tmnm} G = let
  val oi = term_grammar.overload_info G
  val sd =
      case getrule G tmnm of
        NONE => let
        in
          case Overload.info_for_name oi tmnm of
            NONE => raise mk_HOL_ERR "Unicode" "unicode_version"
                                     ("No data for term with name "^tmnm)
          | SOME ops => OverloadUpdate{u = u, ts = #actual_ops ops}
        end
      | SOME(f,s) => RuleUpdate{u = [u],term_name = tmnm, newrule = f u,
                                oldtok = SOME s}
in
  new_action switch G sd
end

fun temp_uadd_rule switch rule G = new_action switch G (RuleUpdate rule)

fun temp_uoverload_on switch (s, t) G =
    new_action switch G (OverloadUpdate { u = s, ts = [t]})

datatype ThyUpdateInfo = UV of {u:string,tmnm:string}
                       | RULE of urule
                       | OVL of string * term

fun encode tui = let
  open Coding
in
  case tui of
    UV {u,tmnm} => "U" ^ StringData.encode u ^ StringData.encode tmnm
  | RULE {u,term_name,newrule,oldtok} => let
      val tn' = StringData.encode term_name
      val u' = StringData.encodel u
      val delta' = user_delta_encode newrule
      val oldtok' = case oldtok of
                      NONE => "N"
                    | SOME s => "S" ^ StringData.encode s
    in
      String.concat ["R",tn',u',delta',oldtok']
    end
  | OVL (s,tm) => let
      val s' = StringData.encode s
      val tm' = TermCoding.encode tm
    in
      String.concat ["O",s',tm']
    end
end

val reader = let
  open Coding
  infix >> >- >-> >* ||
  fun mkrule (((tn,u),delta),oldtok) =
      RULE {u = u, term_name = tn, newrule = delta, oldtok = oldtok}
in
  (literal "U" >> map (fn (u,tm) => UV {u=u,tmnm=tm})
                      (StringData.reader >* StringData.reader)) ||
  (literal "R" >>
   map mkrule (StringData.reader >* many StringData.reader >*
               term_grammar.user_delta_reader >*
               ((literal "N" >> return NONE) ||
                (literal "S" >> map SOME StringData.reader)))) ||
  (literal "O" >> map OVL (StringData.reader >* TermCoding.reader))
end

val decode = Coding.lift reader

open LoadableThyData
val (mk,dest) =
    new {merge = op@, read = Coding.lift (Coding.many reader),
         write = String.concat o map encode, thydataty = "unicodedata"}

fun update value =
    write_data_update {data= mk[value], thydataty = "unicodedata"}

fun unicode_version switch p G = let
in
    temp_unicode_version switch p G before
    update (UV p)
end

fun uadd_rule switch rule G = let
in
  temp_uadd_rule switch rule G before
  update (RULE rule)

end

fun uoverload_on switch st G = let
in
  temp_uoverload_on switch st G before
  update (OVL st)
end


fun enable_all G = List.foldl (fn (a,G) => enable_one G a)
                              G
                              (List.rev (!term_table))
fun disable_all G = List.foldl (fn (a,G) => disable_one G a) G (!term_table)

fun apply_thydata switch thyname G = let
  fun apply1 (up,G) =
      case up of
        UV p => temp_unicode_version switch p G
      | RULE r => temp_uadd_rule switch r G
      | OVL st => temp_uoverload_on switch st G
in
  case segment_data {thy = thyname, thydataty = "unicodedata"} of
    NONE => G
  | SOME data => let
    in
      case dest data of
        NONE => (Feedback.HOL_WARNING "Parse.Unicode" "apply_thydata"
                                      ("Couldn't decode data for theory \""^
                                       String.toString thyname^ "\"");
                 G)
      | SOME l => List.foldl apply1 G l
    end
end



end (* struct *)
