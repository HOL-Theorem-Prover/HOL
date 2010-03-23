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
              newrule : int option * term_grammar.grammar_rule,
              oldtok : string option}

datatype stored_data =
         RuleUpdate of urule
       | OverloadUpdate of { u : string, oldname : string option,
                             ts : term list }

(* This stored data record encodes a number of different options for
   the way in which a Unicode string can be an alternative for a
   syntactic form.

   If it's a RuleUpdate{u,term_name,newrule,oldtok} form, then u is the
   list of tokens appearing in newrule, which maps to term_name,
   and oldtok is an ASCII token of the old rule (if any).

   If it's a OverloadUpdate{u,oldname,t} then u is to be put in as an
   additional overload from u to the term t, and oldname is the ASCII
   version of u (if any)
*)

val term_table = ref ([] : stored_data list)
fun stored_data () = !term_table

fun getrule G term_name = let
  fun replace {term_name, elements, preferred, block_style, paren_style} s =
      {term_name = term_name,
       elements = map (fn (RE (TOK _)) => RE (TOK s) | x => x) elements,
       preferred = true,
       block_style = block_style,
       paren_style = paren_style}
  fun tok_of0 es =
      case es of
        [] => raise Fail "Unicode.getrule: should never happen"
      | RE (TOK s) :: _ => s
      | _ :: rest => tok_of0 rest
  fun tok_of {elements, ...} = tok_of0 elements

  fun search_rrlist f alt rrlist = let
    fun srch ({term_name = nm, preferred, elements, ...} : rule_record) =
        term_name = nm andalso preferred andalso
        length (List.filter (fn (RE (TOK _)) => true | _ => false) elements) = 1
  in
    case List.find srch rrlist of
      NONE => alt()
    | SOME r => f (r, replace r, tok_of r)
  end

  fun breplace {term_name,tok,preferred} s =
      {term_name = term_name, tok = s, preferred = false}
  fun search_bslist f alt blist = let
    fun srch {term_name = nm, preferred, tok} =
        term_name = nm andalso preferred
  in
    case List.find srch blist of
      NONE => alt()
    | SOME r => f (r, breplace r, #tok r)
  end

  fun con c (r,f,tok) = (c [r], (fn s => c [f s]), tok)
  fun addfix fopt (r,f,tok) = SOME ((fopt, r), (fn s => (fopt, f s)), tok)
  fun STD_infix' assoc (r,f,tok) = (INFIX (STD_infix([r],assoc)),
                                    (fn s => INFIX (STD_infix([f s], assoc))),
                                    tok)
  fun BinderString' (r, f, tok) =
      (PREFIX (BINDER [BinderString r]),
       (fn s => PREFIX (BINDER [BinderString (f s)])),
       tok)
  fun sing x = [x]
  fun get_rule_data rs =
      case rs of
        [] => NONE
      | (fixopt, grule) :: rest => let
        in
          case grule of
            PREFIX (BINDER blist) => let
              fun extract_bs (BinderString r) = SOME r
                | extract_bs _ = NONE
              val bslist = List.mapPartial extract_bs blist
            in
              search_bslist (addfix fixopt o BinderString')
                            (fn () => get_rule_data rest)
                            bslist
            end
          | PREFIX (STD_prefix rrlist) =>
            search_rrlist (addfix fixopt o con (PREFIX o STD_prefix))
                          (fn () => get_rule_data rest)
                          rrlist
          | SUFFIX TYPE_annotation => get_rule_data rest
          | SUFFIX (STD_suffix rrlist) =>
            search_rrlist (addfix fixopt o con (SUFFIX o STD_suffix))
                          (fn () => get_rule_data rest)
                          rrlist
          | INFIX (STD_infix (rrlist, assoc)) =>
            search_rrlist (addfix fixopt o STD_infix' assoc)
                          (fn () => get_rule_data rest)
                          rrlist
          | INFIX _ => get_rule_data rest
          | CLOSEFIX _ => get_rule_data rest
             (* only support single token overloads and a closefix form must
                involve two tokens at once *)
          | LISTRULE _ => get_rule_data rest (* likewise *)
        end
in
  get_rule_data (rules G)
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
        g0 |> clear_prefs_for term_name
           |> C add_grule r
      end
    | OverloadUpdate{u,oldname,ts} => let
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
                C prefer_form_with_tok { tok = s, term_name = term_name})
      end
    | OverloadUpdate{u,oldname,ts} => let
        fun foldthis s (t, G) = fupdate_overload_info
                                    (Overload.add_overloading (s,t))
                                    G
      in
        G |> C remove_uoverload u
          |> (case oldname of NONE => (fn x => x)
                            | SOME s => C (List.foldl (foldthis s)) ts)
      end

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
          | SOME ops => OverloadUpdate{u = u, oldname = SOME tmnm,
                                       ts = #actual_ops ops}
        end
      | SOME(r,f,s) => RuleUpdate{u = [u],term_name = tmnm, newrule = f u,
                                  oldtok = SOME s}
in
  new_action switch G sd
end

fun temp_uadd_rule switch rule G = new_action switch G (RuleUpdate rule)

fun temp_uoverload_on switch (s, t) G = let
  val oi = term_grammar.overload_info G
  val oldname =
      case Overload.oi_strip_comb oi (#2 (strip_abs t)) of
        NONE => NONE
      | SOME (f,_) => SOME (unprefix GrammarSpecials.fakeconst_special
                                     (#1 (dest_var f)))
                       handle HOL_ERR _ => NONE
in
  new_action switch G (OverloadUpdate { u = s, ts = [t], oldname = oldname })
end

datatype ThyUpdateInfo = UV of {u:string,tmnm:string}
                       | RULE of urule
                       | OVL of string * term

fun encode tui = let
  open Coding
in
  case tui of
    UV {u,tmnm} => "U" ^ StringData.encode u ^ StringData.encode tmnm
  | RULE {u,term_name,newrule = (precopt, grule),oldtok} => let
      val tn' = StringData.encode term_name
      val u' = StringData.encodel u
      val precopt' = case precopt of
                       NONE => "N"
                     | SOME i => "S" ^ IntData.encode i
      val grule' = term_grammar.grule_encode grule
      val oldtok' = case oldtok of
                      NONE => "N"
                    | SOME s => "S" ^ StringData.encode s
    in
      String.concat ["R",tn',u',precopt',grule',oldtok']
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
  fun mkrule ((((tn,u),precopt),rule),oldtok) =
      RULE {u = u, term_name = tn, newrule = (precopt, rule), oldtok = oldtok}
in
  (literal "U" >> map (fn (u,tm) => UV {u=u,tmnm=tm})
                      (StringData.reader >* StringData.reader)) ||
  (literal "R" >>
   map mkrule (StringData.reader >* many StringData.reader >*
               ((literal "N" >> return NONE) ||
                (literal "S" >> map SOME IntData.reader)) >*
               term_grammar.grule_reader >*
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
