signature Thry =
sig

  type thry = TypeBase.typeBase
  type term = Term.term
  type hol_type = Type.hol_type
  type thm = Thm.thm

  val match_term : thry -> term -> term 
            -> (term,term) USyntax.binding list * 
               (hol_type,hol_type) USyntax.binding list

  val match_type : thry -> hol_type -> hol_type
                     -> (hol_type,hol_type) USyntax.binding list

  val typecheck : thry -> term -> term

  val make_definition: thry -> string -> term -> thm * thry

  (* Datatype facts of various flavours *)
  val match_info: thry -> string -> {constructors:term list,
                                     case_const:term} option

  val induct_info: thry -> string -> {constructors:term list,
                                      nchotomy:thm} option

  val extract_info: thry -> {case_congs:thm list, case_rewrites:thm list}

end;
