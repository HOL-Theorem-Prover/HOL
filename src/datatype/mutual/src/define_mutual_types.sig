(* ===================================================================== *)
(* FILE          : define_mutual_types.sig                               *)
(* DESCRIPTION   : Signature for the mutual recursive types parser.      *)
(*                                                                       *)
(* AUTHOR        : Peter Vincent Homeier, Univ. of Pennsylvania          *)
(* DATE          : April 23, 1998                                        *)
(* ===================================================================== *)


signature Parse_mutual_types_sig =
sig
  structure Parse_support : Parse_support_sig

  val DEFINE_MUTUAL_TYPES_ERR : {func:string,mesg:string} -> exn

  val mutual_types_spec_parser
   : Parse_support.Preterm.Term.term frag list
                    -> {type_name:string,
                        constructors: {name:string,
                                       arg_info:DefTypeInfo.type_info list
                                      } list} list
  val string_to_mutual_types_spec
   : string         -> {type_name:string,
                        constructors: {name:string,
                                       arg_info:DefTypeInfo.type_info list
                                      } list} list
end;


signature Rename_mutual_types_thms_sig =
sig
  val RENAME_EXISTS_THM : Thm.thm -> Thm.thm
  val RENAME_INDUCT_THM : Thm.thm -> Thm.thm
  val RENAME_UNIQUE_THM : Thm.thm -> Thm.thm
  val RENAME_DISTINCT_THM : Thm.thm -> Thm.thm
  val RENAME_ONE_ONE_THM : Thm.thm -> Thm.thm
  val RENAME_CASES_THM : Thm.thm -> Thm.thm
end;


signature DefineMutualTypesInputSig =
    sig
        val name : string
        val recursor_thms : Thm.thm list
        val types_spec : Term.term frag list
    end;


signature StringDefineMutualTypesInputSig =
    sig
        val name : string
        val recursor_thms : Thm.thm list
        val types_spec : string
    end;

