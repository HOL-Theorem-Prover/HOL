(* ====================================================================== *)
(* FILE          : define_type.sig                                        *)
(* DESCRIPTION   : Signature for the (concrete) recursive type definition *)
(*                 facility. Translated from hol88.                       *)
(*                                                                        *)
(* AUTHOR        : (c) Tom Melham, University of Cambridge                *)
(* TRANSLATOR    : Konrad Slind, University of Calgary                    *)
(* DATE          : September 15, 1991                                     *)
(* =======================================================================*)


signature Define_type =
sig

  val parse_tyspec
    : Type.hol_type frag list
       -> {ty_name:string,
           clauses:{constructor:string, args:Type.hol_type option list} list
          }

  val dtype : {save_name:string,ty_name:string,
               clauses:{constructor:string,
                        args:Type.hol_type option list,
                        fixity : Parse.fixity} list}
              -> Thm.thm

  val define_type : {name:string,
                     type_spec: Type.hol_type frag list,
                     fixities : Parse.fixity list} -> Thm.thm

  val string_define_type
      : string -> string -> Parse.fixity list -> Thm.thm

end;
