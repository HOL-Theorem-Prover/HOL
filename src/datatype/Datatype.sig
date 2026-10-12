signature Datatype =
sig
 include Abbrev
 type tyinfo       = TypeBasePure.tyinfo
 type typeBase     = TypeBasePure.typeBase;
 type AST          = ParseDatatype.AST

 (*---------------------------------------------------------------------------*)
 (* A datatype declaration generates tyinfo data for each datatype declared,  *)
 (* stored in a TypeBase, usually TypeBase.theTypeBase.  Hol_datatype and     *)
 (* Datatype do this persistently; the other entrypoints support variations.  *)
 (*---------------------------------------------------------------------------*)

 val primHol_datatype : typeBase -> AST list -> typeBase * tyinfo list

 val astHol_datatype  : AST list -> unit
 val Hol_datatype  : hol_type quotation -> unit
 val Datatype : hol_type quotation -> unit


end
