signature Datatype =
sig

 type hol_type = Type.hol_type
 type typeBase = TypeBase.typeBase
 type tyinfo = TypeBase.tyinfo
 type 'a quotation = 'a frag list;

  (* A "pure" operation that doesn't write the underlying database of facts *)

  val primHol_datatype : typeBase -> hol_type quotation -> tyinfo

  (* An impure version *)

  val Hol_datatype : hol_type quotation -> unit

end;
