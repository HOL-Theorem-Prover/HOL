(* Lightweight pretty-printer for terms read from RawTheory .dat files
   Works purely with RawTheory data, no dependence on kernel Term/Type modules
*)

signature RawTermPP = sig

  (* Simplified term and type structures *)
  type term
  type hol_type

  (* Sharing tables from RawTheory (for resolving term references) *)
  type sharing_tables = {
    stringt : string Vector.vector,
    idt : (int * int) list,
    typet : RawTheory_dtype.raw_type list,
    termt : RawTheory_dtype.raw_term list
  }

  (* Decode a term from the write_raw format string, with access to sharing tables *)
  val decode_term : sharing_tables -> string -> term

  (* Pretty-print a term as an smpp block *)
  val pp_term : term -> (unit, unit) smpp.t

  (* Pretty-print a type as an smpp block *)
  val pp_type : hol_type -> (unit, unit) smpp.t

end

