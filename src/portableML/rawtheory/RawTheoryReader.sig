signature RawTheoryReader =
sig

  exception TheoryReader of string
  type 'a decoder = 'a HOLsexp.decoder
  type 'a encoder = 'a HOLsexp.encoder
  type raw_theory = RawTheory_dtype.raw_theory
  type sharing_tables = RawTheory_dtype.sharing_tables
  type raw_exports = RawTheory_dtype.raw_exports
  type raw_core = {tables : sharing_tables, exports : raw_exports}
  datatype raw_type = datatype RawTheory_dtype.raw_type
  datatype raw_term = datatype RawTheory_dtype.raw_term
  type raw_thm = RawTheory_dtype.raw_thm

  val decode : raw_theory decoder

  (* auxiliaries that are possibly of independent interest *)
  val force : string -> 'a decoder -> HOLsexp.t -> 'a     (* EXN: TheoryReader *)
  val raw_type_decode : raw_type decoder
  val raw_type_encode : raw_type encoder
  val raw_term_decode : raw_term decoder
  val raw_term_encode : raw_term encoder

  val thm_decode : raw_thm decoder
  val core_decode : raw_core decoder
  val load_raw_thydata : {thyname:string,path:string} -> raw_theory

end
