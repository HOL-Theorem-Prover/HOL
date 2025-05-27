signature RawTheoryReader =
sig

  exception TheoryReader of string
  type 'a decoder = 'a HOLsexp.decoder
  type 'a encoder = 'a HOLsexp.encoder
  type raw_theory = RawTheory_dtype.raw_theory
  type sharing_tables = RawTheory_dtype.sharing_tables

  (* 'a parameters below let some sharing occur between the simplest pair of
     "unshared" and "shared" types.  The 'a can either be an int which is a
     reference into a vector of strings, or a string, meaning the original
     ints have been looked up and substituted out *)
  type 'a raw_exports = 'a RawTheory_dtype.raw_exports
  type 'a raw_core = {tables : sharing_tables, exports : 'a raw_exports}
  datatype raw_type = datatype RawTheory_dtype.raw_type
  datatype raw_term = datatype RawTheory_dtype.raw_term
  type 'a raw_thm = 'a RawTheory_dtype.raw_thm

  val decode : raw_theory decoder

  (* auxiliaries that are possibly of independent interest *)
  val force : string -> 'a decoder -> HOLsexp.t -> 'a     (* EXN: TheoryReader *)
  val raw_type_decode : raw_type decoder
  val raw_type_encode : raw_type encoder
  val raw_term_decode : raw_term decoder
  val raw_term_encode : raw_term encoder

  val thm_decode : int raw_thm decoder
  val core_decode : string raw_core decoder
  val load_raw_thydata : {thyname:string,path:string} -> raw_theory

end
