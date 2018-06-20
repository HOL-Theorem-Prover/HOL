signature TheoryReader =
sig

     val load_thydata : string -> string -> (string, Thm.thm) Redblackmap.dict

end
