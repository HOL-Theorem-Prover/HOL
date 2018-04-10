signature ThyDataSexp =
sig

datatype t =
         Int of int
       | String of string
       | List of t list
       | Term of Term.term
       | Type of Type.hol_type
       | Thm of Thm.thm
       | Sym of string
       | Bool of bool
       | Char of char

val uptodate : t -> bool

val new : {thydataty : string, load : {thyname : string, data : t} -> unit,
           other_tds : t * TheoryDelta.t -> t} ->
          {export : t -> unit, segment_data : {thyname : string} -> t option}

val pp_sexp : Type.hol_type PP.pprinter -> Term.term PP.pprinter ->
              Thm.thm PP.pprinter -> t PP.pprinter

end
