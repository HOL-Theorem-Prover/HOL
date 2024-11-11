signature tailrecLib =
sig

    include Abbrev
    type thmloc = DB_dtype.thm_src_location

    val mk_sum_term : term -> hol_type -> term -> term

    val tailrec_define         : string -> term -> thm
    val gen_tailrec_define     : {loc:thmloc,name:string,def:term} -> thm
    val prove_tailrec_exists   : term -> thm

end

(* [mk_sum_term fnt inty t] generates an abstraction term c that can be an
   argument to TAILREC (or TAILCALL) such that ("roughly")

     TAILCALL c fnt x = fnt x

   The argument inty is type of the argument to fnt (x above)
*)
