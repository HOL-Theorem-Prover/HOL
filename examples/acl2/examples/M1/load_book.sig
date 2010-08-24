signature load_book =

sig 

 include Abbrev

 val load_simp_fn : thm -> thm

 val get_acl2_thm : string -> thm

 val load_book : (string->unit) -> (thm->thm) -> string -> (string * thm) list list

end
