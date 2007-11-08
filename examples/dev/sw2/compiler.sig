signature compiler = 
sig
  include Abbrev
  (* val style : arm_code_format ref *)
  val f_compile : thm list -> ((thm * thm) list, thm list * thm list) Lib.verdict
  val b_compile :  ((thm * thm) list, 'c) Lib.verdict -> ((thm * thm) list, 'c) Lib.verdict
  val pp_compile : thm list -> ((thm * thm) list, thm list * thm list) Lib.verdict
end
