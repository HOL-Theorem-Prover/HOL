structure GrammarSpecials :> GrammarSpecials =
struct

  val fnapp_special = "_ fnapp"
  val bracket_special = "_ bracket"
  val let_special = " _ let"
  val and_special = " _ and"
  val fakeconst_special = " _ fakeconst"

  val recsel_special = " _ record select"
  val recupd_special = " _ record update"
  val recfupd_special = " _ record fupdate"
  val recwith_special = " _ record with"
  val reccons_special = " _ record cons"
  val recnil_special = " _ record nil"
  val bigrec_subdivider_string = "brss__"


  val vs_cons_special = " _ vs cons"
  val resquan_special = " _ res quan special"

  val nat_elim_term = "nat_elim__magic"
  val fromNum_str = "_ inject_number"
  val num_injection = "&"


  val std_binder_precedence = 0

  val case_special = "case__magic"
  val case_split_special = "case_split__magic"
  val case_arrow_special = "case_arrow__magic"

  open HolKernel
  val compilefn = ref (NONE : (term -> term) option)
  val constructorsfn =
      ref (NONE : ({Thy:string,Tyop:string} -> term list) option)

  fun compile_pattern_match t =
      case !compilefn of
        NONE => raise HOL_ERR {origin_function = "compile_pattern_match",
                               origin_structure = "GrammarSpecials",
                               message = "Function not initialised"}
      | SOME f => f t
  fun type_constructors s =
      case !constructorsfn of
        NONE => raise HOL_ERR {origin_function = "type_constructors",
                               origin_structure = "GrammarSpecials",
                               message = "Function not initialised"}
      | SOME f => f s

  fun set_case_specials (cmp,cnst) = (compilefn := SOME cmp;
                                      constructorsfn := SOME cnst)

  fun case_initialised () = isSome (!compilefn)


end
