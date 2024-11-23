structure GrammarSpecials :> GrammarSpecials =
struct

  val fnapp_special = "_ fnapp"
  val bracket_special = "_ bracket"
  val let_special = " _ let"
  val letcons_special = " _ letcons"
  val letnil_special = " _ letnil"
  val and_special = " _ and"
  val fakeconst_special = " _ fakeconst"

  fun mk_lform_name {nilstr,cons} = "ListForm<" ^ nilstr ^ "," ^ cons ^">"
  val term_name_is_lform = String.isPrefix "ListForm<"

  fun mk_fakeconst_name {original,fake} = let
    open Coding
  in
    fakeconst_special ^
    PairData.encode (StringData.encode,
                     OptionData.encode KernelNameData.encode)
                    (fake, original)
  end

  fun dest_fakeconst_name s = let
    open Coding
    val decoder =
        PairData.decode (StringData.reader,
                         OptionData.reader KernelNameData.reader)
  in
    case decoder (Lib.unprefix fakeconst_special s) of
        SOME (fake, original) => SOME{fake = fake, original = original}
      | _ => NONE
  end handle Feedback.HOL_ERR _ => NONE

  val decimal_fraction_special = "/decfrac/"

  val recsel_special = " _ record select"
  val recupd_special = " _ record update"
  val recfupd_special = " _ record fupdate"
  val recwith_special = " _ record with"
  val reccons_special = " _ record cons"
  val recnil_special = " _ record nil"
  val bigrec_subdivider_string = "brss__"
  val recd_lform_name =
      mk_lform_name{cons = reccons_special, nilstr = recnil_special}


  val vs_cons_special = " _ vs cons"
  val resquan_special = " _ res quan special"

  val nat_elim_term = "nat_elim__magic"
  val fromNum_str = "_ inject_number"
  val num_injection = "&"

  val stringinjn_base = "_ inject_string"
  fun mk_stringinjn_name s =
      let val ((_, i), _) = valOf (UTF8.getChar s)
            handle Option => raise Fail "GrammarSpecials.mk_stringinjn_name: \
                                        \empty string"
      in
        stringinjn_base ^ StringCvt.padLeft #"0" 4 (Int.fmt StringCvt.HEX i)
      end
  val std_stringinjn_name = mk_stringinjn_name "\""
  val string_elim_term = "string_elim__magic"

  val std_binder_precedence = 0


  fun mk_case_special0 nm component =
      mk_fakeconst_name {original = SOME {Thy = "case magic", Name = nm},
                         fake = component}
  val mk_default_case = mk_case_special0 "default"
  fun mk_case_special nm = mk_case_special0 nm "case"
  fun dest_case_special s =
    case dest_fakeconst_name s of
        SOME {original = SOME{Thy="case magic",Name},fake="case"} => SOME Name
      | _ => NONE
  val is_case_special = isSome o dest_case_special



  val core_case_special = mk_default_case "case"
  val case_split_special = mk_default_case "split"
  val case_arrow_special = mk_default_case "arrow"

  open HolKernel
  val compilefn = ref (NONE : (term -> term) option)
  val constructorsfn =
      ref (NONE : ({Thy:string,Tyop:string} -> term list) option)

  val ERR = mk_HOL_ERR "GrammarSpecials"

  fun compile_pattern_match t =
      case !compilefn of
        NONE => raise ERR "compile_pattern_match" "Function not initialised"
      | SOME f => f t
  fun type_constructors s =
      case !constructorsfn of
        NONE => raise ERR "type_constructors" "Function not initialised"
      | SOME f => f s

  fun set_case_specials (cmp,cnst) = (compilefn := SOME cmp;
                                      constructorsfn := SOME cnst)

  fun case_initialised () = isSome (!compilefn)


end
