structure fp64_machineLib :> fp64_machineLib =
struct

  val native_eval = ref false
  val () = Feedback.register_btrace ("native IEEE", native_eval)
  val sqrt_CONV = ref Conv.NO_CONV
  val add_CONV = ref Conv.NO_CONV
  val sub_CONV = ref Conv.NO_CONV
  val mul_CONV = ref Conv.NO_CONV
  val div_CONV = ref Conv.NO_CONV
  val compare_CONV = ref Conv.NO_CONV
  val eq_CONV = ref Conv.NO_CONV
  val lt_CONV = ref Conv.NO_CONV
  val le_CONV = ref Conv.NO_CONV
  val gt_CONV = ref Conv.NO_CONV
  val ge_CONV = ref Conv.NO_CONV
  fun native cnv1 s =
    let
      val cnv2 =
        Conv.QCHANGED_CONV
          (Rewrite.PURE_REWRITE_CONV [DB.fetch "machine_ieee" ("fp64_" ^  s)])
    in
      fn tm => (if !native_eval then !cnv1 else cnv2) tm
    end
  fun mk s = Term.prim_mk_const {Name = "fp64_" ^ s, Thy = "machine_ieee"}
  val () = computeLib.add_convs
    [(mk "sqrt", 2, native sqrt_CONV "sqrt"),
     (mk "add", 3, native add_CONV "add"),
     (mk "sub", 3, native sub_CONV "sub"),
     (mk "mul", 3, native mul_CONV "mul"),
     (mk "div", 3, native div_CONV "div"),
     (mk "compare", 2, native compare_CONV "compare"),
     (mk "equal", 2, native eq_CONV "equal"),
     (mk "lessThan", 2, native lt_CONV "lessThan"),
     (mk "lessEqual", 2, native le_CONV "lessEqual"),
     (mk "greaterThan", 2, native gt_CONV "greaterThan"),
     (mk "greaterEqual", 2, native ge_CONV "greaterEqual")
    ]

end
