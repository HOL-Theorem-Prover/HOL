open HolKernel Parse boolLib bossLib
open binary_ieeeLib binary_ieeeSyntax
open testutils

fun printn s = print (s ^ "\n")
fun die s = ( printn s; raise ERR "" "" )
val die = printn

val () = show_tags := true

(* ------------------------------------------------------------------------ *)

fun time_to_minutes e =
   let
      val s = Time.toSeconds e
      val minutes = Int.quot (s, 60);
      val seconds = Int.rem (s, 60);
   in
      Int.toString minutes ^ "m " ^
      StringCvt.padLeft #"0" 2 (Int.toString seconds) ^ "s"
   end

local
   val s_t = ``1w:word1``
   val s_f = ``0w:word1``
   fun s_tf b = if b then s_t else s_f
in
   fun float_constants ty =
      let
         val p as (t, w) = dest_float_ty ty
         val itself = boolSyntax.mk_itself (pairSyntax.mk_prod p)
         fun mk_lit (s, e, f) =
            mk_floating_point
              (s_tf s, wordsSyntax.mk_n2w (numLib.term_of_int e, w),
               wordsSyntax.mk_n2w (numLib.term_of_int f, t))
      in
         List.map (fn f => f itself)
            [mk_float_some_nan, mk_float_plus_zero, mk_float_minus_zero,
             mk_float_plus_min, mk_float_top, mk_float_bottom,
             mk_float_plus_infinity, mk_float_minus_infinity] @
         List.map mk_lit
            [(false, 512, 0),
             (false, 12, 123456)]
      end
end

val round_constants =
   [roundTiesToEven_tm, roundTowardPositive_tm, roundTowardNegative_tm,
    roundTowardZero_tm]

val round_constants =
   [roundTiesToEven_tm, roundTowardZero_tm]

fun lcf_eval tm = Feedback.trace ("native ieee", 0) EVAL tm
fun native_eval tm = Feedback.trace ("native ieee", 2) EVAL tm

fun has_tags tags thm =
   case Tag.dest_tag (Thm.tag thm) of
      (ts, []) => Lib.set_eq ts tags
    | _ => false

fun pr_term tm =
   ( print "\n"; Lib.with_flag (show_types, true) print_term tm; print "\n" )

fun ok_result1 tm =
   tm = boolSyntax.T orelse
   tm = boolSyntax.F orelse
   tm = nan_tm orelse
   tm = infinity_tm orelse
   (case Lib.total dest_float tm of
       SOME r => is_ground_real r
     | NONE => false) orelse
   is_ground_real tm

fun ok_result2 tm =
   is_float_plus_infinity tm orelse
   is_float_minus_infinity tm orelse
   is_float_some_nan tm orelse
   Lib.can dest_floating_point tm

fun ok_order_result tm =
   tm = boolSyntax.T orelse
   tm = boolSyntax.F orelse
   tm = EQ_tm orelse
   tm = GT_tm orelse
   tm = LT_tm orelse
   tm = UN_tm

fun test_monops ty =
   let
      val cs = float_constants ty
   in
      print "\nChecking type: "
    ; print_type ty
    ; List.app
        (fn (name, monop) =>
         ( print ("\n\nTesting operation: " ^ name ^ "\n")
         ; List.app
              (fn a =>
                 let
                    val tm =
                       monop a handle e as HOL_ERR _ => (pr_term a; raise e)
                    val e1 = lcf_eval tm
                    val r = rhs (concl e1)
                 in
                    if ok_result1 r orelse ok_result2 r orelse
                       Lib.mem name ["float_negate", "float_abs"] andalso
                       is_float_some_nan a
                       then print "."
                    else ( print "\n"
                         ; print_thm e1
                         ; print "\n"
                         ; die "test_monops failed"
                         )
                 end) cs))
        [("float_negate", mk_float_negate),
         ("float_abs", mk_float_abs),
         ("float_value", mk_float_value),
         ("float_is_nan", mk_float_is_nan),
         ("float_is_infinite", mk_float_is_infinite),
         ("float_is_finite", mk_float_is_finite),
         ("float_is_normal", mk_float_is_normal),
         ("float_is_subnormal", mk_float_is_subnormal),
         ("float_is_zero", mk_float_is_zero)
        ]
    ; print "\nDone.\n"
   end

fun test_binops ty =
   let
      val cs = float_constants ty
      val is_native = ty = native_ty
   in
      print "\nChecking type: "
    ; print_type ty
    ; List.app
        (fn (name, binop) =>
         ( print ("\n\nTesting operation: " ^ name ^ "\n")
         ; List.app
              (fn mode =>
               ( print "\nMode: "; print_term mode; print "\n"
               ; List.app
                    (fn a =>
                       List.app
                          (fn b =>
                             let
                                val tm = binop (mode, a, b)
                                         handle e as HOL_ERR _ =>
                                           ( pr_term mode
                                           ; pr_term a
                                           ; pr_term b
                                           ; raise e
                                           )
                                val e1 = lcf_eval tm
                                val r = rhs (concl e1)
                             in
                                if is_native then
                                   let
                                      val e2 = native_eval tm
                                      val not_native_ok =
                                         is_float_some_nan a orelse
                                         is_float_some_nan b orelse
                                         is_float_some_nan r orelse
                                         has_tags ["native_ieee"] e2 orelse
                                         has_tags ["DISK_THM", "native_ieee"] e2
                                   in
                                      if Thm.concl e1 = Thm.concl e2 andalso
                                         not_native_ok
                                         then print "."
                                      else ( print "\n"
                                           ; print_thm e1
                                           ; print "\n\n"
                                           ; print_thm e2
                                           ; print "\n\n"
                                           ; die "test_binops failed"
                                           )
                                   end
                                else if ok_result2 r
                                   then print "."
                                else ( print "\n"
                                     ; print_thm e1
                                     ; print "\n"
                                     ; die "test_binops failed"
                                     )
                             end) cs) cs)) round_constants))
        [("float_add", mk_float_add), ("float_sub", mk_float_sub),
         ("float_mul", mk_float_mul), ("float_div", mk_float_div)
        ]
    ; print "\nDone.\n"
   end

fun test_orderings ty =
   let
      val cs = float_constants ty
      val is_native = ty = native_ty
   in
      print "\nChecking type: "
    ; print_type ty
    ; List.app
        (fn (name, binop) =>
         ( print ("\n\nTesting operation: " ^ name ^ "\n")
         ; List.app
              (fn a =>
                 List.app
                    (fn b =>
                       let
                          val tm = binop (a, b)
                                   handle e as HOL_ERR _ =>
                                     ( pr_term a
                                     ; pr_term b
                                     ; raise e
                                     )
                          val e1 = lcf_eval tm
                          val r = rhs (concl e1)
                       in
                          if is_native then
                             let
                                val e2 = native_eval tm
                                val not_native_ok =
                                   is_float_some_nan a orelse
                                   is_float_some_nan b orelse
                                   has_tags ["native_ieee"] e2 orelse
                                   has_tags ["DISK_THM", "native_ieee"] e2
                             in
                                if Thm.concl e1 = Thm.concl e2 andalso
                                   not_native_ok
                                   then print "."
                                else ( print "\n"
                                     ; print_thm e1
                                     ; print "\n\n"
                                     ; print_thm e2
                                     ; print "\n\n"
                                     ; die "test_orderings failed"
                                     )
                             end
                          else if ok_order_result r
                             then print "."
                          else ( print "\n"
                               ; print_thm e1
                               ; print "\n"
                               ; die "test_orderings failed"
                               )
                       end) cs) cs))
        [("float_less_than", mk_float_less_than),
         ("float_less_equal", mk_float_less_equal),
         ("float_greater_than", mk_float_greater_than),
         ("float_greater_equal", mk_float_greater_equal),
         ("float_equal", mk_float_equal),
         ("float_compare", mk_float_compare)]
    ; print "\nDone.\n"
   end

(* ------------------------------------------------------------------------ *)

(* start tests *)
val tt = Timer.startRealTimer ()

val () = test_monops ``:half``
val () = test_binops ``:half``
val () = test_orderings ``:half``

val () = test_monops ``:single``
val () = test_binops ``:single``
val () = test_orderings ``:single``

(*
val () = test_monops native_ty
val () = test_binops native_ty
val () = test_orderings native_ty
*)

val elapsed = Timer.checkRealTimer tt;

val _ = print ("\nTotal time: " ^ time_to_minutes elapsed ^ "\n")

(* ------------------------------------------------------------------------ *)

val _ = OS.Process.exit OS.Process.success
