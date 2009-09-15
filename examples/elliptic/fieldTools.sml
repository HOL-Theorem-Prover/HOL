(* ========================================================================= *)
(* FIELD THEORY TOOLS                                                        *)
(* ========================================================================= *)

structure fieldTools :> fieldTools =
struct

open HolKernel Parse boolLib bossLib res_quanLib groupTools fieldTheory;

val Bug = mlibUseful.Bug;

val cond_rewr_conv = subtypeTools.cond_rewr_conv;

val cond_rewrs_conv = subtypeTools.cond_rewrs_conv;

val named_conv_to_simpset_conv = subtypeTools.named_conv_to_simpset_conv;

(* ------------------------------------------------------------------------- *)
(* Syntax operations.                                                        *)
(* ------------------------------------------------------------------------- *)

val field_ty_op = "field";

fun mk_field_type ty = mk_type (field_ty_op,[ty]);

fun dest_field_type ty =
    case dest_type ty of
      (ty_op,[a]) => if ty_op = field_ty_op then a
                     else raise ERR "dest_field_type" ""
    | _ => raise ERR "dest_field_type" "";

val is_field_type = can dest_field_type;

val field_zero_tm = ``field_zero : 'a field -> 'a``;

fun mk_field_zero f =
    let
      val ty = dest_field_type (type_of f)
      val zero_tm = inst [{redex = alpha, residue = ty}] field_zero_tm
    in
      mk_comb (zero_tm,f)
    end;

fun dest_field_zero tm =
    let
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_zero_tm orelse raise ERR "dest_field_zero" ""
    in
      f
    end;

val is_field_zero = can dest_field_zero;

val field_one_tm = ``field_one : 'a field -> 'a``;

fun mk_field_one f =
    let
      val ty = dest_field_type (type_of f)
      val one_tm = inst [{redex = alpha, residue = ty}] field_one_tm
    in
      mk_comb (one_tm,f)
    end;

fun dest_field_one tm =
    let
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_one_tm orelse raise ERR "dest_field_one" ""
    in
      f
    end;

val is_field_one = can dest_field_one;

val field_num_tm = ``field_num : 'a field -> num -> 'a``;

fun mk_field_num (f,n) =
    let
      val ty = dest_field_type (type_of f)
      val num_tm = inst [{redex = alpha, residue = ty}] field_num_tm
    in
      list_mk_comb (num_tm,[f,n])
    end;

fun dest_field_num tm =
    let
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_num_tm orelse raise ERR "dest_field_num" ""
    in
      (f,x)
    end;

val is_field_num = can dest_field_num;

val field_neg_tm = ``field_neg : 'a field -> 'a -> 'a``;

fun mk_field_neg (f,x) =
    let
      val ty = dest_field_type (type_of f)
      val neg_tm = inst [{redex = alpha, residue = ty}] field_neg_tm
    in
      list_mk_comb (neg_tm,[f,x])
    end;

fun dest_field_neg tm =
    let
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_neg_tm orelse raise ERR "dest_field_neg" ""
    in
      (f,x)
    end;

val is_field_neg = can dest_field_neg;

val field_add_tm = ``field_add : 'a field -> 'a -> 'a -> 'a``;

fun mk_field_add (f,x,y) =
    let
      val ty = dest_field_type (type_of f)
      val add_tm = inst [{redex = alpha, residue = ty}] field_add_tm
    in
      list_mk_comb (add_tm,[f,x,y])
    end;

fun dest_field_add tm =
    let
      val (tm,y) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_add_tm orelse raise ERR "dest_field_add" ""
    in
      (f,x,y)
    end;

val is_field_add = can dest_field_add;

val field_sub_tm = ``field_sub : 'a field -> 'a -> 'a -> 'a``;

fun mk_field_sub (f,x,y) =
    let
      val ty = dest_field_type (type_of f)
      val sub_tm = inst [{redex = alpha, residue = ty}] field_sub_tm
    in
      list_mk_comb (sub_tm,[f,x,y])
    end;

fun dest_field_sub tm =
    let
      val (tm,y) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_sub_tm orelse raise ERR "dest_field_sub" ""
    in
      (f,x,y)
    end;

val is_field_sub = can dest_field_sub;

val field_inv_tm = ``field_inv : 'a field -> 'a -> 'a``;

fun mk_field_inv (f,x) =
    let
      val ty = dest_field_type (type_of f)
      val inv_tm = inst [{redex = alpha, residue = ty}] field_inv_tm
    in
      list_mk_comb (inv_tm,[f,x])
    end;

fun dest_field_inv tm =
    let
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_inv_tm orelse raise ERR "dest_field_inv" ""
    in
      (f,x)
    end;

val is_field_inv = can dest_field_inv;

val field_mult_tm = ``field_mult : 'a field -> 'a -> 'a -> 'a``;

fun mk_field_mult (f,x,y) =
    let
      val ty = dest_field_type (type_of f)
      val mult_tm = inst [{redex = alpha, residue = ty}] field_mult_tm
    in
      list_mk_comb (mult_tm,[f,x,y])
    end;

fun dest_field_mult tm =
    let
      val (tm,y) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_mult_tm orelse raise ERR "dest_field_mult" ""
    in
      (f,x,y)
    end;

val is_field_mult = can dest_field_mult;

val field_exp_tm = ``field_exp : 'a field -> 'a -> num -> 'a``;

fun mk_field_exp (f,x,n) =
    let
      val ty = dest_field_type (type_of f)
      val exp_tm = inst [{redex = alpha, residue = ty}] field_exp_tm
    in
      list_mk_comb (exp_tm,[f,x,n])
    end;

fun dest_field_exp tm =
    let
      val (tm,n) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_exp_tm orelse raise ERR "dest_field_exp" ""
    in
      (f,x,n)
    end;

val is_field_exp = can dest_field_exp;

val field_div_tm = ``field_div : 'a field -> 'a -> 'a -> 'a``;

fun mk_field_div (f,x,y) =
    let
      val ty = dest_field_type (type_of f)
      val div_tm = inst [{redex = alpha, residue = ty}] field_div_tm
    in
      list_mk_comb (div_tm,[f,x,y])
    end;

fun dest_field_div tm =
    let
      val (tm,y) = dest_comb tm
      val (tm,x) = dest_comb tm
      val (tm,f) = dest_comb tm
      val _ = same_const tm field_div_tm orelse raise ERR "dest_field_div" ""
    in
      (f,x,y)
    end;

val is_field_div = can dest_field_div;

fun mk_field_num_mult (f,x,n) = mk_field_mult (f, mk_field_num (f,n), x);

fun dest_field_num_mult tm =
    let
      val (f,t,x) = dest_field_mult tm
      val (_,n) = dest_field_num t
    in
      (f,x,n)
    end;

val is_field_num_mult = can dest_field_num_mult;

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val field_pretty_print = ref true;

val field_pretty_print_max_size = ref 1000;

fun field_print Gs (sys,str,brk) gravs d pp =
    let
      open Portable term_pp_types

      fun field_num tm =
          let
            val (_,x) = dest_field_num tm
          in
            sys gravs (d - 1) x
          end

      fun field_unop dest s prec tm =
          let
            val (_,x) = dest tm
          in
            begin_block pp INCONSISTENT 0;
            str s;
            brk (1,0);
            sys (Prec (prec,s), Top, Top) (d - 1) x;
            end_block pp
          end

      fun field_binop_prec x s =
          let
            val (p,l,r) = gravs
            val b =
                (case p of Prec (y,_) => y > x | _ => false) orelse
                (case l of Prec (y,_) => y >= x | _ => false) orelse
                (case r of Prec (y,_) => y > x | _ => false)
            val p = Prec (x,s)
            and l = if b then Top else l
            and r = if b then Top else r
          in
            (b,p,l,r)
          end

      fun field_binop dest s prec tm =
          let
            val (_,x,y) = dest tm
            val (b,p,l,r) = field_binop_prec prec s
            val n = term_size tm
          in
            if n > !field_pretty_print_max_size then
              (begin_block pp INCONSISTENT 0;
               str ("<<" ^ int_to_string n ^ ">>");
               end_block pp)
            else
              (begin_block pp INCONSISTENT (if b then 1 else 0);
               if b then str "(" else ();
               sys (p,l,p) (d - 1) x;
               str (" " ^ s);
               brk (1,0);
               sys (p,p,r) (d - 1) y;
               if b then str ")" else ();
               end_block pp)
          end

      fun first_printer [] _ = raise term_pp_types.UserPP_Failed
        | first_printer (p :: ps) tm =
          (p tm handle HOL_ERR _ => first_printer ps tm)
    in
      fn tm =>
      if not (!field_pretty_print) then raise term_pp_types.UserPP_Failed
      else
        first_printer
          [field_num,
           field_unop dest_field_neg "~" 900,
           field_binop dest_field_add "+" 500,
           field_binop dest_field_sub "-" 500,
           field_binop dest_field_mult "*" 600,
           field_binop dest_field_div "/" 600,
           field_binop dest_field_exp "**" 700]
          tm
    end;

val () = temp_add_user_printer ("field_print", Term `x:'a`, field_print);

(* ------------------------------------------------------------------------- *)
(* AC normalization.                                                         *)
(* ------------------------------------------------------------------------- *)

fun field_compare (x,y) =
    case (total dest_field_num x, total dest_field_num y) of
      (NONE,NONE) => compare (x,y)
    | (SOME _, NONE) => LESS
    | (NONE, SOME _) => GREATER
    | (SOME (_,x), SOME (_,y)) => compare (x,y);

val field_add_ac_conv =
    {name = "field_add_ac_conv",
     key = ``field_add f x y``,
     conv =
       subtypeTools.binop_ac_conv
         {term_compare = field_compare,
          dest_binop = dest_field_add,
          dest_inv = dest_field_neg,
          dest_exp = dest_field_num_mult,
          assoc_th = field_add_assoc,
          comm_th = field_add_comm,
          comm_th' = field_add_comm',
          id_ths =
            [field_add_lzero,
             field_add_lzero',
             field_add_rzero,
             field_add_rzero'],
          simplify_ths =
            [GSYM field_num_one,
             field_neg_zero,
             field_neg_neg,
             field_neg_add,
             field_mult_lzero,
             field_mult_lzero',
             field_mult_rzero,
             field_mult_rzero',
             field_mult_lone,
             field_mult_lone',
             field_mult_rone,
             field_mult_rone'],
          combine_ths =
            [field_single_add_single,
             field_single_add_mult,
             field_rneg,
             field_single_add_neg_mult,
             field_mult_add_mult,
             field_mult_add_neg,
             field_mult_add_neg_mult,
             field_neg_add_neg,
             field_neg_add_neg_mult,
             field_neg_mult_add_neg_mult],
          combine_ths' =
            [field_single_add_single',
             field_single_add_mult',
             field_rneg',
             field_single_add_neg_mult',
             field_mult_add_mult',
             field_mult_add_neg',
             field_mult_add_neg_mult',
             field_neg_add_neg',
             field_neg_add_neg_mult',
             field_neg_mult_add_neg_mult']}};

val field_mult_ac_conv =
    {name = "field_mult_ac_conv",
     key = ``field_mult f x y``,
     conv =
       subtypeTools.binop_ac_conv
         {term_compare = field_compare,
          dest_binop = dest_field_mult,
          dest_inv = dest_field_inv,
          dest_exp = dest_field_exp,
          assoc_th = field_mult_assoc,
          comm_th = field_mult_comm,
          comm_th' = field_mult_comm',
          id_ths =
            [field_mult_lone,
             field_mult_lone',
             field_mult_rone,
             field_mult_rone'],
          simplify_ths =
            [field_inv_one,
             field_inv_inv,
             field_inv_mult,
             field_exp_zero,
             field_exp_one,
             field_exp_exp,
             field_exp_mult,
             field_exp_inv],
          combine_ths =
            [field_single_mult_single,
             field_single_mult_exp,
             field_rinv,
             field_single_mult_inv_exp,
             field_exp_mult_exp,
             field_exp_mult_inv,
             field_exp_mult_inv_exp,
             field_inv_mult_inv,
             field_inv_mult_inv_exp,
             field_inv_exp_mult_inv_exp],
          combine_ths' =
            [field_single_mult_single',
             field_single_mult_exp',
             field_rinv',
             field_single_mult_inv_exp',
             field_exp_mult_exp',
             field_exp_mult_inv',
             field_exp_mult_inv_exp',
             field_inv_mult_inv',
             field_inv_mult_inv_exp',
             field_inv_exp_mult_inv_exp']}};

(* ------------------------------------------------------------------------- *)
(* Proof tools.                                                              *)
(* ------------------------------------------------------------------------- *)

local
  val field_sub_eq_zero_conv =
      let
        val th = CONV_RULE RES_FORALL_CONV (GSYM field_sub_eq_zero)
      in
        fn f => cond_rewr_conv (ISPEC f th)
      end;

  fun left_conv solver tm =
      let
        val (x,y) = dest_eq tm
        val _ = not (is_field_zero y) orelse
                raise ERR "field_sub_eq_zero_conv (left)" "looping"
        val (f,_,_) = dest_field_add x
      in
        field_sub_eq_zero_conv f solver
      end tm;

  fun right_conv solver tm =
      let
        val (_,y) = dest_eq tm
        val (f,_,_) = dest_field_add y
      in
        field_sub_eq_zero_conv f solver
      end tm;
in
  val field_sub_eq_zero_l_conv =
      {name = "field_sub_eq_zero_conv (left)",
       key = ``field_add (f : 'a field) x y = z``,
       conv = left_conv}
  and field_sub_eq_zero_r_conv =
      {name = "field_sub_eq_zero_conv (right)",
       key = ``x = field_add (f : 'a field) y z``,
       conv = right_conv};
end;

local
  fun field_field tm =
      case total dest_field_zero tm of
        SOME f => f
      | NONE =>
        case total dest_field_one tm of
          SOME f => f
        | NONE =>
          case total dest_field_num tm of
            SOME (f,_) => f
          | NONE =>
            case total dest_field_neg tm of
              SOME (f,_) => f
            | NONE =>
              case total dest_field_add tm of
                SOME (f,_,_) => f
              | NONE =>
                case total dest_field_mult tm of
                  SOME (f,_,_) => f
                | NONE =>
                  case total dest_field_exp tm of
                    SOME (f,_,_) => f
                  | NONE => raise ERR "field_field" "";

  fun field_to_exp tm varmap =
      case total dest_field_zero tm of
        SOME _ => (Algebra.fromInt 0, varmap)
      | NONE =>
        case total dest_field_one tm of
          SOME _ => (Algebra.fromInt 1, varmap)
        | NONE =>
          case total dest_field_num tm of
            SOME (_,n) => (Algebra.fromInt (numLib.int_of_term n), varmap)
          | NONE =>
            case total dest_field_neg tm of
              SOME (_,a) =>
              let
                val (a,varmap) = field_to_exp a varmap
              in
                (Algebra.negate a, varmap)
              end
            | NONE =>
              case total dest_field_add tm of
                SOME (_,a,b) =>
                let
                  val (a,varmap) = field_to_exp a varmap
                  val (b,varmap) = field_to_exp b varmap
                in
                  (Algebra.add (a,b), varmap)
                end
              | NONE =>
                case total dest_field_sub tm of
                  SOME (_,a,b) =>
                  let
                    val (a,varmap) = field_to_exp a varmap
                    val (b,varmap) = field_to_exp b varmap
                  in
                    (Algebra.subtract (a,b), varmap)
                  end
                | NONE =>
                  case total dest_field_mult tm of
                    SOME (_,a,b) =>
                    let
                      val (a,varmap) = field_to_exp a varmap
                      val (b,varmap) = field_to_exp b varmap
                    in
                      (Algebra.multiply (a,b), varmap)
                    end
                  | NONE =>
                    case total dest_field_exp tm of
                      SOME (_,a,n) =>
                      let
                        val (a,varmap) = field_to_exp a varmap
                      in
                        (Algebra.power (a, numLib.int_of_term n), varmap)
                      end
                    | NONE =>
                      let
                        val s = term_to_string tm
                        val v = Algebra.Var s
                      in
                        case List.find (equal s o fst) varmap of
                          NONE => (v, (s,tm) :: varmap)
                        | SOME (_,tm') =>
                          let
                            val _ = tm = tm' orelse raise Bug "field_to_exp"
                          in
                            (v,varmap)
                          end
                      end;

  fun exp_to_field f varmap e =
      case Algebra.toInt e of
        SOME n =>
        if 0 <= n then mk_field_num (f, numLib.term_of_int n)
        else mk_field_neg (f, mk_field_num (f, numLib.term_of_int (~n)))
      | NONE =>
        case e of
          Algebra.Var v =>
          (case List.find (equal v o fst) varmap of
             NONE => raise Bug "exp_to_field: variable not found"
           | SOME (_,tm) => tm)
        | Algebra.Sum m =>
          (case map (exp_sum_to_field f varmap) (rev (Map.toList m)) of
             [] => raise Bug "exp_to_field: empty sum"
           | x :: xs => foldl (fn (y,z) => mk_field_add (f,y,z)) x xs)
        | Algebra.Prod m =>
          (case map (exp_prod_to_field f varmap) (rev (Map.toList m)) of
             [] => raise Bug "exp_to_field: empty product"
           | x :: xs => foldl (fn (y,z) => mk_field_mult (f,y,z)) x xs)
  and exp_sum_to_field f varmap (e,n) =
      let
        val e = exp_to_field f varmap e
      in
        if n = 1 then e
        else if n = ~1 then mk_field_neg (f,e)
        else if 0 <= n then mk_field_num_mult (f, e, numLib.term_of_int n)
        else mk_field_neg (f, mk_field_num_mult (f, e, numLib.term_of_int (~n)))
      end
  and exp_prod_to_field f varmap (e,n) =
      let
        val e = exp_to_field f varmap e
      in
        if n = 1 then e
        else if n = ~1 then mk_field_inv (f,e)
        else if 0 <= n then mk_field_exp (f, e, numLib.term_of_int n)
        else mk_field_inv (f, mk_field_exp (f, e, numLib.term_of_int (~n)))
      end;
in
  fun ORACLE_field_poly_conv term_normalize_ths _ tm =
      let
        val field = field_field tm

        val _ = print ("ORACLE_field_poly_conv: input =\n"
                       ^ term_to_string tm ^ "\n")

        val _ = print ("ORACLE_field_poly_conv: reducing with "
                       ^ int_to_string (length term_normalize_ths)
                       ^ " equations.\n")

        val _ = print ("ORACLE_field_poly_conv: field = "
                       ^ term_to_string field ^ "\n")

        val (exp,varmap) = field_to_exp tm []

        fun mk_eqn th varmap =
            let
              val (l_tm,r_tm) = dest_eq (concl th)
              val (l_exp,varmap) = field_to_exp l_tm varmap
              val (r_exp,varmap) = field_to_exp r_tm varmap
            in
              ((l_exp,r_exp),varmap)
            end

        val (eqns,varmap) = Useful.maps mk_eqn term_normalize_ths varmap

        val _ = print ("ORACLE_field_poly_conv: variables =\n\""
                       ^ Useful.join "\" \"" (map fst varmap) ^ "\"\n")

        val exp = Algebra.normalize {equations = eqns} exp

        val tm' = exp_to_field field varmap exp

        val _ = print ("ORACLE_field_poly_conv: result =\n"
                       ^ term_to_string tm' ^ "\n")

        val _ = tm <> tm' orelse raise ERR "ORACLE_field_poly_conv" "unchanged"
      in
        mk_oracle_thm "field_poly" ([], mk_eq (tm,tm'))
      end;
end;

local
  val field_single_mult_exp_alt = prove
    (``!f x n.
         f IN Field /\ x IN f.carrier ==>
         (field_exp f x (SUC n) = field_mult f x (field_exp f x n))``,
     METIS_TAC [field_single_mult_exp, arithmeticTheory.ADD1]);

  val field_exp_mult_exp_alt = prove
    (``!f x m n.
         f IN Field /\ x IN f.carrier ==>
         (field_exp f x (m + n) =
          field_mult f (field_exp f x m) (field_exp f x n))``,
     METIS_TAC [field_exp_mult_exp]);

  val field_mult_lone_conv =
      let
        val th = CONV_RULE RES_FORALL_CONV (GSYM field_mult_lone)
      in
        fn f => cond_rewr_conv (ISPEC f th)
      end;

  val field_mult_rone_conv =
      let
        val th = CONV_RULE RES_FORALL_CONV (GSYM field_mult_rone)
      in
        fn f => cond_rewr_conv (ISPEC f th)
      end;

  fun field_single_mult_exp_conv f x n =
      let
        val th = ISPECL [f, x, numLib.term_of_int n] field_single_mult_exp_alt
        val conv = RAND_CONV (LAND_CONV (RAND_CONV reduceLib.SUC_CONV))
        val th = CONV_RULE conv th
      in
        cond_rewr_conv th
      end;

  fun field_exp_mult_exp_conv f x m n =
      let
        val th = field_exp_mult_exp_alt
        val th = ISPECL [f, x, numLib.term_of_int m, numLib.term_of_int n] th
        val conv = RAND_CONV (LAND_CONV (RAND_CONV reduceLib.ADD_CONV))
        val th = CONV_RULE conv th
      in
        cond_rewr_conv th
      end;

  fun field_mult_presimp_conv solver =
(***
      trace_conv "field_mult_presimp_conv"
***)
        (QCONV (TRY_CONV (#conv field_mult_ac_conv solver) THENC
                reduceLib.REDUCE_CONV));

  fun field_mult_postsimp_conv solver =
      BINOP_CONV (field_mult_presimp_conv solver);

  fun dest_field_power tm =
      case total dest_field_exp tm of
        NONE => (tm,NONE)
      | SOME (_,t,n) => (t, SOME (numLib.int_of_term n))

  fun hcf_power_conv2 f (a,b) =
      if aconv a b then (field_mult_rone_conv f, field_mult_rone_conv f)
      else
        let
          val _ = not (is_field_mult a) orelse raise Bug "a is a mult"
          and _ = not (is_field_mult b) orelse raise Bug "b is a mult"

          val (at,an) = dest_field_power a
          and (bt,bn) = dest_field_power b

          val _ = aconv at bt orelse raise Bug "at <> bt"

          val _ = (case an of NONE => true | SOME n => n >= 2) orelse
                  raise Bug "exponenent of a is less than 2 (nyi)"

          val _ = (case bn of NONE => true | SOME n => n >= 2) orelse
                  raise Bug "exponenent of b is less than 2 (nyi)"
        in
          case (an,bn) of
            (NONE,NONE) => raise Bug "a = b"
          | (SOME an, NONE) =>
            (field_single_mult_exp_conv f at (an - 1), field_mult_rone_conv f)
          | (NONE, SOME bn) =>
            (field_mult_rone_conv f, field_single_mult_exp_conv f bt (bn - 1))
          | (SOME an, SOME bn) =>
            (case Int.compare (an,bn) of
               LESS => (field_mult_rone_conv f,
                        field_exp_mult_exp_conv f bt an (bn - an))
             | EQUAL => raise Bug "a = b (power)"
             | GREATER => (field_exp_mult_exp_conv f at bn (an - bn),
                           field_mult_rone_conv f))
        end;

  local
    val field_mult_comm_conv' = cond_rewr_conv field_mult_comm';

    val field_mult_assoc_conv = cond_rewr_conv field_mult_assoc;

    val field_mult_assoc_conv' = cond_rewr_conv (GSYM field_mult_assoc);
  in
    fun push_conv solver a_th =
        RAND_CONV (K a_th) THENC field_mult_comm_conv' solver;

    fun double_push_conv solver ac a_th =
        LAND_CONV (ac solver) THENC
        field_mult_assoc_conv solver THENC
        RAND_CONV (push_conv solver a_th) THENC
        field_mult_assoc_conv' solver;
  end;

  fun hcf_conv2 f solver (a,b) =
      if is_field_one a orelse is_field_one b then
        (field_mult_lone_conv f solver a,
         field_mult_lone_conv f solver b)
      else if not (is_field_mult a) then
        let
          val a_th = field_mult_rone_conv f solver a
          val (a_th',b_th) = hcf_conv2 f solver (rhs (concl a_th), b)
        in
          (TRANS a_th a_th', b_th)
        end
      else if not (is_field_mult b) then
        let
          val b_th = field_mult_rone_conv f solver b
          val (a_th,b_th') = hcf_conv2 f solver (a, rhs (concl b_th))
        in
          (a_th, TRANS b_th b_th')
        end
      else
        let
          val (a1,a2) =
              case total dest_field_mult a of
                NONE => raise Bug "a not a mult"
              | SOME (_,a1,a2) => (a1,a2)

          val (b1,b2) =
              case total dest_field_mult b of
                NONE => raise Bug "b not a mult"
              | SOME (_,b1,b2) => (b1,b2)

          val (at,an) = dest_field_power a1
          and (bt,bn) = dest_field_power b1
        in
          case field_compare (at,bt) of
            LESS =>
            let
              val (a_th,b_th) = hcf_conv2 f solver (a2,b)
            in
              (push_conv solver a_th a, b_th)
            end
          | EQUAL =>
            let
              val (ac,bc) = hcf_power_conv2 f (a1,b1)
              val (a_th,b_th) = hcf_conv2 f solver (a2,b2)
            in
              (double_push_conv solver ac a_th a,
               double_push_conv solver bc b_th b)
            end
          | GREATER =>
            let
              val (a_th,b_th) = hcf_conv2 f solver (a,b2)
            in
              (a_th, push_conv solver b_th b)
            end
        end;
in
  fun field_hcf_conv2 f solver (a,b) =
      let
(*
        val () = (print "field_hcf_conv2: "; print_term a; print ", ";
                  print_term b; print "\n")
*)
        val a_th = field_mult_presimp_conv solver a
        and b_th = field_mult_presimp_conv solver b
(*
        val () = (print "field_hcf_conv2: "; print_thm a_th; print ", ";
                  print_thm b_th; print "\n")
*)
        val (a',b') = (rhs (concl a_th), rhs (concl b_th))
        val (a_th',b_th') = hcf_conv2 f solver (a',b')
        val a_th'' = field_mult_postsimp_conv solver (rhs (concl a_th'))
        and b_th'' = field_mult_postsimp_conv solver (rhs (concl b_th'))
        val a_th = TRANS a_th (TRANS a_th' a_th'')
        and b_th = TRANS b_th (TRANS b_th' b_th'')
(***
        val () = (print "field_hcf_conv2: "; print_thm a_th; print ", ";
                  print_thm b_th; print "\n")
***)
      in
        (a_th,b_th)
      end;
end;

local
  val has_nested_divs = can (find_term (same_const field_div_tm));

  fun is_normal_numerator tm = not (has_nested_divs tm);

  fun is_normal_denominator tm = not (has_nested_divs tm);

  fun is_normal_fraction is_div tm =
      if not is_div then is_normal_numerator tm
      else
        let
          val (_,n,d) = dest_field_div tm
        in
          is_normal_numerator n andalso is_normal_denominator d
        end;

  fun check_normal_fraction is_div tm =
      if is_normal_fraction is_div tm then ()
      else raise ERR "check_normal_fraction" "";

  val field_add_divl_conv = cond_rewr_conv field_add_divl
  and field_add_divr_conv = cond_rewr_conv field_add_divr
  and field_add_div2_conv = cond_rewr_conv field_add_div
  and field_add_divl_conv' = cond_rewr_conv field_add_divl'
  and field_add_divr_conv' = cond_rewr_conv field_add_divr'
  and field_add_div2_conv' = cond_rewr_conv field_add_div';

  fun field_add_div_hcf solver x1 x2 =
      let
        val (f,a1,b1) = dest_field_div x1
        and (_,a2,b2) = dest_field_div x2
      in
        field_hcf_conv2 f solver (b1,b2)
      end;

  fun field_add_div_hcf_conv (th1,th2) solver =
      LAND_CONV (RAND_CONV (K th1)) THENC
      RAND_CONV (RAND_CONV (K th2)) THENC
      field_add_div2_conv solver;

  fun field_add_div_hcf_conv' (th1,th2) solver =
      LAND_CONV (RAND_CONV (K th1)) THENC
      RAND_CONV (LAND_CONV (RAND_CONV (K th2))) THENC
      field_add_div2_conv' solver;

  fun field_add_div_conv solver tm =
(***
      trace_conv "field_add_div_conv"
***)
      let
        val (f,a,b) = dest_field_add tm
        val ap = is_field_div a
        and bp = is_field_div b
        val () = check_normal_fraction ap a
        and () = check_normal_fraction bp b
      in
        case (ap,bp) of
          (false,false) => raise ERR "field_add_div_conv" "no div"
        | (true,false) => field_add_divl_conv solver
        | (false,true) => field_add_divr_conv solver
        | (true,true) =>
          field_add_div_hcf_conv (field_add_div_hcf solver a b) solver
      end tm;

  fun field_add_div_conv' solver tm =
(***
      trace_conv "field_add_div_conv'"
***)
      let
        val (f,a,b) = dest_field_add tm
        val (_,b,_) = dest_field_add b
        val ap = is_field_div a
        and bp = is_field_div b
        val () = check_normal_fraction ap a
        and () = check_normal_fraction bp b
      in
        case (ap,bp) of
          (false,false) => raise ERR "field_add_div_conv'" "no div"
        | (true,false) => field_add_divl_conv' solver
        | (false,true) => field_add_divr_conv' solver
        | (true,true) =>
          field_add_div_hcf_conv' (field_add_div_hcf solver a b) solver
      end tm;
in
  val field_add_div_conv_left =
      {name = "field_add_div_conv (left)",
       key = ``field_add (f : 'a field) (field_div f x y) z``,
       conv = field_add_div_conv}
  and field_add_div_conv_right =
      {name = "field_add_div_conv (right)",
       key = ``field_add (f : 'a field) x (field_div f y z)``,
       conv = field_add_div_conv}
  and field_add_div_conv_left' =
      {name = "field_add_div_conv' (left)",
       key = ``field_add (f : 'a field) (field_div f x y) (field_add f z p)``,
       conv = field_add_div_conv'}
  and field_add_div_conv_right' =
      {name = "field_add_div_conv' (right)",
       key = ``field_add (f : 'a field) x (field_add f (field_div f y z) p)``,
       conv = field_add_div_conv'};
end;

fun field_div_elim_ss context =
    let
      val rewrs =
          [field_sub_def,
           field_neg_add,
           GSYM field_div_lneg, field_div_rneg,
           field_div_multl,field_div_multr,
           field_div_divl,field_div_divr,
           field_div_exp,
           field_mult_assoc,
           field_single_mult_single,
           field_single_mult_single']

      val convs =
          map
            named_conv_to_simpset_conv
            [field_add_div_conv_left,
             field_add_div_conv_right]

      val data =
          simpLib.SSFRAG
            {name = NONE, ac = [], congs = [], convs = convs, rewrs = rewrs,
             dprocs = [], filter = NONE}

      val {simplify = alg_ss, ...} = subtypeTools.simpset2 context
    in
      simpLib.++ (alg_ss,data)
    end;

local
  val add_assoc_conv = cond_rewr_conv field_add_assoc
  and neg_neg_conv = cond_rewr_conv field_neg_neg
  and neg_add_conv = cond_rewr_conv field_neg_add
  and mult_lneg_conv = cond_rewr_conv field_mult_lneg
  and mult_rneg_conv = cond_rewr_conv field_mult_rneg
  and distrib_ladd_conv = cond_rewr_conv field_distrib_ladd
  and distrib_radd_conv = cond_rewr_conv field_distrib_radd
  and mult_assoc_conv = cond_rewr_conv field_mult_assoc
  and exp_zero_conv = cond_rewr_conv field_exp_zero
  and exp_one_conv = cond_rewr_conv field_exp_one
  and exp_num_conv = cond_rewr_conv field_num_exp
  and exp_exp_conv = cond_rewr_conv field_exp_exp
  and exp_mult_conv = cond_rewr_conv field_exp_mult
  and exp_neg_conv = cond_rewr_conv field_exp_neg
  and binomial_2_conv = cond_rewr_conv field_binomial_2
  and binomial_3_conv = cond_rewr_conv field_binomial_3
  and binomial_4_conv = cond_rewr_conv field_binomial_4;

  val num_conv =
      cond_rewrs_conv [field_num_exp,field_num_mult,field_num_mult'];
in
  val ORACLE_field_poly = ref false;

  val field_poly_print_term = ref false;

  fun field_poly_conv term_normalize_ths solver tm =
      if !ORACLE_field_poly then
        ORACLE_field_poly_conv term_normalize_ths solver tm
      else
(***
        trace_conv "field_poly_conv"
***)
        let
          val term_normalize_conv = PURE_REWRITE_CONV term_normalize_ths

          fun exp_conv tm =
              let
                val (_,a,n) = dest_field_exp tm
              in
                FIRST_CONV
                  [exp_zero_conv solver,
                   exp_one_conv solver,
                   exp_num_conv solver THENC RAND_CONV reduceLib.EXP_CONV,
                   exp_exp_conv solver THENC
                     TRY_CONV (RAND_CONV reduceLib.MUL_CONV) THENC
                     TRY_CONV exp_conv,
                   exp_mult_conv solver,
                   exp_neg_conv solver THENC
                     RATOR_CONV (LAND_CONV reduceLib.EVEN_CONV) THENC
                     COND_CONV,
                   binomial_2_conv solver,
                   binomial_3_conv solver,
                   binomial_4_conv solver]
              end tm

          fun mult_conv tm =
              (case total dest_field_mult tm of
                 NONE => exp_conv THENC TRY_CONV mult_conv
               | SOME (_,a,b) =>
                 FIRST_CONV
                   [mult_lneg_conv solver,
                    mult_rneg_conv solver,
                    distrib_radd_conv solver,
                    distrib_ladd_conv solver,
                    mult_assoc_conv solver THENC TRY_CONV mult_conv,
                    LAND_CONV exp_conv THENC TRY_CONV mult_conv,
                    RAND_CONV mult_conv THENC TRY_CONV mult_conv]) tm

          fun term_conv tm =
              (mult_conv ORELSEC
               CHANGED_CONV
                 (TRY_CONV (#conv field_mult_ac_conv solver) THENC
                  DEPTH_CONV (num_conv solver) THENC
                  reduceLib.REDUCE_CONV THENC
                  term_normalize_conv)) tm

          fun neg_conv tm =
              (case total dest_field_neg tm of
                 NONE => term_conv THENC TRY_CONV neg_conv
               | SOME (_,a) =>
                 FIRST_CONV
                   [neg_neg_conv solver,
                    neg_add_conv solver,
                    RAND_CONV term_conv THENC TRY_CONV neg_conv]) tm

          fun add_conv n tm =
              (case total dest_field_add tm of
                 NONE => neg_conv THENC TRY_CONV (add_conv n)
               | SOME (_,a,b) =>
                 let
                   fun print_term_conv conv tm =
                       let
                         val n = n + term_size a
                         val () = print ("term<<" ^ int_to_string n ^ ">>: ")
                         val () = print_term a
                         val () = print "\n"
                       in
                         conv n tm
                       end
                 in
                   FIRST_CONV
                     [add_assoc_conv solver THENC TRY_CONV (add_conv n),
                      LAND_CONV neg_conv THENC TRY_CONV (add_conv n),
                      print_term_conv (RAND_CONV o add_conv)]
                 end) tm

          val cancel_conv = #conv field_add_ac_conv solver

          val poly_conv =
              (add_conv 0 THENC TRY_CONV cancel_conv) ORELSEC cancel_conv
        in
          poly_conv
        end tm;
end;

val field_op_patterns =
    [``field_add (f : 'a field) x y``,
     ``field_neg (f : 'a field) x``,
     ``field_mult (f : 'a field) x y``,
     ``field_exp (f : 'a field) x n``,
     ``field_num (f : 'a field) n``];

val field_op_blocking_congs =
    let
      fun in_pattern pattern =
          let
            val (_,l) = strip_comb pattern
            val ty = hd (snd (dest_type (type_of (hd l)))) --> bool
          in
            pred_setSyntax.mk_in (pattern, mk_var ("s",ty))
          end

      val patterns = field_op_patterns
    in
      map REFL patterns @ map (REFL o in_pattern) patterns
    end;

fun field_poly_ss context term_normalize_ths =
    let
      val patterns = field_op_patterns

      val congs = field_op_blocking_congs

      val convs =
          map
            (fn (n,key) =>
             named_conv_to_simpset_conv
             {name = "field_poly_conv (" ^ int_to_string n ^ ")",
              key = key,
              conv = field_poly_conv term_normalize_ths})
            (enumerate 0 patterns)

      val data =
          simpLib.SSFRAG
            {name =  NONE, ac = [], congs = congs, convs = convs, rewrs = [],
             dprocs = [], filter = NONE}

      val {simplify = alg_ss, ...} = subtypeTools.simpset2 context
    in
      simpLib.++ (alg_ss,data)
    end;

local
  val push_disch =
      let
        val f = MATCH_MP (PROVE [] ``(a ==> (b = c)) ==> (a ==> b = a ==> c)``)
      in
        fn d => fn th => f (DISCH d th)
      end;

  val and_imp_intro = CONV_RULE (BINOP_CONV (REWR_CONV AND_IMP_INTRO));
in
  fun field_poly_basis_conv solver tm =
      let
        fun f [] _ = raise Bug "field_poly_basis_conv"
          | f [eqn] th = push_disch eqn th
          | f (eqn :: (eqns as _ :: _)) th =
            and_imp_intro (push_disch eqn (f eqns th))

        val (eqns,tm) = dest_imp_only tm
        val eqns = strip_conj eqns
        val reduce_ths = map ASSUME eqns

(***
        val _ = print ("field_poly_basis_conv: reducing with "
                       ^ int_to_string (length eqns) ^ " equations.\n")
***)

        val th = f eqns (LAND_CONV (field_poly_conv reduce_ths solver) tm)

        val _ = (print "field_poly_basis_conv: result thm =\n";
                 print_thm th; print "\n")
      in
        th
      end;
end;

fun field_poly_basis_ss context =
    let
      val patterns =
          [``((x : 'a) = y) ==> (z = field_zero (f : 'a field))``,
           ``((x : 'a) = y) /\ E ==> (z = field_zero (f : 'a field))``]

      val congs = map REFL patterns @ field_op_blocking_congs

      val convs =
          map
            (fn (n,key) =>
             named_conv_to_simpset_conv
             {name = "field_poly_basis_conv (" ^ int_to_string n ^ ")",
              key = key,
              conv = field_poly_basis_conv})
            (enumerate 0 patterns)

      val data =
          simpLib.SSFRAG
            {name =  NONE, ac = [], congs = [], convs = convs, rewrs = [],
             dprocs = [], filter = NONE}

      val {simplify = alg_ss, ...} = subtypeTools.simpset2 context
    in
      simpLib.++ (alg_ss,data)
    end;

(* ------------------------------------------------------------------------- *)
(* Subtype context.                                                          *)
(* ------------------------------------------------------------------------- *)

val context = group_context;
val context = subtypeTools.add_rewrite2'' field_sub_def context;
val context = subtypeTools.add_judgement2 FiniteField_Field context;
val context = subtypeTools.add_judgement2 field_nonzero_carrier context;
val context = subtypeTools.add_reduction2 field_zero_carrier context;
val context = subtypeTools.add_rewrite2 field_one_zero context;
val context = subtypeTools.add_reduction2 field_one_nonzero context;
val context = subtypeTools.add_reduction2 field_neg_carrier context;
val context = subtypeTools.add_reduction2 field_add_carrier context;
val context = subtypeTools.add_rewrite2'' field_add_assoc context;
val context = subtypeTools.add_rewrite2 field_num_zero context;
val context = subtypeTools.add_rewrite2 field_add_lzero context;
val context = subtypeTools.add_rewrite2'' (GSYM field_num_one) context;
val context = subtypeTools.add_rewrite2 field_add_lzero' context;
val context = subtypeTools.add_rewrite2 field_add_rzero context;
val context = subtypeTools.add_rewrite2 field_add_rzero' context;
val context = subtypeTools.add_rewrite2 field_lneg context;
val context = subtypeTools.add_rewrite2 field_lneg' context;
val context = subtypeTools.add_rewrite2 field_rneg context;
val context = subtypeTools.add_rewrite2 field_rneg' context;
val context = subtypeTools.add_rewrite2' field_add_lcancel context;
val context = subtypeTools.add_rewrite2' field_add_rcancel context;
val context = subtypeTools.add_reduction2 field_inv_nonzero context;
val context = subtypeTools.add_rewrite2 field_mult_lzero context;
val context = subtypeTools.add_rewrite2 field_mult_lzero' context;
val context = subtypeTools.add_rewrite2 field_mult_rzero context;
val context = subtypeTools.add_rewrite2 field_mult_rzero' context;
val context = subtypeTools.add_reduction2 field_mult_nonzero context;
val context = subtypeTools.add_reduction2 field_mult_carrier context;
val context = subtypeTools.add_rewrite2'' field_mult_assoc context;
val context = subtypeTools.add_rewrite2' field_entire context;
val context = subtypeTools.add_rewrite2 field_mult_lone context;
val context = subtypeTools.add_rewrite2 field_mult_lone' context;
val context = subtypeTools.add_rewrite2 field_mult_rone context;
val context = subtypeTools.add_rewrite2 field_mult_rone' context;
val context = subtypeTools.add_rewrite2 field_linv context;
val context = subtypeTools.add_rewrite2 field_linv' context;
val context = subtypeTools.add_rewrite2 field_rinv context;
val context = subtypeTools.add_rewrite2 field_rinv' context;
val context = subtypeTools.add_rewrite2' field_mult_lcancel context;
val context = subtypeTools.add_rewrite2' field_mult_rcancel context;
val context = subtypeTools.add_rewrite2 field_neg_neg context;
val context = subtypeTools.add_rewrite2 field_neg_cancel context;
val context = subtypeTools.add_rewrite2 field_neg_zero context;
val context = subtypeTools.add_rewrite2 field_mult_lneg context;
val context = subtypeTools.add_rewrite2 field_mult_rneg context;
val context = subtypeTools.add_rewrite2'' field_inv_mult context;
val context = subtypeTools.add_reduction2 field_exp_carrier context;
val context = subtypeTools.add_reduction2 field_exp_nonzero context;
val context = subtypeTools.add_reduction2 field_num_carrier context;
val context = subtypeTools.add_rewrite2 field_inv_one context;
val context = subtypeTools.add_rewrite2 field_exp_zero context;
val context = subtypeTools.add_rewrite2 field_exp_one context;
val context = subtypeTools.add_rewrite2'' field_neg_add context;
val context = subtypeTools.add_rewrite2 field_num_add context;
val context = subtypeTools.add_rewrite2'' field_num_add' context;
val context = subtypeTools.add_rewrite2 field_num_mult context;
val context = subtypeTools.add_rewrite2'' field_num_mult' context;
val context = subtypeTools.add_rewrite2 field_num_exp context;
val context = subtypeTools.add_rewrite2'' field_single_add_single context;
val context = subtypeTools.add_rewrite2'' field_single_add_single' context;
val context = subtypeTools.add_rewrite2'' field_single_add_mult context;
val context = subtypeTools.add_rewrite2'' field_single_add_mult' context;
val context = subtypeTools.add_rewrite2'' field_single_add_neg_mult context;
val context = subtypeTools.add_rewrite2'' field_single_add_neg_mult' context;
val context = subtypeTools.add_rewrite2'' field_mult_add_mult context;
val context = subtypeTools.add_rewrite2'' field_mult_add_mult' context;
val context = subtypeTools.add_rewrite2'' field_mult_add_neg context;
val context = subtypeTools.add_rewrite2'' field_mult_add_neg' context;
val context = subtypeTools.add_rewrite2'' field_mult_add_neg_mult context;
val context = subtypeTools.add_rewrite2'' field_mult_add_neg_mult' context;
val context = subtypeTools.add_rewrite2'' field_neg_add_neg context;
val context = subtypeTools.add_rewrite2'' field_neg_add_neg' context;
val context = subtypeTools.add_rewrite2'' field_neg_add_neg_mult context;
val context = subtypeTools.add_rewrite2'' field_neg_add_neg_mult' context;
val context = subtypeTools.add_rewrite2'' field_neg_mult_add_neg_mult context;
val context = subtypeTools.add_rewrite2'' field_neg_mult_add_neg_mult' context;
val context = subtypeTools.add_rewrite2'' field_single_mult_single context;
val context = subtypeTools.add_rewrite2'' field_single_mult_single' context;
val context = subtypeTools.add_rewrite2'' field_single_mult_exp context;
val context = subtypeTools.add_rewrite2'' field_single_mult_exp' context;
val context = subtypeTools.add_rewrite2'' field_single_mult_inv_exp context;
val context = subtypeTools.add_rewrite2'' field_single_mult_inv_exp' context;
val context = subtypeTools.add_rewrite2'' field_exp_mult_exp context;
val context = subtypeTools.add_rewrite2'' field_exp_mult_exp' context;
val context = subtypeTools.add_rewrite2'' field_exp_mult_inv context;
val context = subtypeTools.add_rewrite2'' field_exp_mult_inv' context;
val context = subtypeTools.add_rewrite2'' field_exp_mult_inv_exp context;
val context = subtypeTools.add_rewrite2'' field_exp_mult_inv_exp' context;
val context = subtypeTools.add_rewrite2'' field_inv_mult_inv context;
val context = subtypeTools.add_rewrite2'' field_inv_mult_inv' context;
val context = subtypeTools.add_rewrite2'' field_inv_mult_inv_exp context;
val context = subtypeTools.add_rewrite2'' field_inv_mult_inv_exp' context;
val context = subtypeTools.add_rewrite2'' field_inv_exp_mult_inv_exp context;
val context = subtypeTools.add_rewrite2'' field_inv_exp_mult_inv_exp' context;
val context = subtypeTools.add_rewrite2 field_one_exp context;
val context = subtypeTools.add_rewrite2 field_zero_exp context;
val context = subtypeTools.add_rewrite2 field_exp_eq_zero context;
val context = subtypeTools.add_rewrite2'' field_exp_neg context;
val context = subtypeTools.add_rewrite2'' field_exp_exp context;
val context = subtypeTools.add_conversion2'' field_sub_eq_zero_r_conv context;
val context = subtypeTools.add_conversion2'' field_sub_eq_zero_l_conv context;
val context = subtypeTools.add_rewrite2 field_inv_inv context;
val context = subtypeTools.add_reduction2 field_sub_carrier context;
val context = subtypeTools.add_reduction2 field_neg_nonzero context;
val context = subtypeTools.add_rewrite2'' field_inv_neg context;
val context = subtypeTools.add_rewrite2'' field_exp_mult context;
val context = subtypeTools.add_rewrite2'' field_exp_inv context;
val context = subtypeTools.add_conversion2'' field_add_ac_conv context;
val context = subtypeTools.add_conversion2'' field_mult_ac_conv context;
val context = subtypeTools.add_reduction2 field_div_carrier context;
val context = subtypeTools.add_reduction2 field_div_nonzero context;
val context = subtypeTools.add_rewrite2 field_inv_eq_zero context;
val context = subtypeTools.add_rewrite2 field_div_eq_zero context;
val context = subtypeTools.add_judgement2 GF_in_carrier_imp context;
val context = subtypeTools.add_reduction2 GF context;

val field_context = context;

end
