structure numSyntax :> numSyntax =
struct
  open HolKernel
  local open arithmeticTheory in end;

  infixr -->
  val num_ty = mk_thy_type{Thy = "num", Tyop = "num", Args = []}
  val n_n_ty = num_ty --> num_ty
  val n3_ty = num_ty --> n_n_ty

  val zero_t = mk_thy_const{Name = "0", Ty = num_ty, Thy = "num"};
  val SUC_t = mk_thy_const{Name = "SUC", Ty = n_n_ty, Thy = "num"};
  val plus_t = mk_thy_const{Name = "+", Ty = n3_ty, Thy = "arithmetic"};
  val NUMERAL_t = mk_thy_const{Name = "NUMERAL", Ty = n_n_ty,
                               Thy = "arithmetic"}
  val ALT_ZERO_t = mk_thy_const{Name = "ALT_ZERO", Ty = num_ty,
                                Thy = "arithmetic"}

  val mk_numeral = Numeral.gen_mk_numeral {
    mk_comb = Term.mk_comb,
    ALT_ZERO = ALT_ZERO_t,
    ZERO = zero_t,
    NUMERAL = NUMERAL_t,
    BIT1 = mk_thy_const{Name = "NUMERAL_BIT1", Ty = n_n_ty,
                        Thy = "arithmetic"},
    BIT2 = mk_thy_const{Name = "NUMERAL_BIT2", Ty = n_n_ty,
                        Thy = "arithmetic"}
  };

  val dest_numeral = Numeral.dest_numeral
  val is_numeral = Numeral.is_numeral

  fun mk_binop t (t1, t2) = list_mk_comb(t, [t1, t2])
  val mk_plus = mk_binop plus_t

  fun mk_SUC t = Term.mk_comb{Rator = SUC_t, Rand = t};
  fun is_SUC t = Term.is_comb t andalso rator t = SUC_t


end;