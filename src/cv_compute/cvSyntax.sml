structure cvSyntax :> cvSyntax =
struct

  open HolKernel Abbrev;
  open cvTheory;

  val ERR = mk_HOL_ERR "cvSyntax";
  val WARN = HOL_WARNING "cvSyntax";

(* -------------------------------------------------------------------------
 * Constants
 * ------------------------------------------------------------------------- *)

  val cv = mk_thy_type {Thy = "cv", Tyop = "cv", Args = []};

  val cv_pair_tm = prim_mk_const {Name="Pair", Thy="cv"};
  val cv_num_tm = prim_mk_const {Name="Num", Thy="cv"};
  val cv_fst_tm = prim_mk_const {Name="cv_fst", Thy="cv"};
  val cv_snd_tm = prim_mk_const {Name="cv_snd", Thy="cv"};
  val cv_ispair_tm = prim_mk_const {Name="cv_ispair", Thy="cv"};
  val cv_add_tm = prim_mk_const {Name="cv_add", Thy="cv"};
  val cv_sub_tm = prim_mk_const {Name="cv_sub", Thy="cv"};
  val cv_mul_tm = prim_mk_const {Name="cv_mul", Thy="cv"};
  val cv_div_tm = prim_mk_const {Name="cv_div", Thy="cv"};
  val cv_mod_tm = prim_mk_const {Name="cv_mod", Thy="cv"};
  val cv_lt_tm = prim_mk_const {Name="cv_lt", Thy="cv"};
  val cv_if_tm = prim_mk_const {Name="cv_if", Thy="cv"};
  val cv_eq_tm = prim_mk_const {Name="cv_eq", Thy="cv"};
  val safediv_tm = prim_mk_const {Name="SAFEDIV", Thy="cv"};
  val safemod_tm = prim_mk_const {Name="SAFEMOD", Thy="cv"};

(* -------------------------------------------------------------------------
 * Constructors
 * ------------------------------------------------------------------------- *)

  fun mk_monop f t = mk_comb (f, t);
  fun mk_binop f (s, t) = mk_comb (mk_comb (f, s), t);
  fun mk_triop f (s, t, u) = mk_comb (mk_comb (mk_comb (f, s), t), u);

  val mk_cv_pair   = mk_binop cv_pair_tm;
  val mk_cv_num    = mk_monop cv_num_tm;
  val mk_cv_fst    = mk_monop cv_fst_tm;
  val mk_cv_snd    = mk_monop cv_snd_tm;
  val mk_cv_ispair = mk_monop cv_ispair_tm;
  val mk_cv_add    = mk_binop cv_add_tm;
  val mk_cv_sub    = mk_binop cv_sub_tm;
  val mk_cv_mul    = mk_binop cv_mul_tm;
  val mk_cv_div    = mk_binop cv_div_tm;
  val mk_cv_mod    = mk_binop cv_mod_tm;
  val mk_cv_lt     = mk_binop cv_lt_tm;
  val mk_cv_if     = mk_triop cv_if_tm;
  val mk_cv_eq     = mk_binop cv_eq_tm;
  val mk_safediv   = mk_monop safediv_tm;
  val mk_safemod   = mk_monop safemod_tm;

(* -------------------------------------------------------------------------
 * Destructors
 * ------------------------------------------------------------------------- *)

  fun dest_monop f tm =
    let
      val (g, x) = dest_comb tm
    in
      if same_const f g then x else raise ERR "" ""
    end;

  fun dest_binop f tm =
    let
      val (gx, y) = dest_comb tm
      val (g, x) = dest_comb gx
    in
      if same_const f g then (x, y) else raise ERR "" ""
    end;


  fun dest_triop f tm =
    let
      val (gxy, z) = dest_comb tm
      val (gx, y) = dest_comb gxy
      val (g, x) = dest_comb gx
    in
      if same_const f g then (x, y, z) else raise ERR "" ""
    end;

  val dest_cv_pair   = dest_binop cv_pair_tm;
  val dest_cv_num    = dest_monop cv_num_tm;
  val dest_cv_fst    = dest_monop cv_fst_tm;
  val dest_cv_snd    = dest_monop cv_snd_tm;
  val dest_cv_ispair = dest_monop cv_ispair_tm;
  val dest_cv_add    = dest_binop cv_add_tm;
  val dest_cv_sub    = dest_binop cv_sub_tm;
  val dest_cv_mul    = dest_binop cv_mul_tm;
  val dest_cv_div    = dest_binop cv_div_tm;
  val dest_cv_mod    = dest_binop cv_mod_tm;
  val dest_cv_lt     = dest_binop cv_lt_tm;
  val dest_cv_if     = dest_triop cv_if_tm;
  val dest_cv_eq     = dest_binop cv_eq_tm;
  val dest_safediv   = dest_binop safediv_tm;
  val dest_safemod   = dest_binop safemod_tm;

(* -------------------------------------------------------------------------
 * Recognizers
 * ------------------------------------------------------------------------- *)

  val is_cv_pair   = can (dest_binop cv_pair_tm);
  val is_cv_num    = can (dest_monop cv_num_tm);
  val is_cv_fst    = can (dest_monop cv_fst_tm);
  val is_cv_snd    = can (dest_monop cv_snd_tm);
  val is_cv_ispair = can (dest_monop cv_ispair_tm);
  val is_cv_add    = can (dest_binop cv_add_tm);
  val is_cv_sub    = can (dest_binop cv_sub_tm);
  val is_cv_mul    = can (dest_binop cv_mul_tm);
  val is_cv_div    = can (dest_binop cv_div_tm);
  val is_cv_mod    = can (dest_binop cv_mod_tm);
  val is_cv_lt     = can (dest_binop cv_lt_tm);
  val is_cv_if     = can (dest_triop cv_if_tm);
  val is_cv_eq     = can (dest_binop cv_eq_tm);
  val is_safediv   = can (dest_binop safediv_tm);
  val is_safemod   = can (dest_binop safemod_tm);

end (* struct *)

