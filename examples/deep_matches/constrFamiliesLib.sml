structure constrFamiliesLib :> constrFamiliesLib =
struct

open HolKernel boolLib simpLib bossLib

(* Contructor families are lists of constructors.
   Constructors are functions that are injective and
   pairwise distinct. Moreover, a case-expansion theorem needs to be provided.

   Let's assume we have a datatype t with
     C1 of bool, C2, C3 of nat. Then we need the following theorems

   !b1 b2. (C1 b1 = C1 b2) <-> (b1 = b2)
   !n1 n2. (C3 n1 = C3 n2) <-> (n1 = n2)
   (!b. not (C1 b = C2))
   (!b. not (C2 = C1 b))
   (!b n. not (C1 b = C3 n))
   (!b n. not (C3 n = C3 b))
   (!n. not (C3 n = C2))
   (!n. not (C2 = C3 n))

   and a case split theorem like

  !f v. f v = (case v of
       C1 b -> f (C1 b)
     | C2 -> f C2
     | C3 n -> f (C3 n))
*)

type constrFamily = {
  constructors  : term list,
  one_one_thm   : thm,
  distinct_thm  : thm,
  case_split_thm: thm
}



fun gen_case_expand_thm case_def_thm nchotomy_thm = let
  val c = fst (
     strip_comb (lhs (snd (strip_forall (hd (strip_conj (concl case_def_thm)))))))
  val (a, cases) = dest_forall (concl nchotomy_thm)

  val res_ty = snd (strip_fun (type_of c))
  val ff_tm = mk_var ("ff", (type_of a) --> res_ty)

  val args = let
    val cases_tms = strip_disj cases
    fun process_case ct = let
      val (vars, b) = strip_exists ct
      val b' = rhs b
    in
      list_mk_abs (vars, (mk_comb (ff_tm, b')))
    end
  in
    map process_case cases_tms
  end

  val t_rhs = list_mk_comb (c, a::args)
  val t_lhs = mk_comb (ff_tm, a)
  val t = list_mk_forall([ff_tm, a], mk_eq (t_lhs, t_rhs))

  val res_thm = prove (t,
    REPEAT GEN_TAC THEN
    MP_TAC (ISPEC a nchotomy_thm) THEN
    SIMP_TAC std_ss [DISJ_IMP_THM, case_def_thm,
      GSYM LEFT_FORALL_IMP_THM])
in
  res_thm
end

fun get_case_expand_thm (v, _) = let
  val ty = type_of v
  val case_def_thm  = TypeBase.case_def_of ty
  val nchotomy_thm = TypeBase.nchotomy_of ty
in
  gen_case_expand_thm case_def_thm nchotomy_thm
end






end
