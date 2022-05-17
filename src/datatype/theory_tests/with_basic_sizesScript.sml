(* Tests of datatypes with indirect recursion, especially involving basic
   types. Some of these were moved here from selftest to ensure that
   basicSize is loaded and the tests make sense. *)

open HolKernel Parse Datatype boolSyntax
local open testutils basicSize in end

val _ = new_theory "with_basic_sizes" ;

val ERR = mk_HOL_ERR "with_basic_sizes"


(* these are a subset of the tests in datatype selftest.sml, which
   are interesting because they involve the basic types, which are
   installed but missing their size functions in this context *)

fun check_size_eq ty nms = let
    val _ = testutils.tprint ("Checking size_eq in " ^ type_to_string ty)
    val szs_etc = TypeBase.size_of ty |> snd |> concl |> strip_conj
      |> map (lhs o snd o strip_forall)
      |> map (find_terms is_const) |> List.concat
    val eq_rhss = mapfilter (Conv.TOP_SWEEP_CONV TotalDefn.size_eq_conv) szs_etc
      |> map (rhs o concl)
    fun is_nm nm t = total (fst o dest_const) t = SOME nm
    fun check nm = if List.exists (can (find_term (is_nm nm))) eq_rhss then ()
      else raise ERR "check_size_eq" ("no term named " ^ nm)
    val _ = List.map check nms
  in testutils.OK () end

(* Tom Ridge's example from 2009/04/23 *)
val _ = Hol_datatype `
  command2 =
     Skip2
   | Seq2 of bool # command2 # command2
   | IfThenElse2 of bool # num # command2 # command2
   | While2 of (num # num) # bool # command2
`;

val _ = check_size_eq ``: command2`` ["pair_size", "bool_size"]

(* this version raises a different error *)
val _ = Hol_datatype `
  tr20090423 =
     trSkip2
   | trSeq2 of bool # tr20090423 # tr20090423
   | trIfThenElse2 of bool # num # tr20090423 # tr20090423
   | trWhile2 of (num # num) # bool # tr20090423
`;

val _ = check_size_eq ``: tr20090423`` ["pair_size", "bool_size"]

(* Ramana Kumar's examples from 2010/08/25
   with itself replaced by option to avoid a particular silly issue *)
val _ = Hol_datatype `t1 = c1 of 'a => t1 option `;
val _ = Hol_datatype `t2 = c2 of t2 t1 option ` ;

val _ = Hol_datatype `u1 = d1 of 'a option`;
val _ = Hol_datatype `u2 = d2 of 'a u1 `;
val _ = Hol_datatype `u3 = d3 of u4 u2 u1 ;
                      u4 = d4 of u3 u1 `;

val _ = check_size_eq ``: u3`` ["u1_size", "u2_size", "option_size"];

val _ = Hol_datatype `list = NIL | :: of 'a => list`;

val _ = Datatype `v_rec = V (v_rec + num) | W`

val _ = check_size_eq ``: v_rec`` ["full_sum_size"];

val _ = Datatype`a_rec = A ((a_rec # unit # num option # (unit + num)) list) | B unit`

val _ = check_size_eq ``: a_rec`` ["option_size", "list_size", "one_size"];

val _ = export_theory ();

