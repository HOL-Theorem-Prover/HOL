(* Tests of datatypes with indirect recursion, especially involving basic
   types. Some of these were moved here from selftest to ensure that
   basicSize is loaded and the tests make sense. *)
Theory with_basic_sizes[bare]
Libs
  HolKernel Parse Datatype boolSyntax
  testutils[qualified] basicSize[qualified]

val ERR = mk_HOL_ERR "with_basic_sizes"


(* these are a subset of the tests in datatype selftest.sml, which
   are interesting because they involve the basic types, which are
   installed but missing their size functions in this context

*)

(*
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
*)

val dest_clause = (I##dest_eq) o strip_forall
val clause_rhs = snd o snd o dest_clause
val string_set = HOLset.fromList String.compare

fun check_size_eq ty nms =
 let open HOLset
     val _ = testutils.tprint ("Checking size_eq in " ^ type_to_string ty)
     val expected = string_set nms
     val size_def = snd $ TypeBase.size_of ty
     val clauses = strip_conj (concl size_def)
     val rights = map clause_rhs clauses
     val rhs_consts = rights |> map (find_terms is_const) |> List.concat
     val defset = string_set (map (fst o dest_const) rhs_consts)
 in
   if isSubset (expected,defset) then
      testutils.OK ()
   else raise ERR "check_size_eq"
           (String.concat ("size_def missing constant(s): "
                :: (Lib.commafy $ listItems $ difference (expected,defset))))
 end

(* Tom Ridge's example from 2009/04/23 *)
Datatype:
  command2 =
     Skip2
   | Seq2 of bool # command2 # command2
   | IfThenElse2 of bool # num # command2 # command2
   | While2 of (num # num) # bool # command2
End

val _ = check_size_eq ``: command2`` ["pair_size", "bool_size"]

(* this version raises a different error *)
Datatype:
  tr20090423 =
     trSkip2
   | trSeq2 of bool # tr20090423 # tr20090423
   | trIfThenElse2 of bool # num # tr20090423 # tr20090423
   | trWhile2 of (num # num) # bool # tr20090423
End

val _ = check_size_eq ``: tr20090423`` ["pair_size", "bool_size"]

(* Ramana Kumar's examples from 2010/08/25
   with itself replaced by option to avoid a particular silly issue *)
Datatype: t1 = c1 of 'a => t1 option
End
Datatype: t2 = c2 of t2 t1 option
End

Datatype: u1 = d1 of 'a option
End
Datatype: u2 = d2 of 'a u1
End
Datatype: u3 = d3 of u4 u2 u1 ;
                      u4 = d4 of u3 u1
End

val _ = check_size_eq ``: u3`` ["u1_size", "u2_size"];

Datatype: list = NIL | :: of 'a => list
End

val _ = Datatype `v_rec = V (v_rec + num) | W`

val _ = check_size_eq ``: v_rec`` ["full_sum_size"];

val _ = Datatype`a_rec = A ((a_rec # unit # num option # (unit + num)) list) | B unit`

val _ = check_size_eq ``: a_rec`` ["option_size", "list_size", "one_size"];
