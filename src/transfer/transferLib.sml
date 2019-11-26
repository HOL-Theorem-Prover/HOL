structure transferLib :> transferLib =
struct

val PART_MATCH' = mp_then.PART_MATCH'
val op $ = Portable.$

(*
val thm0 = DISCH_ALL fall' |> SIMP_RULE bool_ss [PULL_FORALL]
                    |> SIMP_RULE bool_ss [AND_IMP_INTRO]
val thm = thm0
val tm = “combin$C (==>) ^(mk_var("?A", bool)) (∀s1 s2. s1 ∪ s2 = s2 ∪ s1)”
val leftp = false

val thm = SIMP_RULE std_ss [] thm0
val tm = “(∀s1 s2. s1 ∪ s2 = s2 ∪ s1) ==> ^(mk_var("?A", bool))”
val leftp = true
*)
(* leftp : concrete "input" is left argument to relation *)
fun check_stage1_match thm (tm, leftp ) =
    if leftp then
      PART_MATCH' (lhand o rand) thm (lhand tm)
    else
      let
        val th1 = PART_MATCH' (rand o rand) thm (rand tm)
      in
        PART_MATCH' (rator o rator o rand) th1 (rator (rator tm))
      end


datatype var_flavour = Unification | Constrained
fun flavour_to_pfx Unification = "?" | flavour_to_pfx Constrained = "!"
local
  val c = Counter.make()
in
fun gspec_all flavour th =
    let
      val (vs, bod) = strip_forall $ concl th
      fun foldthis (v, th) =
          let
            val (nm, ty) = dest_var v
          in
            SPEC(mk_var(flavour_to_pfx flavour ^ nm ^ Int.toString (c()), ty))
                th
          end
    in
      List.foldl foldthis th vs
    end
val guspec_all = gspec_all Unification
val gcspec_all = gspec_all Constrained
end

fun is_uvar v = String.sub(v |> dest_var |> #1, 0) = #"?" handle _ => false

(*
val stage1' = check_stage1_match thm (tm, leftp) |> BETA_RULE |> guspec_all

*)

fun new_goals th = th |> dest_imp |> #1 |> strip_conj

(* val new1 = new_goals stage1' *)


fun is_relconstraint t =
    same_const t “left_unique”
fun relconstraint t =
    is_relconstraint (rator t)

val (rcs, others) = List.partition relconstraint new1

fun process_other tm =
    let
      val tm' = tm |> ASSUME |> gcspec_all |> concl
      val (h,c) = dest_imp tm'
    in
      map check_stage1_match ..



end (* struct *)
