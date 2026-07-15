(* Core Refute definitions land in subsequent M1 tasks. *)
structure Refute_Core = struct
  val refute_simp =
    ThmSetData.export_list {settype = "refute_simp", initial = []}

  val refute_psimp =
    ThmSetData.export_list {settype = "refute_psimp", initial = []}

  val refute_unfold =
    ThmSetData.export_list {settype = "refute_unfold", initial = []}

  val placeholder = ()
end
