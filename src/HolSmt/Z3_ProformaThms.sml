(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

(* Proforma theorems, used for Z3 proof reconstruction *)

structure Z3_ProformaThms =
struct

  fun prove net t =
    Lib.tryfind
      (fn th => Drule.INST_TY_TERM (Term.match_term (Thm.concl th) t) th)
      (Net.match t net)

  fun thm_net_from_list thms =
    List.foldl (fn (th, net) => Net.insert (Thm.concl th, th) net) Net.empty
      thms

local
  open HolSmtTheory
in
  val def_axiom_thms = thm_net_from_list
    [th001, th002, th003, th003a, th004, th005, th006, th007, th008, th009, th010, th011,
     th012, th013, th014, th015, th016]

  val rewrite_thms = thm_net_from_list
    [th017, th018, th019, th020, th021, th022, th023, th024, th025, th026, th027, th028,
     th029, th030, th031, th032, th033, th034, th035, th036, th037, th038, th039, th040,
     th041, th042, th043, th044, th045, th046, th047, th048, th049, th050, th051, th052,
     th053, th054, th055, th056, th057, th058, th059, th060, th061, th062, th063, th064,
     th065, th066, th067, th068, th069, th070, th071, th072, th073, th074, th075, th076,
     th077, th078, th079, th080, th081, th082, th083, th084, th085, th086, th087, th088,
     th089, th090, th091, th092, th093, th094, th095, th096, th097, th098, th099, th100,
     th101, th102, th103, th104, th105, th106, th107, th108, th109, th110, th111, th112,
     th113, th114, th115, th116, th117, th118, th119, th120, th121, th122, th123, th124,
     th125, th126, th127, th128, th129, th130, th131, th132, th133, th134, th135, th136,
     th137, th138, th139, th140, th141, th142, th143, th144, th145, th146, th147, th148,
     th149, th150, th151, th152, th153, th154, th155, th156, th157, th158, th159, th160,
     th161, th162, th163, th164, th165, th166, th167, th168, th169, th170, th171, th172,
     th173, th174, th175, th176, th177, th178, th179, th180, th181, th182, th183, th184,
     th185, th186, th187, th188, th189, th190, th191, th192, th193, th194, th195, th196,
     th197, th198, th199, th200, th201, th202, th203, th204, th205, th206, th207, th208,
     th209, th210, th211, th212, th213, th214, th215, th216, th217, th218, th219, th220,
     th221, th222, th223, th224, th225, th226, th227]

  val th_lemma_thms = thm_net_from_list
    [th228, th229, th230, th231, th232, th233, th234, th235, th236, th237, th238]
end  (* local *)

end
