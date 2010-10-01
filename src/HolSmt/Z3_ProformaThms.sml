(* Copyright (c) 2009-2010 Tjark Weber. All rights reserved. *)

(* Proforma theorems, used for Z3 proof reconstruction *)

structure Z3_ProformaThms =
struct

  fun thm_net_from_list thms =
    List.foldl (fn (th, net) => Net.insert (Thm.concl th, th) net) Net.empty
      thms

local
  open HolSmtTheory
in
  val def_axiom_thms = thm_net_from_list
    [d001, d002, d003, d004, d005, d006, d007, d008, d009, d010, d011, d012,
     d013, d014, d015, d016, d017, d018, d019, d020, d021, d022, d023, d024,
     d025, d026, d027, d028]

  val rewrite_thms = thm_net_from_list
    [r001, r002, r003, r004, r005, r006, r007, r008, r009, r010, r011, r012,
     r013, r014, r015, r016, r017, r018, r019, r020, r021, r022, r023, r024,
     r025, r026, r027, r028, r029, r030, r031, r032, r033, r034, r035, r036,
     r037, r038, r039, r040, r041, r042, r043, r044, r045, r046, r047, r048,
     r049, r050, r051, r052, r053, r054, r055, r056, r057, r058, r059, r060,
     r061, r062, r063, r064, r065, r066, r067, r068, r069, r070, r071, r072,
     r073, r074, r075, r076, r077, r078, r079, r080, r081, r082, r083, r084,
     r085, r086, r087, r088, r089, r090, r091, r092, r093, r094, r095, r096,
     r097, r098, r099, r100, r101, r102, r103, r104, r105, r106, r107, r108,
     r109, r110, r111, r112, r113, r114, r115, r116, r117, r118, r119, r120,
     r121, r122, r123, r124, r125, r126, r127, r128, r129, r130, r131, r132,
     r133, r134, r135, r136, r137, r138, r139, r140, r141, r142, r143, r144,
     r145, r146, r147, r148, r149, r150, r151, r152, r153, r154, r155, r156,
     r157, r158, r159, r160, r161, r162, r163, r164, r165, r166, r167, r168,
     r169, r170, r171, r172, r173, r174, r175, r176, r177, r178, r179, r180,
     r181, r182, r183, r184, r185, r186, r187, r188, r189, r190, r191, r192,
     r193, r194, r195, r196, r197, r198, r199, r200, r201, r202, r203, r204,
     r205, r206, r207, r208, r209, r210, r211, r212, r213, r214, r215, r216,
     r217, r218, r219, r220, r221, r222, r223, r224, r225, r226, r227, r228,
     r229, r230, r231, r232, r233, r234, r235, r236, r237, r238, r239, r240,
     r241, r242, r243, r244, r245, r246, r247, r248, r249, r250, r251, r252,
     r253, r254, r255]

  val th_lemma_thms = thm_net_from_list
    [t001, t002, t003, t004, t005, t006, t007, t008, t009, t010, t011, t012,
     t013, t014, t015, t016, t017, t018, t019, t020, t021, t022, t023, t024,
     t025, t026, t027, t028, t029, t030, t031, t032, t033, t034, t035]

  val prove_hyp_thms = thm_net_from_list
    [p001, p002, p003, p004, p005, p006, p007, p008, p009]
end  (* local *)

  (* finds a matching theorem, instantiates it, attempts to prove all
     hypotheses of the instantiated theorem (by instantiation or
     simplification) *)
  fun prove net t =
    Lib.tryfind
      (fn th =>
        let
          val th = Drule.INST_TY_TERM (Term.match_term (Thm.concl th) t) th
          fun prove_hyp (hyp, th) =
            let
              val hyp_th = prove prove_hyp_thms hyp
                handle Feedback.HOL_ERR _ =>
                  simpLib.SIMP_PROVE (simpLib.++ (bossLib.std_ss,
                    wordsLib.SIZES_ss)) [] hyp
            in
              Drule.PROVE_HYP hyp_th th
            end
        in
          HOLset.foldl prove_hyp th (Thm.hypset th)
        end)
      (Net.match t net)

end
