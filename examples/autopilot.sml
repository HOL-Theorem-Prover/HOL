(*===========================================================================*)
(* Autopilot Specification Example                                           *)
(*                                                                           *)
(* The Hol98 part of an intended comparison between PVS, ACL2 and HOL98.     *)
(* Copyright 1998, Mark Staples                                              *)
(* Modifications (April,June 1998) Konrad Slind.                             *)
(*===========================================================================*)

app load ["bossLib",                (* General reasoning support *)
          "RecordType"              (* Record-style type definitions *)
         ];
				    
open bossLib;  infix &&; 

(*---------------------------------------------------------------------------*
 * We'll track information on inferences.                                    *
 *---------------------------------------------------------------------------*)

val meter = Count.mk_meter();


(*---------------------------------------------------------------------------*
 * Start the theory.                                                         *
 *---------------------------------------------------------------------------*)

val _ = new_theory "Autopilot";


Hol_datatype `events = press_att_cws 
                     | press_cas_eng 
                     | press_alt_eng 
                     | press_fpa_sel
                     | input_alt     
                     | input_fpa
                     | input_cas
                     | alt_reached   
                     | fpa_reached   
                     | alt_gets_near`;


Hol_datatype `off_eng 
                     = off 
                     | engaged`;


Hol_datatype `mode_status 
                     = armed 
                     | Mode of off_eng`;


Hol_datatype `disp_status 
                     = pre_selected 
                     | current`;


Hol_datatype `altitude_vals 
                     = away 
                     | near_pre_selected 
                     | at_pre_selected`;


(*---------------------------------------------------------------------------*
 * State-type projection and update functions.                               *
 *---------------------------------------------------------------------------*)

val {create_fn=create_states, 
  accessor_fns=select_states,
   acc_upd_thm=select_update_states, 
   upd_acc_thm=update_select_states,
 upd_canon_thm=update_canon_states, 
   upd_upd_thm=update_update_states,
    fn_upd_thm=fn_update_states,...} 
  = 
    RecordType.create_record "states"
              [ ("att_cws",  Type`:off_eng`),
                ("cas_eng",  Type`:off_eng`),
                ("fpa_sel",  Type`:off_eng`),
                ("alt_eng",  Type`:mode_status`),
                ("alt_disp", Type`:disp_status`),
                ("fpa_disp", Type`:disp_status`),
                ("cas_disp", Type`:disp_status`),
                ("altitude", Type`:altitude_vals`) ];


(*---------------------------------------------------------------------------*
 * State predicates.                                                         *
 *---------------------------------------------------------------------------*)

val tran_att_cws_def = 
 Define 
     `tran_att_cws st =
        (att_cws st = off 
         => att_cws_update engaged
              (fpa_sel_update off
                (alt_eng_update (Mode off)
                  (fpa_disp_update current 
                     (alt_disp_update current st))))
         | st)`;


val tran_cas_eng_def = 
 Define 
     `tran_cas_eng st =
        (cas_eng st = off 
         => cas_eng_update engaged st
         |  cas_disp_update current (cas_eng_update off st))`;


val tran_fpa_sel_def = 
 Define 
     `tran_fpa_sel st =
        (fpa_sel st = off 
        => fpa_sel_update engaged 
            (att_cws_update off
              (alt_eng_update (Mode off) (alt_disp_update current st)))
        |  fpa_sel_update off 
             (fpa_disp_update current
               (att_cws_update engaged 
                 (alt_eng_update (Mode off) (alt_disp_update current st)))))`;


val tran_alt_eng_def = 
 Define 
     `tran_alt_eng st =
        ((alt_eng st = Mode off) /\ (alt_disp st = pre_selected) 
        => (~(altitude st = away) 
            => att_cws_update off 
                 (fpa_sel_update off
                   (alt_eng_update (Mode engaged) 
                     (fpa_disp_update current st)))
            |  att_cws_update off
                 (fpa_sel_update engaged 
                   (alt_eng_update armed st))
           )
        | st)`;


val tran_input_alt_def = 
 Define 
     `tran_input_alt st =
        (alt_eng st = Mode off 
         => alt_disp_update pre_selected st
         |  ((alt_eng st = armed) \/ (alt_eng st = Mode engaged) 
            => alt_eng_update (Mode off) 
                (alt_disp_update pre_selected
                  (att_cws_update engaged 
                     (fpa_sel_update off (fpa_disp_update current st))))
            |  st))`;
   

val tran_input_fpa_def = 
 Define 
     `tran_input_fpa st =
        (fpa_sel st = off 
         => fpa_disp_update pre_selected st
         |  st)`;


val tran_input_cas_def = 
 Define 
     `tran_input_cas st =
        (cas_eng st = off 
         => cas_disp_update pre_selected st 
         |  st)`;


val tran_alt_gets_near_def = 
 Define 
     `tran_alt_gets_near st =
        (alt_eng st = armed 
         => altitude_update near_pre_selected 
             (alt_eng_update (Mode engaged)
               (fpa_sel_update off 
                 (fpa_disp_update current st)))
         |  altitude_update near_pre_selected st)`;


val tran_alt_reached_def = 
 Define 
     `tran_alt_reached st = 
        (alt_eng st = armed 
         => altitude_update at_pre_selected 
             (alt_disp_update current
               (alt_eng_update (Mode engaged)
                 (fpa_sel_update off 
                   (fpa_disp_update current st))))
         |  altitude_update at_pre_selected 
               (alt_disp_update current st))`;


val tran_fpa_reached_def = 
 Define 
      `tran_fpa_reached st = fpa_disp_update current st`;


val tran_defs = 
  [ tran_att_cws_def, tran_alt_eng_def, tran_fpa_sel_def, tran_cas_eng_def,
    tran_input_alt_def, tran_input_fpa_def, tran_input_cas_def,
    tran_alt_reached_def, tran_fpa_reached_def, tran_alt_gets_near_def];


(*---------------------------------------------------------------------------*
 * The transition function.                                                  *
 *---------------------------------------------------------------------------*)

val nextstate_def = 
  Define
     `(nextstate st press_att_cws = tran_att_cws st)     /\
      (nextstate st press_alt_eng = tran_alt_eng st)     /\
      (nextstate st press_fpa_sel = tran_fpa_sel st)     /\
      (nextstate st press_cas_eng = tran_cas_eng st)     /\
      (nextstate st input_alt     = tran_input_alt st)   /\
      (nextstate st input_fpa     = tran_input_fpa st)   /\
      (nextstate st input_cas     = tran_input_cas st)   /\
      (nextstate st alt_reached   = tran_alt_reached st) /\
      (nextstate st fpa_reached   = tran_fpa_reached st) /\
      (nextstate st alt_gets_near = tran_alt_gets_near st)`;


val st0_def = 
 Define 
    `st0 = states
        (* "att_cws"  *) engaged
        (* "cas_eng"  *) off
        (* "fpa_sel"  *) off
        (* "alt_eng"  *) (Mode off)
        (* "alt_disp" *) current
        (* "fpa_disp" *) current
        (* "cas_disp" *) current
        (* "altitude" *) away`;


val is_initial_def = 
 Define 
     `is_initial st =
         (att_cws st  = engaged)  /\
         (cas_eng st  = off)      /\
         (fpa_sel st  = off)      /\
         (alt_eng st  = Mode off) /\
         (alt_disp st = current)  /\
         (fpa_disp st = current)  /\
         (cas_disp st = current)`;


val valid_state_def = 
 Define 
     `valid_state st =
         ((att_cws st = engaged) 
          \/ (fpa_sel st = engaged) \/ (alt_eng st = Mode engaged))
      /\ (~(alt_eng st = Mode engaged) \/ ~(fpa_sel st = engaged)) 
      /\ ((att_cws st = engaged)
            ==> ~(alt_eng st = Mode engaged) /\ ~(fpa_sel st = engaged))
      /\ ((alt_eng st = armed) ==> (fpa_sel st = engaged))`;



(*---------------------------------------------------------------------------*
 * Proofs. First we build the simplification set. Note that standard         *
 * simplifications arising from datatype definitions get applied             *
 * automatically, and thus can be considered to be in every simplification   *
 * set.                                                                      *
 *---------------------------------------------------------------------------*)

val ap_ss = bool_ss && [nextstate_def, valid_state_def];

val st0_initial = prove (Term`is_initial st0`,
 ZAP_TAC 
    (ap_ss && [is_initial_def,st0_def]) []);


val is_initial_valid_state = prove(Term`is_initial st ==> valid_state st`,
  ZAP_TAC 
    (ap_ss && [is_initial_def]) []);


val st0_valid_state = prove (Term`valid_state st0`,
  ZAP_TAC 
    (ap_ss && [is_initial_valid_state,st0_initial]) []);


(*---------------------------------------------------------------------------*
 * nextstate preserves valid_stateness.                                      *
 * It takes approx. 18 seconds of runtime on 80Meg Pentium 133Mhz.           *
 * Memory consumption is steady at about 10 Mbyte.                           *
 *---------------------------------------------------------------------------*)

val nextstate_valid_state = 
Count.apply prove  
  (Term`!event. valid_state st ==> valid_state (nextstate st event)`,
   Induct 
     THEN ZAP_TAC (ap_ss && tran_defs) []);


(*---------------------------------------------------------------------------*
 * Reachability. This could also be given as an inductive definition.        *
 *---------------------------------------------------------------------------*)

val reachable_in_def = 
 Define
    `(reachable_in 0 st = is_initial st) /\
     (reachable_in (SUC n) st =
        ?pst ev. (st = nextstate pst ev) /\ reachable_in n pst)`;



(*---------------------------------------------------------------------------*
 * Every reachable state is valid_state.                                     *
 *---------------------------------------------------------------------------*)

val reachable_valid_state = prove
 (Term`!n st. reachable_in n st ==> valid_state st`,
  Induct THEN 
   ZAP_TAC (bool_ss && [reachable_in_def])
     [is_initial_valid_state,nextstate_valid_state]);


(*---------------------------------------------------------------------------*
 * A state is reachable if it is reachable in a finite number of steps.      *
 *---------------------------------------------------------------------------*)

val is_reachable_def = Define  `is_reachable st = ?n. reachable_in n st`;

 
val is_reachable_valid_state = prove
(Term`!st. is_reachable st ==> valid_state st`,
  ZAP_TAC bool_ss 
    [is_reachable_def,reachable_valid_state]);


(*---------------------------------------------------------------------------*
 * A couple of safety properties.                                            *
 *---------------------------------------------------------------------------*)

val safety1 = prove
(Term`!event st. 
       valid_state st 
       /\ (fpa_sel st = engaged) 
       /\ (fpa_sel (nextstate st event) = off)
         ==> 
          (fpa_disp (nextstate st event) = current)`,
Induct 
  THEN ZAP_TAC (ap_ss && tran_defs)  (tl (type_rws "off_eng")));


val safety2 = prove
(Term`!event st. 
       valid_state st 
       /\ (alt_eng st = Mode engaged)
       /\ ~(event = input_alt)
       /\ (alt_eng(nextstate st event) = Mode off)
         ==>
          (alt_disp (nextstate st event) = current)`,
Induct 
  THEN ZAP_TAC (ap_ss && tran_defs) 
             (tl(type_rws "off_eng") @ tl(type_rws "mode_status")));


val reachable_induct = prove
(Term`!P. (!st. is_initial st ==> P st) /\ 
          (!st st' e. is_reachable st /\ (st' = nextstate st e) ==> P st')
          ==>
          !st. is_reachable st ==> P st`,
 RW_TAC bool_ss [is_reachable_def]
  THEN Cases_on `n` 
  THEN PROVE_TAC [reachable_in_def]);


val _ = Count.report (Count.read meter);
