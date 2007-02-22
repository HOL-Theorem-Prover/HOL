(*===========================================================================*)
(* Autopilot Specification Example                                           *)
(*                                                                           *)
(* The Hol98 part of an intended comparison between PVS, ACL2 and HOL98.     *)
(* Copyright 1998, Mark Staples                                              *)
(* Modifications (April,June 1998) Konrad Slind.                             *)
(*===========================================================================*)

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
 * Define state-type projection and update functions.                        *
 *---------------------------------------------------------------------------*)

Hol_datatype `states = <| att_cws  : off_eng;
                          cas_eng  : off_eng;
                          fpa_sel  : off_eng;
                          alt_eng  : mode_status;
                          alt_disp : disp_status;
                          fpa_disp : disp_status;
                          cas_disp : disp_status;
                          altitude : altitude_vals |>`;


(*---------------------------------------------------------------------------*
 * State predicates.                                                         *
 *---------------------------------------------------------------------------*)

val tran_att_cws_def =
 Define
     `tran_att_cws st =
         if st.att_cws = off
         then st with
                 <| att_cws := engaged;
                    fpa_sel := off;
                    alt_eng := Mode off;
                   fpa_disp := current;
                   alt_disp := current|>
         else st`;


val tran_cas_eng_def =
 Define
    `tran_cas_eng st =
        if st.cas_eng = off
          then st with cas_eng := engaged
          else (st with <|cas_disp := current; cas_eng := off|>)`;


val tran_fpa_sel_def =
 Define
    `tran_fpa_sel st =
       if st.fpa_sel = off
       then st with
               <| fpa_sel := engaged;
                  att_cws := off;
                  alt_eng := Mode off;
                 alt_disp := current|>
       else (st with
                <| fpa_sel := off;
                  fpa_disp := current;
                   att_cws := engaged;
                   alt_eng := Mode off;
                  alt_disp := current|>)`;

val tran_alt_eng_def =
 Define
     `tran_alt_eng st =
         if (st.alt_eng = Mode off) /\
            (st.alt_disp = pre_selected)
         then (if ~(st.altitude = away)
               then st with
                       <| att_cws := off;
                          fpa_sel := off;
                          alt_eng := Mode engaged;
                         fpa_disp := current|>
               else (st with
                        <|att_cws := off;
                          fpa_sel := engaged;
                          alt_eng := armed|>))
         else st`;

val tran_input_alt_def =
 Define
     `tran_input_alt st =
         if st.alt_eng = Mode off
         then st with alt_disp := pre_selected
         else if (st.alt_eng = armed) \/ (st.alt_eng = Mode engaged)
              then st with
                    <|alt_eng  := Mode off;
                      alt_disp := pre_selected;
                      att_cws  := engaged;
                      fpa_sel  := off;
                      fpa_disp := current|>
              else st`;

val tran_input_fpa_def =
 Define
     `tran_input_fpa st =
         if st.fpa_sel = off
         then st with fpa_disp := pre_selected
         else st`;


val tran_input_cas_def =
 Define
     `tran_input_cas st =
         if st.cas_eng = off then st with cas_disp := pre_selected else st`;


val tran_alt_gets_near_def =
 Define
     `tran_alt_gets_near st =
         if st.alt_eng = armed
         then st with
                <|altitude := near_pre_selected;
                  alt_eng  := Mode engaged;
                  fpa_sel  := off;
                  fpa_disp := current|>
         else
           (st with altitude := near_pre_selected)`;

val tran_alt_reached_def =
 Define
     `tran_alt_reached st =
        if st.alt_eng = armed
        then st with
              <|altitude := at_pre_selected;
                alt_disp := current;
                alt_eng  := Mode engaged;
                fpa_sel  := off;
                fpa_disp := current|>
        else (st with <|altitude := at_pre_selected; alt_disp := current|>)`;

val tran_fpa_reached_def =
 Define
     `tran_fpa_reached st = (st with fpa_disp := current)`;


val tran_defs =
  [ tran_att_cws_def, tran_alt_eng_def, tran_fpa_sel_def, tran_cas_eng_def,
    tran_input_alt_def, tran_input_fpa_def, tran_input_cas_def,
    tran_alt_reached_def, tran_fpa_reached_def, tran_alt_gets_near_def];


(*---------------------------------------------------------------------------*
 * The transition function.                                                  *
 *---------------------------------------------------------------------------*)

val nextstate_def =
  Define
     `(nextstate st press_att_cws  =  tran_att_cws st)
  /\  (nextstate st press_alt_eng  =  tran_alt_eng st)
  /\  (nextstate st press_fpa_sel  =  tran_fpa_sel st)
  /\  (nextstate st press_cas_eng  =  tran_cas_eng st)
  /\  (nextstate st input_alt      =  tran_input_alt st)
  /\  (nextstate st input_fpa      =  tran_input_fpa st)
  /\  (nextstate st input_cas      =  tran_input_cas st)
  /\  (nextstate st alt_reached    =  tran_alt_reached st)
  /\  (nextstate st fpa_reached    =  tran_fpa_reached st)
  /\  (nextstate st alt_gets_near  =  tran_alt_gets_near st)`;


(*---------------------------------------------------------------------------*
 * Initial state.                                                            *
 *---------------------------------------------------------------------------*)

val st0_def =
 Define
    `st0 = <|att_cws  := engaged;
             cas_eng  := off;
             fpa_sel  := off;
             alt_eng  := Mode off;
             alt_disp := current;
             fpa_disp := current;
             cas_disp := current;
             altitude := away|>`;


val is_initial_def =
 Define
     `is_initial st =
         (st.att_cws = engaged)  /\
         (st.cas_eng = off)      /\
         (st.fpa_sel = off)      /\
         (st.alt_eng = Mode off) /\
         (st.alt_disp = current) /\
         (st.fpa_disp = current) /\
         (st.cas_disp = current)`;


val valid_state_def =
 Define
     `valid_state st =
         ((st.att_cws = engaged) \/ (st.fpa_sel = engaged) \/
          (st.alt_eng = Mode engaged))
     /\  (~(st.alt_eng = Mode engaged) \/ ~(st.fpa_sel = engaged))
     /\  ((st.att_cws = engaged)
           ==> ~(st.alt_eng = Mode engaged) /\
               ~(st.fpa_sel = engaged))
     /\  ((st.alt_eng = armed) ==> (st.fpa_sel = engaged))`;


(*---------------------------------------------------------------------------*
 * Proofs. First we build the simplification set. Note that standard         *
 * simplifications arising from datatype definitions get applied             *
 * automatically, and thus can be considered to be in every simplification   *
 * set.                                                                      *
 *---------------------------------------------------------------------------*)

val ap_ss = std_ss && [nextstate_def, valid_state_def];

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
 * It takes approx. 17 seconds of runtime on 80Meg Pentium 133Mhz.           *
 *---------------------------------------------------------------------------*)

val nextstate_valid_state =
Count.apply prove
  (Term`!event. valid_state st ==> valid_state (nextstate st event)`,
   Cases
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
 * Every reachable state is valid.                                           *
 *---------------------------------------------------------------------------*)

val reachable_valid_state = prove
 (Term`!n st. reachable_in n st ==> valid_state st`,
  Induct THEN
   ZAP_TAC (std_ss && [reachable_in_def])
           [is_initial_valid_state,nextstate_valid_state]);


(*---------------------------------------------------------------------------*
 * A state is reachable if it is reachable in a finite number of steps.      *
 *---------------------------------------------------------------------------*)

val is_reachable_def = Define  `is_reachable st = ?n. reachable_in n st`;


val is_reachable_valid_state = prove
(Term`!st. is_reachable st ==> valid_state st`,
  ZAP_TAC std_ss
    [is_reachable_def,reachable_valid_state]);


(*---------------------------------------------------------------------------*
 * A couple of safety properties.                                            *
 *---------------------------------------------------------------------------*)

val safety1 = prove(Term
`!event st.
     valid_state st
  /\ (st.fpa_sel = engaged)
  /\ ((nextstate st event).fpa_sel = off)
    ==>
     ((nextstate st event).fpa_disp = current)`,
Induct
  THEN ZAP_TAC (ap_ss && tran_defs)  (tl (type_rws ``:off_eng``)));


val safety2 = prove
(Term`!event st.
           valid_state st
        /\ (st.alt_eng = Mode engaged)
        /\ ~(event = input_alt)
        /\ ((nextstate st event).alt_eng = Mode off)
          ==>
           ((nextstate st event).alt_disp = current)`,
Induct
  THEN ZAP_TAC (ap_ss && tran_defs)
             (tl(type_rws ``:off_eng``) @ tl(type_rws ``:mode_status``)));


(*---------------------------------------------------------------------------*
 * Induction for reachable states.                                           *
 *---------------------------------------------------------------------------*)

val reachable_induct = prove
(Term`!P. (!st. is_initial st ==> P st) /\
          (!st e. is_reachable st ==> P (nextstate st e))
          ==>
          !st. is_reachable st ==> P st`,
 RW_TAC std_ss [is_reachable_def]
  THEN Cases_on `n`
  THEN PROVE_TAC [reachable_in_def]);


val _ = Count.report (Count.read meter);
