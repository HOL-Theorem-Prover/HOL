open HolKernel Parse boolLib bossLib

val _ = new_theory "amba_apb"; 

open boolSyntax;
open bossLib;
open ctl2muTheory;
open cearTools;
open Ho_Rewrite;
open Tactical;
open Tactic;
open PairRules;
open holCheckTools
open bddTools
open ctlTheory
open ctlSyntax
open ksTools


val I1p = Define `INIT_APB (paddr_0:bool,pwrite:bool,psel_0:bool,penable:bool,pdata_0:bool,m_0_0:bool,s_0_0_0:bool) = ~psel_0 /\ ~penable`;

(* TODO: transitions for pdata of the form pdata_0' = ... , so we can use pdata in the defs of m' and s' *)
(* other TODOs: scale, separate read/write buses *)
(* note: pselx is a family signals, where x identifies the slave, so the x is not bits i.e. psel2 is a valid signal *)

val Rm = Define `TRANS_M ((paddr_0:bool,pwrite:bool,psel_0:bool,penable:bool,pdata_0:bool,m_0_0:bool,s_0_0_0:bool),(paddr_0':bool,pwrite':bool,psel_0':bool,penable':bool,pdata_0':bool,m_0_0':bool,s_0_0_0':bool)) = 
  (penable' = psel_0 /\ ~penable) /\
    (pwrite' = psel_0 ==> pwrite) /\
    (paddr_0' = psel_0 ==> paddr_0) /\
    ((psel_0 /\ ~penable) ==> psel_0') /\
    (m_0_0' = if (~pwrite /\ ~paddr_0 /\ psel_0 /\ penable) then s_0_0_0 else m_0_0)`;

val Rs = Define `TRANS_S ((paddr_0:bool,pwrite:bool,psel_0:bool,penable:bool,pdata_0:bool,m_0_0:bool,s_0_0_0:bool),(paddr_0':bool,pwrite':bool,psel_0':bool,penable':bool,pdata_0':bool,m_0_0':bool,s_0_0_0':bool)) = 
    (s_0_0_0' = if (pwrite /\ ~paddr_0 /\ psel_0 /\ penable) then m_0_0 else s_0_0_0) 
`;

 
val R1p = Define `TRANS_APB ((paddr_0:bool,pwrite:bool,psel_0:bool,penable:bool,pdata_0:bool,m_0_0:bool,s_0_0_0:bool),(paddr_0':bool,pwrite':bool,psel_0':bool,penable':bool,pdata_0':bool,m_0_0':bool,s_0_0_0':bool)) = 
^(lhs(concl(Drule.SPEC_ALL Rm)))  /\
^(lhs(concl(Drule.SPEC_ALL Rs)))
`;


val _ = export_theory()