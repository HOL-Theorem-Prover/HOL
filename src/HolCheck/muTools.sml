(*List.app load ["bossLib","stringTheory","stringLib","HolBddLib","pairTheory","pred_setLib","listLib","CTL","pairSyntax","pairRules","pairTools","muTheory","boolSyntax","Drule","Tactical","Conv","Rewrite","Tactic","boolTheory"];*)

structure muTools =
struct

local

open Globals HolKernel Parse goalstackLib;

open bossLib;
open pairTheory;
open pred_setTheory;
open pred_setLib;
open stringLib;
open listTheory;
open simpLib;
open pairSyntax;
open pairLib;
open PrimitiveBddRules;
open DerivedBddRules;
open Binarymap;
open PairRules;
open pairTools;
open setLemmasTheory;
open muSyntax
open muSyntaxTheory;
open muTheory;
open boolSyntax;
open Drule;
open Tactical;
open Conv;
open Rewrite;
open Tactic;
open boolTheory;
open listSyntax;
open stringTheory;
open stringBinTree;
open boolSimps;
open pureSimps;
open listSimps;
open numLib;
open reachTheory;
open bddTools
open envTheory
open envTools

in

fun mk_imf_thm mf  (tysimps,seths) prop_type = prove(``IMF (^mf)``,
						     SIMP_TAC std_ss ([IMF_def,MU_SUB_def,NNF_def,RVNEG_def]@tysimps@seths))

(* FIXME: in many places, awkward use of BddEqMp can be replaced by cleaner eqToTermBdd *)  
end
end
