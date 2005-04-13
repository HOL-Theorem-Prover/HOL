
(*****************************************************************************)
(* Theorems for word32 values needed for compile Fact32 example.             *)
(*****************************************************************************)


 
(*****************************************************************************) 
(* START BOILERPLATE                                                         *) 
(*****************************************************************************) 
(****************************************************************************** 
* Load theories 
******************************************************************************) 
(* 
quietdec := true;
loadPath := "../" :: "word32" :: "../dff/" :: !loadPath;
map load
 ["compileTheory","compile","metisLib","intLib","word32Theory",
  "dffTheory","vsynth"];
open compile metisLib word32Theory;
open arithmeticTheory intLib pairLib pairTheory PairRules combinTheory
     devTheory composeTheory compileTheory compile vsynth 
     dffTheory tempabsTheory;
val _ = intLib.deprecate_int();
val _ = (if_print_flag := false);
quietdec := false;
*) 
 
(****************************************************************************** 
* Boilerplate needed for compilation 
******************************************************************************) 

(****************************************************************************** 
* Open theories 
******************************************************************************) 
open HolKernel Parse boolLib bossLib; 
open compile metisLib word32Theory;
open arithmeticTheory intLib pairLib pairTheory PairRules combinTheory
     devTheory composeTheory compileTheory compile vsynth 
     dffTheory tempabsTheory;
 
(****************************************************************************** 
* Set default parsing to natural numbers rather than integers 
******************************************************************************) 
val _ = intLib.deprecate_int(); 
 
(*****************************************************************************) 
(* END BOILERPLATE                                                           *) 
(*****************************************************************************) 

(*****************************************************************************) 
(* Start new theory "compile32"                                              *) 
(*****************************************************************************) 
val _ = new_theory "compile32"; 

(*****************************************************************************)
(* 32-bit combinational components                                           *)
(*****************************************************************************) 
val ADD_def = 
 Define 
  `ADD(in1,in2,out) = !t. out t = in1 t + in2 t`; 
 
val COMB_ADD = 
 store_thm 
  ("COMB_ADD", 
   ``COMB (UNCURRY $+) (in1 <> in2, out) = ADD(in1,in2,out)``, 
   RW_TAC std_ss [COMB_def,BUS_CONCAT_def,ADD_def]); 
 
val SUB_def = 
 Define 
  `SUB(in1,in2,out) = !t. out t = in1 t - in2 t`; 
 
val COMB_SUB = 
 store_thm 
  ("COMB_SUB", 
   ``COMB (UNCURRY $-) (in1 <> in2, out) = SUB(in1,in2,out)``, 
   RW_TAC std_ss [COMB_def,BUS_CONCAT_def,SUB_def]); 
 
val EQ_def = 
 Define 
  `EQ(in1:num->word32,in2:num->word32,out) = !t. out t = (in1 t = in2 t)`; 
 
val COMB_EQ = 
 store_thm 
  ("COMB_EQ", 
   ``COMB (UNCURRY $=) (in1 <> in2, out) = EQ(in1,in2,out)``, 
   RW_TAC std_ss [COMB_def,BUS_CONCAT_def,EQ_def]); 
 
val LESS_def = 
 Define 
  `LESS(in1,in2,out) = !t. out t = in1 t < in2 t`; 
 
val COMB_LESS = 
 store_thm 
  ("COMB_LESS", 
   ``COMB (UNCURRY $<) (in1 <> in2, out) = LESS(in1,in2,out)``, 
   RW_TAC std_ss [COMB_def,BUS_CONCAT_def,LESS_def]); 
 
(*****************************************************************************)
(* Temporal abstraction theorems                                             *)
(*****************************************************************************)
val EQ_at = 
 store_thm 
  ("EQ_at", 
   ``EQ(in1,in2,out)  
     ==>  
     EQ(in1 at clk,in2 at clk,out at clk)``, 
   RW_TAC std_ss [EQ_def,at_def,when]); 
 
val ADD_at = 
 store_thm 
  ("ADD_at", 
   ``ADD(in1,in2,out)  
     ==>  
     ADD(in1 at clk,in2 at clk,out at clk)``, 
   RW_TAC std_ss [ADD_def,at_def,when]); 
 
val SUB_at = 
 store_thm 
  ("SUB_at", 
   ``SUB(in1,in2,out)  
     ==>  
     SUB(in1 at clk,in2 at clk,out at clk)``, 
   RW_TAC std_ss [SUB_def,at_def,when]); 
 
val LESS_at = 
 store_thm 
  ("LESS_at", 
   ``LESS(in1,in2,out)  
     ==>  
     LESS(in1 at clk,in2 at clk,out at clk)``, 
   RW_TAC std_ss [LESS_def,at_def,when]); 
 
val _ = export_theory();
