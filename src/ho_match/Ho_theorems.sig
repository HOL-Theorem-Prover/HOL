(* ===================================================================== 
 * FILE          : Ho_theorems.sig                                         
 * DESCRIPTION   : Signature for a collection of tautologies. These are  
 *                 collected in one place and proved uniformly for the   
 *                 first time in hol90. Some are proved much more        
 *                 elegantly in the comments (hol88 code).               
 *                                                                       
 * AUTHORS       : (c) Tom Melham, University of Cambridge, for hol88    
 *                     Konrad Slind, University of Calgary               
 * DATE          : September 11, 1991                                    
 * ADDITIONS     : by RJB, Dec 21, 1992, proved by a uniform tactic now  
 *                 (Konrad Slind)                                        
 * ===================================================================== *)


signature Ho_theorems =
sig
  type thm = Thm.thm

   val BETA_THM : thm                      
   val RIGHT_AND_FORALL_THM : thm          
   val LEFT_AND_EXISTS_THM : thm           
   val LEFT_IMP_EXISTS_THM : thm           
   val TRIV_FORALL_IMP_THM : thm           
   val RIGHT_IMP_FORALL_THM : thm          
   val LEFT_OR_EXISTS_THM : thm            
   val FORALL_AND_THM : thm                
   val RIGHT_AND_EXISTS_THM : thm          
   val RIGHT_FORALL_IMP_THM : thm          
   val RIGHT_EXISTS_AND_THM : thm          
   val OR_EXISTS_THM : thm                 
   val AND_FORALL_THM : thm                
   val TRIV_EXISTS_AND_THM : thm          
   val RIGHT_OR_EXISTS_THM : thm           
   val LEFT_AND_FORALL_THM : thm           
   val EXISTS_OR_THM : thm                 
   val LEFT_EXISTS_AND_THM : thm           
   val TRIV_FORALL_OR_THM : thm            
   val TRIV_AND_EXISTS_THM : thm           
   val TRIV_OR_FORALL_THM : thm            
   val TRIV_EXISTS_IMP_THM : thm           
   val LEFT_FORALL_IMP_THM : thm           

   val EXISTS_REFL : thm                   
   val UNWIND_THM2 : thm                   
   val UNWIND_THM1 : thm                   
   val UNWIND_FORALL_THM2 : thm                   
   val UNWIND_FORALL_THM1 : thm                   
   val SWAP_EXISTS_THM : thm               
   val SWAP_FORALL_THM : thm               

   val MONO_EXISTS : thm                   
   val MONO_AND : thm                      
   val MONO_IMP : thm                      
   val MONO_OR : thm                       
   val MONO_ALL : thm                      
   val MONO_NOT : thm                      

   val EXISTS_UNIQUE_THM : thm		       
   val EXISTS_UNIQUE_ALT : thm             
   val EXISTS_UNIQUE_REFL : thm            


(* from Classical *)

   val LEFT_FORALL_OR_THM : thm  
   val NOT_EXISTS_THM : thm      
   val RIGHT_FORALL_OR_THM : thm 
   val EXCLUDED_MIDDLE : thm     
   val LEFT_OR_FORALL_THM : thm  
   val RIGHT_IMP_EXISTS_THM : thm 
   val EXISTS_NOT_THM : thm       
   val SKOLEM_THM : thm           
   val FUN_EQ_THM : thm           
   val LEFT_IMP_FORALL_THM : thm 
   val LEFT_EXISTS_IMP_THM : thm 
   val FORALL_NOT_THM : thm      
   val NOT_FORALL_THM : thm      
   val RIGHT_OR_FORALL_THM : thm 
   val UNIQUE_SKOLEM_ALT : thm 
   val SELECT_REFL_2 : thm     
   val RIGHT_EXISTS_IMP_THM : thm 
   val UNIQUE_SKOLEM_THM : thm    

   val COND_BOOL_CLAUSES : thm
   val OR_CONG :thm 
   val IMP_CONG : thm            
   val AND_CONG : thm 
   val COND_CONG : thm 

end (* sig *)
