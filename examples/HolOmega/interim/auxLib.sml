
structure auxLib = struct

(* rec1 : ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  repeatedly strip off something on the left *)
fun rec1 f th =
  let val (v, th1) = f th ;
    val (vs, thf) = rec1 f th1 ;
  in (v :: vs, thf) end
  handle _ => ([], th) ;

(* rec2 : ('a -> 'a * 'b) -> 'a -> 'a * 'b list
  repeatedly strip off something on the right *)
fun rec2 f th =
  let fun rec2' (th', vs) =
      let val (th1, v) = f th' in rec2' (th1, v :: vs) end
      handle _ => (th', vs)
  in rec2' (th, []) end ;

(* SPEC_VARL : thm -> term list * thm, like SPECL and SPEC_VAR *)
val SPEC_VARL = rec1 Drule.SPEC_VAR ;
val SPEC_TYVARL = rec1 Drule.SPEC_TYVAR ;

local open HolKernel in 

(* sfg : (thm -> thm) -> thm -> thm
  remove universal quantifiers, apply f, add quantifiers back *)
fun sfg f thm = 
  let val (vars, sthm) = SPEC_VARL thm ;
  in GENL vars (f sthm) end ;

(* tsfg : (thm -> thm) -> thm -> thm
  remove type universal quantifiers, apply f, add quantifiers back *)
fun tsfg f thm =
  let val (tyvars, sthm) = SPEC_TYVARL thm ;
  in Drule.TY_GENL tyvars (f sthm) end ;

(* ufd : (thm -> thm) -> thm -> thm
  removes implication antecedents, apply f, restores antecedents,
  assumes thm has no assumptions *)
fun ufd f thm = Drule.DISCH_ALL (f (Drule.UNDISCH_ALL thm)) ;

end ; (* local open HolKernel *)
end ; (* structure auxLib *)

