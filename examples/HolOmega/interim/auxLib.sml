
structure auxLib = struct

(* strip_left : ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  repeatedly strip off something on the left *)
fun strip_left f th =
  let val (v, th1) = f th ;
    val (vs, thf) = strip_left f th1 ;
  in (v :: vs, thf) end
  handle _ => ([], th) ;

(* strip_right : ('a -> 'a * 'b) -> 'a -> 'a * 'b list
  repeatedly strip off something on the right *)
fun strip_right f th =
  let fun strip_right' (th', vs) =
      let val (th1, v) = f th' in strip_right' (th1, v :: vs) end
      handle _ => (th', vs)
  in strip_right' (th, []) end ;

(* list_mk_left : ('b * 'a -> 'a) -> 'b list * 'a -> 'a
  repeatedly join something on the left *)
fun list_mk_left f ([], th) = th
  | list_mk_left f (v :: vs, th) = f (v, list_mk_left f (vs, th)) ;

(* list_mk_left_cur : ('b -> 'a -> 'a) -> 'b list -> 'a -> 'a
  repeatedly join something on the left, curried *)
fun list_mk_left_cur f [] th = th
  | list_mk_left_cur f (v :: vs) th = f v (list_mk_left_cur f vs th) ;

(* list_mk_right : ('a * 'b -> 'a) -> 'a * 'b list -> 'a
  repeatedly join something on the right *)
fun list_mk_right f (th, []) = th
  | list_mk_right f (th, v :: vs) = list_mk_right f (f (th, v), vs) ;

(* rec2 : ('a -> 'a * 'b) -> 'a -> 'a * 'b list
  repeatedly strip off something on the right *)
fun rec2 f th =
  let fun rec2' (th', vs) =
      let val (th1, v) = f th' in rec2' (th1, v :: vs) end
      handle _ => (th', vs)
  in rec2' (th, []) end ;

(* SPEC_VARL : thm -> term list * thm, like SPECL and SPEC_VAR *)
val SPEC_VARL = strip_left Drule.SPEC_VAR ;
val SPEC_TYVARL = strip_left Drule.SPEC_TYVAR ;

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

(* UNDISCH_TERM : thm -> term * thm
  like UNDISCH, but also returns term *) 
fun UNDISCH_TERM th = 
  let val (hy, _) = boolSyntax.dest_imp (concl th) ;
  in (hy, Drule.UNDISCH th) end ; 

(* UNDISCH_ALL_TERMS : thm -> term list * thm *) 
val UNDISCH_ALL_TERMS = strip_left UNDISCH_TERM ;

(* DISCH_TERMS : term list -> thm -> thm
  DISCH a list of terms *)
val DISCH_TERMS = list_mk_left_cur Thm.DISCH ; 

end ; (* local open HolKernel *)
end ; (* structure auxLib *)

