structure ConstMapML :> ConstMapML = 
struct 

local open boolTheory in end;

open HolKernel Redblackmap;

val ERR = mk_HOL_ERR "ConstMapML";

fun LEX c1 c2 ((x1,x2),(y1,y2)) =
  case c1 (x1,y1)
   of EQUAL => c2 (x2,y2)
    | other => other;

val qmk_vartype = with_flag (Feedback.emit_WARNING,false) mk_vartype;

val eq_alpha = qmk_vartype "''a";

fun unprime s = String.extract(s,1,NONE);

(*---------------------------------------------------------------------------*)
(* The incoming strings are the names of eqtyvars, hence are prefixed with   *)
(* double primes.                                                            *)
(*---------------------------------------------------------------------------*)

fun iconst (slist,n,thy) = 
  inst (List.map (fn s => (mk_vartype (unprime s) |-> qmk_vartype s)) slist)
        (prim_mk_const{Name=n,Thy=thy});

(*---------------------------------------------------------------------------*)
(* The initial constant map has equality, conjunction, disjunction,          *)
(* negation, true, and false in it. The range is triples of the form         *)
(* (structure name,value name, type).                                        *)
(*---------------------------------------------------------------------------*)

type constmap = (term, bool*string*string*hol_type)dict

(*---------------------------------------------------------------------------*)
(* Need to call same_const in order to get the notion of equality desired,   *)
(* otherwise could just use Term.compare.                                    *)
(*---------------------------------------------------------------------------*)

fun compare (c1,c2) = 
   if Term.same_const c1 c2 then EQUAL else Term.compare (c1,c2);

val initConstMap : constmap = mkDict compare

local val equality = prim_mk_const{Name="=",Thy="min"}
      val negation = prim_mk_const{Name="~",Thy="bool"}
      val T        = prim_mk_const{Name="T",Thy="bool"}
      val F        = prim_mk_const{Name="F",Thy="bool"}
      val conj     = prim_mk_const{Name="/\\",Thy="bool"}
      val disj     = prim_mk_const{Name="\\/",Thy="bool"}
in
val ConstMapRef = ref
  (insert(insert(insert(insert(insert(insert
    (initConstMap,
     equality, (false,"","=",    eq_alpha-->eq_alpha-->bool)),
     negation, (false,"","not",  bool-->bool)),
     T,        (false,"","true", bool)),
     F,        (false,"","false",bool)),
     conj,     (false,"","andalso",bool-->bool-->bool)),
     disj,     (false,"","orelse", bool-->bool-->bool)))
end;

fun theConstMap () = !ConstMapRef;

(*---------------------------------------------------------------------------*)
(* Checks for "*" are to avoid situation where prefix multiplication has an  *)
(* open paren just before it ... which is interpreted as beginning of a      *)
(* comment.                                                                  *)
(*---------------------------------------------------------------------------*)

local fun check_name(is_type_cons,Thy,Name,Ty) =
       let val Name' = if String.sub(Name,0) = #"*" orelse
                          String.sub(Name,String.size Name -1) = #"*"
                       then " "^Name^" "
                       else Name
       in (is_type_cons,Thy,Name',Ty)
       end
in
fun prim_insert (c,t) = (ConstMapRef := insert(theConstMap(),c,check_name t))
end;


fun insert c = 
 let val {Name,Thy,Ty} = dest_thy_const c
 in prim_insert(c,(false,Thy,Name,Ty))
 end;

fun insert_cons c = 
 let val {Name,Thy,Ty} = dest_thy_const c
 in prim_insert(c,(true,Thy,Name,Ty))
 end;

fun apply c =
 case peek(theConstMap(),c)
   of SOME triple => triple
    | NONE => let val {Name,Thy,Ty} = dest_thy_const c
              in raise ERR "apply" 
                       ("no binding found for "^Lib.quote(Thy^"$"^Name))
              end

end
