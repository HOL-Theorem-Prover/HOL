structure PairedDefinition = 
struct
 
local open HolKernel boolLib PairedLambda pairSyntax

infix ORELSEC;

val ERR = mk_HOL_ERR "PairedDefinition";

(*---------------------------------------------------------------------------
     Lifting primitive definition principle to understand varstruct
     arguments in definitions.
 ---------------------------------------------------------------------------*)

fun inter s1 [] = []
  | inter s1 (h::t) = case intersect s1 h of [] => inter s1 t | X => X

fun joint_vars []  = []
  | joint_vars [_] = []
  | joint_vars (h::t) = case inter h t of [] => joint_vars t | X => X;

fun dest t = 
  let val (lhs,rhs) = dest_eq (snd(strip_forall t))
      val (f,args) = strip_comb lhs
  in 
  case gather (not o is_vstruct) args 
   of [] => (case joint_vars (map free_vars args)
              of [] => (args, mk_eq(f,list_mk_pabs(args,rhs)))
               | V  => raise ERR "new_definition" (String.concat
                       ("shared variables between arguments: " ::
                        commafy (map Parse.term_to_string V))))
    | tml => raise ERR "new_definition" (String.concat
             ("The following arguments are not varstructs: "::
              commafy (map Parse.term_to_string tml)))
  end;

fun RHS_CONV conv th = TRANS th (conv(rhs(concl th)));

fun add_varstruct v th = 
  RHS_CONV(BETA_CONV ORELSEC PAIRED_BETA_CONV) (AP_THM th v)

fun post (V,th) =
  let val cname = fst(dest_const(lhs(concl th)))
      val vars = List.concat (map free_vars_lr V)
  in Parse.add_const cname;
     itlist GEN vars (rev_itlist add_varstruct V th)
  end;
  
val _ = Definition.new_definition_hook := (dest, post)

in end;

end
