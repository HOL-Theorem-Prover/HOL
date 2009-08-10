(* Interactive use

  app load ["Omega_AutomataTheory", "numLib"];
  open Rsyntax

*)
structure temporalLib :> temporalLib =
struct

(*---------------------------------------------------------------------------
   Note (kxs): the pathname and file handling in this file should be
               made portable.
 ---------------------------------------------------------------------------*)

val smv_tmp_dir = ref "/tmp/";
val smv_path    = ref (Path.concat(Globals.HOLDIR,"sigobj/"));
val smv_call    = ref "smv.xable -r -v -f ";


open HolKernel Parse boolLib Rsyntax;

infixr 3 -->;
infix ## |-> THEN THENL THENC ORELSE ORELSEC THEN_TCL ORELSE_TCL;

local open Omega_AutomataTheory in end;

local  (* Fix the grammar used by this file *)
  val ambient_grammars = Parse.current_grammars();
  val _ = Parse.temp_set_grammars Omega_AutomataTheory.Omega_Automata_grammars
in

type smv_output =
	{Proved:bool,
	 Init_Sequence:(string list * string list) list,
	 Loop_Sequence:(string list * string list) list,
	 Resources:string list}


datatype temp_formula =
	truesig |
	falsesig |
	var of string |
	neg of temp_formula |
	conj of (temp_formula * temp_formula) |
	disj of (temp_formula * temp_formula) |
	imp  of (temp_formula * temp_formula) |
	equ  of (temp_formula * temp_formula) |
	ifte of (temp_formula * temp_formula * temp_formula) |
	next of temp_formula |
	always of temp_formula |
	eventual of temp_formula |
	when of (temp_formula * temp_formula) |
	swhen of (temp_formula * temp_formula) |
	until of (temp_formula * temp_formula) |
	suntil of (temp_formula * temp_formula) |
	befor of (temp_formula * temp_formula) |
	sbefor of (temp_formula * temp_formula) |
	pnext of temp_formula |
	psnext of temp_formula |
	palways of temp_formula |
	peventual of temp_formula |
	pwhen of (temp_formula * temp_formula) |
	pswhen of (temp_formula * temp_formula) |
	puntil of (temp_formula * temp_formula) |
	psuntil of (temp_formula * temp_formula) |
	pbefor of (temp_formula * temp_formula) |
	psbefor of (temp_formula * temp_formula);





(* ****************************************************************************	*)
(* Converting functions: hol2temporal & temporal2hol				*)
(* ****************************************************************************	*)

val thetrue   = T
val thefalse  = F
val NEXT      = Term`NEXT`
val ALWAYS    = Term`ALWAYS`
val EVENTUAL  = Term`EVENTUAL`
val PNEXT     = Term`PNEXT`
val PSNEXT    = Term`PSNEXT`
val PALWAYS   = Term`PALWAYS`
val PEVENTUAL = Term`PEVENTUAL`
val WHEN      = Term`$WHEN`
val UNTIL     = Term`$UNTIL`
val BEFORE    = Term`$BEFORE`
val SWHEN     = Term`$SWHEN`
val SUNTIL    = Term`$SUNTIL`
val SBEFORE   = Term`$SBEFORE`
val PWHEN     = Term`$PWHEN`
val PUNTIL    = Term`$PUNTIL`
val PBEFORE   = Term`$PBEFORE`
val PSWHEN    = Term`$PSWHEN`
val PSUNTIL   = Term`$PSUNTIL`
val PSBEFORE  = Term`$PSBEFORE`

fun hol2temporal t =
  if t=thetrue then truesig else if t=thefalse then falsesig
  else
    (let val {Name=n,Ty=typ} = dest_var t
      in var(n)
     end)
  handle _=> (* --------------------- signal abstraction ------------------------------	*)
    (let val {Bvar=v,Body=b} = dest_abs t
	 val {Name=n,Ty=_} = dest_var v
      in (hol2temporal b)
     end)
  handle _=> (* ------ propositional or temporal operator or signal evalutation -------	*)
    (let val t1 = dest_neg t
      in neg(hol2temporal t1)
     end)
  handle _=>
    (let val {conj1=t1,conj2=t2} = dest_conj t
      in conj((hol2temporal t1),(hol2temporal t2))
     end)
  handle _=>
    (let val {disj1=t1,disj2=t2} = dest_disj t
      in disj((hol2temporal t1),(hol2temporal t2))
     end)
  handle _=>
    (let val {ant=t1,conseq=t2} = dest_imp t
      in imp((hol2temporal t1),(hol2temporal t2))
     end)
  handle _=>
    (let val {lhs=t1,rhs=t2} = dest_eq t
      in equ((hol2temporal t1),(hol2temporal t2))
     end)
  handle _=>
    (let val {cond=t1,larm=t2,rarm=t3} = dest_cond t
      in ifte((hol2temporal t1),(hol2temporal t2),(hol2temporal t3))
     end)
  handle _=> 		      (* ------ temporal operator or signal evalutation -------	*)
    (let val {Rator=f,Rand=x} = dest_comb t
      in if f=NEXT then next(hol2temporal x)
	 else if f=ALWAYS then always(hol2temporal x)
	 else if f=EVENTUAL then eventual(hol2temporal x)
	 else if f=PNEXT then pnext(hol2temporal x)
	 else if f=PSNEXT then psnext(hol2temporal x)
	 else if f=PALWAYS then palways(hol2temporal x)
	 else if f=PEVENTUAL then peventual(hol2temporal x)
	 else      (* -------- binary temporal operator or signal evalutation ---------	*)
	    let val {Rator=temp_op,Rand=b} = dest_comb f
	     in if temp_op = WHEN then
			when((hol2temporal b),(hol2temporal x))
		else if temp_op = UNTIL then
			until((hol2temporal b),(hol2temporal x))
		else if temp_op = BEFORE then
			befor((hol2temporal b),(hol2temporal x))
		else if temp_op = SWHEN then
			swhen((hol2temporal b),(hol2temporal x))
		else if temp_op = SUNTIL then
			suntil((hol2temporal b),(hol2temporal x))
		else if temp_op = SBEFORE then
			sbefor((hol2temporal b),(hol2temporal x))
		else if temp_op = PWHEN then
			pwhen((hol2temporal b),(hol2temporal x))
		else if temp_op = PUNTIL then
			puntil((hol2temporal b),(hol2temporal x))
		else if temp_op = PBEFORE then
			pbefor((hol2temporal b),(hol2temporal x))
		else if temp_op = PSWHEN then
			pswhen((hol2temporal b),(hol2temporal x))
		else if temp_op = PSUNTIL then
			psuntil((hol2temporal b),(hol2temporal x))
		else if temp_op = PSBEFORE then
			psbefor((hol2temporal b),(hol2temporal x))
		else (hol2temporal f)
	    end
	  handle _=> (hol2temporal f)
     end)




fun temporal2hol truesig  = (--`\t:num.T`--)
  | temporal2hol falsesig = (--`\t:num.F`--)
  | temporal2hol (var(x)) = mk_var{Name=x,Ty=(==`:num->bool`==)}
  | temporal2hol (neg f)  =
	let val t = temporal2hol f in (--`\t:num. ~^t t`--) end
  | temporal2hol (conj(f1,f2)) =
	let
	   val t1 = temporal2hol f1
	   val t2 = temporal2hol f2
	 in (--`\t:num. ^t1 t /\ ^t2 t`--)
	end
  | temporal2hol (disj(f1,f2)) =
	let
	   val t1 = temporal2hol f1
	   val t2 = temporal2hol f2
	 in (--`\t:num. ^t1 t \/ ^t2 t`--)
	end
  | temporal2hol (imp(f1,f2)) =
	let
	   val t1 = temporal2hol f1
	   val t2 = temporal2hol f2
	 in (--`\t:num. ^t1 t ==> ^t2 t`--)
	end
  | temporal2hol (equ(f1,f2)) =
	let
	   val t1 = temporal2hol f1
	   val t2 = temporal2hol f2
	 in (--`\t:num. ^t1 t = ^t2 t`--)
	end
  | temporal2hol (ifte(f1,f2,f3)) =
	let
	   val t1 = temporal2hol f1
	   val t2 = temporal2hol f2
	   val t3 = temporal2hol f3
	 in (--`\t:num. ^t1 t => ^t2 t | ^t3 t `--)
	end
  | temporal2hol (next f) =
	mk_comb{Rator=NEXT,Rand=(temporal2hol f)}
  | temporal2hol (always f) =
	mk_comb{Rator=ALWAYS,Rand=(temporal2hol f)}
  | temporal2hol (eventual f) =
	mk_comb{Rator=EVENTUAL,Rand=(temporal2hol f)}
  | temporal2hol (pnext f) =
	mk_comb{Rator=PNEXT,Rand=(temporal2hol f)}
  | temporal2hol (psnext f) =
	mk_comb{Rator=PSNEXT,Rand=(temporal2hol f)}
  | temporal2hol (palways f) =
	mk_comb{Rator=PALWAYS,Rand=(temporal2hol f)}
  | temporal2hol (peventual f) =
	mk_comb{Rator=PEVENTUAL,Rand=(temporal2hol f)}
  | temporal2hol (when(x,b)) =
	mk_comb{Rator=mk_comb{Rator=WHEN,Rand=(temporal2hol x)},
		Rand=(temporal2hol b)}
  | temporal2hol (until(x,b)) =
	mk_comb{Rator=mk_comb{Rator=UNTIL,Rand=(temporal2hol x)},
		Rand=(temporal2hol b)}
  | temporal2hol (befor(x,b)) =
	mk_comb{Rator=mk_comb{Rator=BEFORE,Rand=(temporal2hol x)},
		Rand=(temporal2hol b)}
  | temporal2hol (swhen(x,b)) =
	mk_comb{Rator=mk_comb{Rator=SWHEN,Rand=(temporal2hol x)},
		Rand=(temporal2hol b)}
  | temporal2hol (suntil(x,b)) =
	mk_comb{Rator=mk_comb{Rator=SUNTIL,Rand=(temporal2hol x)},
		Rand=(temporal2hol b)}
  | temporal2hol (sbefor(x,b)) =
	mk_comb{Rator=mk_comb{Rator=SBEFORE,Rand=(temporal2hol x)},
		Rand=(temporal2hol b)}
  | temporal2hol (pwhen(x,b)) =
	mk_comb{Rator=mk_comb{Rator=PWHEN,Rand=(temporal2hol x)},
		Rand=(temporal2hol b)}
  | temporal2hol (puntil(x,b)) =
	mk_comb{Rator=mk_comb{Rator=PUNTIL,Rand=(temporal2hol x)},
		Rand=(temporal2hol b)}
  | temporal2hol (pbefor(x,b)) =
	mk_comb{Rator=mk_comb{Rator=PBEFORE,Rand=(temporal2hol x)},
		Rand=(temporal2hol b)}
  | temporal2hol (pswhen(x,b)) =
	mk_comb{Rator=mk_comb{Rator=PSWHEN,Rand=(temporal2hol x)},
		Rand=(temporal2hol b)}
  | temporal2hol (psuntil(x,b)) =
	mk_comb{Rator=mk_comb{Rator=PSUNTIL,Rand=(temporal2hol x)},
		Rand=(temporal2hol b)}
  | temporal2hol (psbefor(x,b)) =
	mk_comb{Rator=mk_comb{Rator=PSBEFORE,Rand=(temporal2hol x)},
		Rand=(temporal2hol b)}






(* ****************************************************************************	*)
(* 		Computing the the names of the variables 			*)
(* ****************************************************************************	*)

fun var_names truesig          = []
  | var_names falsesig         = []
  | var_names (var(x))         = [x]
  | var_names (neg f)          = var_names f
  | var_names (conj(f1,f2))    = (var_names f1)@(var_names f2)
  | var_names (disj(f1,f2))    = (var_names f1)@(var_names f2)
  | var_names (imp(f1,f2))     = (var_names f1)@(var_names f2)
  | var_names (equ(f1,f2))     = (var_names f1)@(var_names f2)
  | var_names (ifte(f1,f2,f3)) = (var_names f1)@(var_names f2)@(var_names f3)
  | var_names (next f)         = var_names f
  | var_names (always f)       = var_names f
  | var_names (eventual f)     = var_names f
  | var_names (when(x,b))      = (var_names x)@(var_names b)
  | var_names (until(x,b))     = (var_names x)@(var_names b)
  | var_names (befor(x,b))     = (var_names x)@(var_names b)
  | var_names (swhen(x,b))     = (var_names x)@(var_names b)
  | var_names (suntil(x,b))    = (var_names x)@(var_names b)
  | var_names (sbefor(x,b))    = (var_names x)@(var_names b)
  | var_names (pnext f)        = var_names f
  | var_names (psnext f)       = var_names f
  | var_names (palways f)      = var_names f
  | var_names (peventual f)    = var_names f
  | var_names (pwhen(x,b))     = (var_names x)@(var_names b)
  | var_names (puntil(x,b))    = (var_names x)@(var_names b)
  | var_names (pbefor(x,b))    = (var_names x)@(var_names b)
  | var_names (pswhen(x,b))    = (var_names x)@(var_names b)
  | var_names (psuntil(x,b))   = (var_names x)@(var_names b)
  | var_names (psbefor(x,b))   = (var_names x)@(var_names b)




(* ****************************************************************************	*)
(*			Generating new variable names				*)
(* ****************************************************************************	*)

fun new_sig_var name fb index =
    let val n = name^(int_to_string index)
     in if mem n fb then new_sig_var name fb (index+1)
	else n
    end



(* *********************** tsubst & temp_subst ********************************	*)
(* tsubst v x t replaces each occurence of v by x in the formula t (v need	*)
(* not be a variable). The function temp_subst is a multiple replacement, where	*)
(* the replacement is not done simulaneously. The function def_subst is a 	*)
(* special variant that is needed in the tableau construction below.		*)
(* ****************************************************************************	*)

fun tsubst v x t =
    if v=t then x else
      case t of
	  falsesig 	 => falsesig
	| truesig 	 => truesig
	| var(n) 	 => var(n)
	| neg f 	 => neg(tsubst v x f)
	| conj(f1,f2)  	 => conj(tsubst v x f1,tsubst v x f2)
	| disj(f1,f2) 	 => disj(tsubst v x f1,tsubst v x f2)
	| imp(f1,f2) 	 => imp(tsubst v x f1,tsubst v x f2)
	| equ(f1,f2) 	 => equ(tsubst v x f1,tsubst v x f2)
	| ifte(f1,f2,f3) => ifte(tsubst v x f1,tsubst v x f2,tsubst v x f3)
	| next f 	 => next(tsubst v x f)
	| always f 	 => always(tsubst v x f)
	| eventual f 	 => eventual(tsubst v x f)
	| when(f1,f2)  	 => when(tsubst v x f1,tsubst v x f2)
	| until(f1,f2) 	 => until(tsubst v x f1,tsubst v x f2)
	| befor(f1,f2) 	 => befor(tsubst v x f1,tsubst v x f2)
	| swhen(f1,f2)   => swhen(tsubst v x f1,tsubst v x f2)
	| suntil(f1,f2)  => suntil(tsubst v x f1,tsubst v x f2)
	| sbefor(f1,f2)  => sbefor(tsubst v x f1,tsubst v x f2)
	| pnext f 	 => pnext(tsubst v x f)
	| psnext f 	 => psnext(tsubst v x f)
	| palways f 	 => palways(tsubst v x f)
	| peventual f 	 => peventual(tsubst v x f)
	| pwhen(f1,f2)   => pwhen(tsubst v x f1,tsubst v x f2)
	| puntil(f1,f2)  => puntil(tsubst v x f1,tsubst v x f2)
	| pbefor(f1,f2)  => pbefor(tsubst v x f1,tsubst v x f2)
	| pswhen(f1,f2)  => pswhen(tsubst v x f1,tsubst v x f2)
	| psuntil(f1,f2) => psuntil(tsubst v x f1,tsubst v x f2)
	| psbefor(f1,f2) => psbefor(tsubst v x f1,tsubst v x f2)

fun temp_subst [] t = t |
    temp_subst ((v,x)::sigma) t = temp_subst sigma (tsubst v x t)


fun def_subst [] t = t |
    def_subst (equ(ell,phi)::s) t = def_subst s (tsubst phi ell t)



(* ****************************************************************************	*)
(* The function tableau is described in my paper of TPHOL99. It essentially 	*)
(* abbreviates any subformula that starts with a temporal operator with a new	*)
(* variable that is then hidden by an existential quantification.		*)
(* Special care has to be taken for the NEXT operator and the past temporal 	*)
(* operators. For abbreviating past temporal operators, we must first apply one	*)
(* recursion step according to the recursion theorem for the corresponding past	*)
(* operator and abbreviate then the past next operator applied on the past 	*)
(* operator. For the next operator, we use two state variable to compute really	*)
(* an automaton. See the theorem "TEMP_OPS_DEFS_TO_OMEGA" of the theory		*)
(* "Omega_Automata" for more details on the form of the abbreviations.		*)
(* ****************************************************************************	*)


val fb = ref([]:string list); (* contains the names of forbidden variables *)

fun tableau Phi =
    case Phi of
	  var(_)	=> ([],Phi)
        | neg phi 	=>
		let val (defs,phi') = tableau phi
		 in (defs,neg(phi'))
		end
        | conj(phi,psi)	=>
		let val (defs1,phi') = tableau phi
		    val (defs2,psi') = tableau (def_subst defs1 psi)
		 in (defs1 @ defs2,conj(phi',psi'))
		end
        | disj(phi,psi)	=>
		let val (defs1,phi') = tableau phi
		    val (defs2,psi') = tableau (def_subst defs1 psi)
		 in (defs1 @ defs2,disj(phi',psi'))
		end
        | imp(phi,psi)	=>
		let val (defs1,phi') = tableau phi
		    val (defs2,psi') = tableau (def_subst defs1 psi)
		 in (defs1 @ defs2,imp(phi',psi'))
		end
        | equ(phi,psi)	=>
		let val (defs1,phi') = tableau phi
		    val (defs2,psi') = tableau (def_subst defs1 psi)
		 in (defs1 @ defs2, equ(phi',psi'))
		end
        | ifte(phi,alpha,beta) =>
		let val (defs1,phi') = tableau phi
		    val (defs2,alpha') = tableau (def_subst defs1 alpha)
		    val (defs3,beta')  = tableau (def_subst (defs1 @ defs2) beta)
		 in (defs1 @ defs2 @ defs3,ifte(phi',alpha',beta'))
		end
        | next phi =>
		let
		    val (defs,phi') = tableau phi
		    val ell0_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell0_name::(!fb) )
		    val ell1_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell1_name::(!fb) )
		    val ell0 = var(ell0_name)
		    val ell1 = var(ell1_name)
		    val def0 = equ(ell0,phi')
		    val def1 = equ(ell1,next(ell0))
		 in ( defs @ [def0,def1], ell1)
		end
        | always phi =>
		let
		    val (defs,phi') = tableau phi
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,always(phi'))
		 in (defs @ [def], ell)
		end
        | eventual phi =>
		let
		    val (defs,phi') = tableau phi
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,eventual(phi'))
		 in (defs @ [def], ell)
		end
        | when(phi,psi) =>
		let
		    val (defs1,phi') = tableau phi
		    val (defs2,psi') = tableau (def_subst defs1 psi)
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,when(phi',psi'))
		 in (defs1 @ defs2 @ [def], ell)
		end
        | until(phi,psi) =>
		let
		    val (defs1,phi') = tableau phi
		    val (defs2,psi') = tableau (def_subst defs1 psi)
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,until(phi',psi'))
		 in (defs1 @ defs2 @ [def], ell)
		end
        | befor(phi,psi) =>
		let
		    val (defs1,phi') = tableau phi
		    val (defs2,psi') = tableau (def_subst defs1 psi)
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,befor(phi',psi'))
		 in (defs1 @ defs2 @ [def], ell)
		end
        | swhen(phi,psi) =>
		let
		    val (defs1,phi') = tableau phi
		    val (defs2,psi') = tableau (def_subst defs1 psi)
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,swhen(phi',psi'))
		 in (defs1 @ defs2 @ [def], ell)
		end
        | suntil(phi,psi) =>
		let
		    val (defs1,phi') = tableau phi
		    val (defs2,psi') = tableau (def_subst defs1 psi)
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,suntil(phi',psi'))
		 in (defs1 @ defs2 @ [def], ell)
		end
        | sbefor(phi,psi) =>
		let
		    val (defs1,phi') = tableau phi
		    val (defs2,psi') = tableau (def_subst defs1 psi)
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,sbefor(phi',psi'))
		 in (defs1 @ defs2 @ [def], ell)
		end
        | pnext phi =>
		let
		    val (defs,phi') = tableau phi
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,pnext(phi'))
		 in (defs @ [def], ell)
		end
        | psnext phi =>
		let
		    val (defs,phi') = tableau phi
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,psnext(phi'))
		 in (defs @ [def], ell)
		end
        | palways phi =>
		let
		    val (defs,phi') = tableau phi
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,pnext(palways(phi')))
		 in (defs @ [def], conj(phi',ell))
		end
        | peventual phi =>
		let
		    val (defs,phi') = tableau phi
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,psnext(peventual(phi')))
		 in (defs @ [def], disj(phi',ell))
		end
        | pwhen(phi,psi) =>
		let
		    val (defs1,phi') = tableau phi
		    val (defs2,psi') = tableau (def_subst defs1 psi)
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,pnext(pwhen(phi',psi')))
		 in (
		     defs1 @ defs2 @ [def],
		     disj(conj(phi,psi),conj(neg(psi),ell))
		    )
		end
        | puntil(phi,psi) =>
		let
		    val (defs1,phi') = tableau phi
		    val (defs2,psi') = tableau (def_subst defs1 psi)
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,pnext(puntil(phi',psi')))
		 in (
		     defs1 @ defs2 @ [def],
		     disj(psi',conj(phi',ell))
		    )
		end
        | pbefor(phi,psi) =>
		let
		    val (defs1,phi') = tableau phi
		    val (defs2,psi') = tableau (def_subst defs1 psi)
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,pnext(pbefor(phi',psi')))
		 in (
		     defs1 @ defs2 @ [def],
		     conj(neg(psi'),disj(phi',ell))
		    )
		end
        | pswhen(phi,psi) =>
		let
		    val (defs1,phi') = tableau phi
		    val (defs2,psi') = tableau (def_subst defs1 psi)
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,psnext(pswhen(phi',psi')))
		 in (
		     defs1 @ defs2 @ [def],
		     disj(conj(phi,psi),conj(neg(psi),ell))
		    )
		end
        | psuntil(phi,psi) =>
		let
		    val (defs1,phi') = tableau phi
		    val (defs2,psi') = tableau (def_subst defs1 psi)
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,psnext(psuntil(phi',psi')))
		 in (
		     defs1 @ defs2 @ [def],
		     disj(psi',conj(phi',ell))
		    )
		end
        | psbefor(phi,psi) =>
		let
		    val (defs1,phi') = tableau phi
		    val (defs2,psi') = tableau (def_subst defs1 psi)
		    val ell_name = new_sig_var "ell" (!fb) 0
		    val u = (fb := ell_name::(!fb) )
		    val ell = var(ell_name)
		    val def = equ(ell,psnext(psbefor(phi',psi')))
		 in (
		     defs1 @ defs2 @ [def],
		     conj(neg(psi'),disj(phi',ell))
		    )
		end
	| truesig => ([],truesig)
	| falsesig => ([],falsesig)







(* ************************************************************************************	*)
(* Based on the above function, the conversion TEMP_DEFS_CONV proves now the equivalence*)
(* between the term with the local abbreviations and the given LTL formula. Note that	*)
(* the given LTL formula must be of the form ALWAYS phi 0, i.e., we only deal with 	*)
(* initial equivalence, which is necessary for the past operators. 			*)
(* ------------------------------------------------------------------------------------	*)
(* new_theory "ltltest";								*)
(* new_parent "Omega_Automata";								*)
(* TEMP_DEFS_CONV (--`ALWAYS (\t. (EVENTUAL a) t = a t \/ NEXT (EVENTUAL a) t) 0`--); 	*)
(* val it =										*)
(*   |- ALWAYS (\t. EVENTUAL a t = a t \/ NEXT (EVENTUAL a) t) 0 =			*)
(*      (?ell0 ell1 ell2 ell3 ell4.							*)
(*        ell4 0 /\									*)
(*        (ell0 = EVENTUAL a) /\							*)
(*        (ell1 = EVENTUAL a) /\							*)
(*        (ell2 = ell1) /\								*)
(*        (ell3 = NEXT ell2) /\								*)
(*        (ell4 = ALWAYS (\t. ell0 t = a t \/ ell3 t))) : thm				*)
(* 											*)
(* TEMP_DEFS_CONV (--`ALWAYS (EVENTUAL (\t. a t /\ PALWAYS b t)) 0`--);			*)
(* val it =										*)
(*   |- ALWAYS (EVENTUAL (\t. a t /\ PALWAYS b t)) 0 =					*)
(*      (?ell0 ell1 ell2.								*)
(*        ell2 0 /\									*)
(*        (ell0 = PNEXT (PALWAYS b)) /\							*)
(*        (ell1 = EVENTUAL (\t. a t /\ b t /\ ell0 t)) /\				*)
(*        (ell2 = ALWAYS ell1)) : thm							*)
(* 											*)
(* ************************************************************************************	*)

(* ----------------------------------------------------------------------------	*)
(* In the following, we have to deal with goals of the following form 		*)
(* 		asm |- (?l1'...ln'. /\_{i=1^k} phi_i ) ==> Phi. 		*)
(* Clearly, we should apply STRIP_TAC to reduce this to the following subgoal:	*)
(*		[phi_1,...,phi_k] @ asm |- Phi					*)
(* However, STRIP_TAC is painfully slow, as the number of quantified variables 	*)
(* may be larger than 50. Hence, we use a more specialized and more efficient 	*)
(* tactic here to do the reduction. Do not replace it with STRIP_TAC.		*)
(* ----------------------------------------------------------------------------	*)

fun MY_STRIP_TAC (asm,g) =
    let val {ant=a,conseq=Phi} = dest_imp g
     in
	(REPEAT ((CONV_TAC LEFT_IMP_EXISTS_CONV) THEN GEN_TAC)
	 THEN DISCH_TAC
	 THEN POP_ASSUM (fn x=> MAP_EVERY ASSUME_TAC (CONJUNCTS x))
	)
	(asm,g)
    end



val boolean_sig_ops = TAC_PROOF(
	([],--`
		? s_not s_and s_or s_imp s_equiv s_ifte.
		     (!a b c.
			( (s_not a) = \t:num. ~a t) /\
			( s_and a b = \t:num. (a t /\ b t) ) /\
			( s_or a b  = \t:num. (a t \/ b t) ) /\
			( s_imp a b = \t:num. (a t ==> b t) ) /\
			( s_equiv a b = \t:num. (a t = b t) ) /\
			( s_ifte a b c = \t:num. (a t => b t | c t))
		     )
		    /\
		     (!a b c.
			(!t:num. ~a t = (s_not a) t) /\
			(!t:num. (a t /\ b t)  = s_and a b t) /\
			(!t:num. (a t \/ b t)  = s_or a b t) /\
			(!t:num. (a t ==> b t) = s_imp a b t) /\
			(!t:num. (a t = b t)   = s_equiv a b t) /\
			(!t:num. (a t => b t | c t) = s_ifte a b c t)
		     )
	`--),
	EXISTS_TAC (--`\a.\t:num.~a t`--)
	THEN EXISTS_TAC (--`\a b.\t:num. a t /\ b t`--)
	THEN EXISTS_TAC (--`\a b.\t:num. a t \/ b t`--)
	THEN EXISTS_TAC (--`\a b.\t:num. a t ==> b t`--)
	THEN EXISTS_TAC (--`\a b.\t:num. (a t):bool = b t`--)
	THEN EXISTS_TAC (--`\a b c.\t:num. a t => (b t):bool | c t`--)
	THEN CONV_TAC(DEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
	THEN REPEAT GEN_TAC THEN REWRITE_TAC[])



fun PAST_RECURSION_TAC (asm,g) =
    let fun tll 0 l = l | tll n (e::l) = tll (n-1) l
	val rec_thm = Past_Temporal_LogicTheory.RECURSION
	val past_rec_thms = (map (GEN_ALL o SYM) (tll 8 (CONJUNCTS rec_thm)))
     in
       (
	MAP_EVERY ASSUME_TAC past_rec_thms
	THEN MAP_EVERY (UNDISCH_TAC o concl) past_rec_thms
	THEN ASSUME_TAC boolean_sig_ops
	THEN UNDISCH_TAC (concl boolean_sig_ops) THEN STRIP_TAC
	THEN POP_ASSUM (fn x => REWRITE_TAC[x])
	THEN CONV_TAC(DEPTH_CONV ETA_CONV)
	THEN DISCH_TAC THEN POP_ASSUM (fn x => REWRITE_TAC[x])
	THEN DISCH_TAC THEN POP_ASSUM (fn x => REWRITE_TAC[x])
	THEN DISCH_TAC THEN POP_ASSUM (fn x => REWRITE_TAC[x])
	THEN DISCH_TAC THEN POP_ASSUM (fn x => REWRITE_TAC[x])
	THEN DISCH_TAC THEN POP_ASSUM (fn x => REWRITE_TAC[x])
	THEN DISCH_TAC THEN POP_ASSUM (fn x => REWRITE_TAC[x])
	THEN DISCH_TAC THEN POP_ASSUM (fn x => REWRITE_TAC[x])
	THEN DISCH_TAC THEN POP_ASSUM (fn x => REWRITE_TAC[x])
	THEN POP_ASSUM (fn x => REWRITE_TAC[x])
       ) (asm,g)
    end


fun TEMP_DEFS_CONV t =
    let
	(* ----------------------------------------------------------------------------	*)
	(* First we construct the goal that is to be proved. For this reason, we invoke	*)
	(* the function tableau above and generate the corresponding hol term. 		*)
	(* ----------------------------------------------------------------------------	*)
	val tt = hol2temporal t
	val u = (fb := var_names tt)
	val (defs,pt) = tableau tt
	fun eta_conv t = (* ----- transforms "\t. ell t" to "ell" ----- *)
	    let val {Bvar=x,Body=b} = dest_abs t
		val {Rator=ell,Rand=y} = dest_comb b
	     in if(x=y) then ell else t
	    end
	fun fun_eta_conv t = (* ----- transforms "\t. ell t = phi" to "ell = \t. phi" ----- *)
	    let val {Bvar=x,Body=b} = dest_abs t
		val {lhs=l,rhs=r} = dest_eq b
		val ell = rator l
		val new_r = mk_abs{Bvar=x,Body=r}
	     in mk_eq{lhs=ell,rhs=(eta_conv new_r)}
	    end
	fun beta_conv t = rhs(concl ((QCONV (REPEATC (DEPTH_CONV BETA_CONV))) t))
	val hdefs = map (fun_eta_conv o temporal2hol) defs
	val hpt = mk_comb{Rator=(temporal2hol pt),Rand=(--`0`--)}
	val hpt = beta_conv hpt
	val hdefs = map beta_conv hdefs
	val varnames = map lhs hdefs
	val defterm = (list_mk_conj hdefs)
	val tt = list_mk_exists(varnames,mk_conj{conj1 = hpt, conj2 = defterm})
	val goal = ([],--`^t = ^tt`--) : goal
	(* ----------------------------------------------------------------------------	*)
	(* Having constructed the goal, we define now the tactic that solves this goal.	*)
	(* ----------------------------------------------------------------------------	*)
	fun flatten_defs [] = [] |
	    flatten_defs (d::dl) =
		let val equ(ell,phi) = d
		 in d::(map (tsubst ell phi) (flatten_defs dl))
		end
	val flat_hdefs = map (fun_eta_conv o temporal2hol) (flatten_defs defs)
	val inst_list = map rhs flat_hdefs
	val tac =
	    EQ_TAC
	    THENL[
		DISCH_TAC
		THEN MAP_EVERY EXISTS_TAC inst_list THEN BETA_TAC
		THEN UNDISCH_TAC t
		THEN PAST_RECURSION_TAC,
		MY_STRIP_TAC
		THEN UNDISCH_TAC hpt THEN ASM_REWRITE_TAC[] THEN BETA_TAC
		THEN PAST_RECURSION_TAC
		]
     in TAC_PROOF(goal, tac)
    end;





fun UNSAFE_TEMP_DEFS_CONV t =
    let
	(* ----------------------------------------------------------------------------	*)
	(* First we construct the goal that is to be proved. For this reason, we invoke	*)
	(* the function tableau above and generate the corresponding hol term. 		*)
	(* ----------------------------------------------------------------------------	*)
	val tt = hol2temporal t
	val u = (fb := var_names tt)
	val (defs,pt) = tableau tt
	fun eta_conv t = (* ----- transforms "\t. ell t" to "ell" ----- *)
	    let val {Bvar=x,Body=b} = dest_abs t
		val {Rator=ell,Rand=y} = dest_comb b
	     in if(x=y) then ell else t
	    end
	fun fun_eta_conv t = (* ----- transforms "\t. ell t = phi" to "ell = \t. phi" ----- *)
	    let val {Bvar=x,Body=b} = dest_abs t
		val {lhs=l,rhs=r} = dest_eq b
		val ell = rator l
		val new_r = mk_abs{Bvar=x,Body=r}
	     in mk_eq{lhs=ell,rhs=(eta_conv new_r)}
	    end
  fun beta_conv t = rhs(concl ((QCONV (REPEATC (DEPTH_CONV BETA_CONV))) t))
	val hdefs = map (fun_eta_conv o temporal2hol) defs
	val hpt = mk_comb{Rator=(temporal2hol pt),Rand=(--`0`--)}
	val hpt = beta_conv hpt
	val hdefs = map beta_conv hdefs
	val varnames = map lhs hdefs
	val defterm = (list_mk_conj hdefs)
	val tt = list_mk_exists(varnames,mk_conj{conj1 = hpt, conj2 = defterm})
	val goal = ([],--`^t = ^tt`--) : goal
     in mk_thm goal
    end




(* ************************************************************************************	*)
(* The conversion LTL2OMEGA_CONV finally does what its name indicates. Given an LTL 	*)
(* formula in the form as mentioned in the comment on the conversion TEMP_DEFS_CONV,	*)
(* LTL2OMEGA_CONV computes an equivalent generalized Büchi automaton and proves the 	*)
(* equivalence with the given LTL formula. 						*)
(* ------------------------------------------------------------------------------------	*)
(* LTL2OMEGA_CONV (--`ALWAYS (\t. (EVENTUAL a) t = a t \/ NEXT (EVENTUAL a) t) 0`--); 	*)
(* val it =										*)
(*   |- ALWAYS (\t. EVENTUAL a t = a t \/ NEXT (EVENTUAL a) t) 0 =			*)
(*      (?ell0 ell1 ell2 ell3 ell4.							*)
(*        ell4 0 /\									*)
(*        (!t.										*)
(*          (ell0 t = a t \/ ell0 (SUC t)) /\						*)
(*          (ell1 t = a t \/ ell1 (SUC t)) /\						*)
(*          (ell2 t = ell1 t) /\							*)
(*          (ell3 t = ell2 (SUC t)) /\							*)
(*          (ell4 t = (ell0 t = a t \/ ell3 t) /\ ell4 (SUC t))) /\			*)
(*        (!t1. ?t2. ell0 (t1 + t2) ==> a (t1 + t2)) /\					*)
(*        (!t1. ?t2. ell1 (t1 + t2) ==> a (t1 + t2)) /\					*)
(*        (!t1.										*)
(*          ?t2.									*)
(*            (ell0 (t1 + t2) = a (t1 + t2) \/ ell3 (t1 + t2)) ==>			*)
(*            ell4 (t1 + t2))) : thm							*)
(* 											*)
(* LTL2OMEGA_CONV (--`ALWAYS (EVENTUAL (\t. a t /\ PALWAYS b t)) 0`--);			*)
(* val it =										*)
(*   |- ALWAYS (EVENTUAL (\t. a t /\ PALWAYS b t)) 0 =					*)
(*      (?ell0 ell1 ell2.								*)
(*        (ell2 0 /\ ell0 0) /\								*)
(*        (!t.										*)
(*          (ell0 (SUC t) = b t /\ ell0 t) /\						*)
(*          (ell1 t = a t /\ b t /\ ell0 t \/ ell1 (SUC t)) /\				*)
(*          (ell2 t = ell1 t /\ ell2 (SUC t))) /\					*)
(*        (!t1.										*)
(*          ?t2.									*)
(*            ell1 (t1 + t2) ==> a (t1 + t2) /\ b (t1 + t2) /\ ell0 (t1 + t2)) /\	*)
(*        (!t1. ?t2. ell1 (t1 + t2) ==> ell2 (t1 + t2))) : thm				*)
(* 											*)
(* ************************************************************************************	*)



fun LTL2OMEGA_CONV t =
    let
	val future_temp_ops = constants "Temporal_Logic"
	val past_temp_ops = constants "Past_Temporal_Logic"
	val temp_ops = future_temp_ops @ past_temp_ops
	fun elem 0 l = hd l
	  | elem i l = elem (i-1) (tl l)
	fun delete 0 (e::l) = l
	  | delete i (e::l) = (e::(delete (i-1) l))
	fun get_constants t =
	    if (is_var t) then []
	    else if (is_const t) then [t]
	    else if (is_abs t) then get_constants(body t)
	    else (* its a function application *)
		let val {Rator=f,Rand=x} = dest_comb t
		 in (get_constants f) @ (get_constants x)
		end
	fun is_prop t = null((intersect (get_constants t) temp_ops))
	val def2omega_thms = CONJUNCTS Omega_AutomataTheory.TEMP_OPS_DEFS_TO_OMEGA
	val past_nx_thms = [elem 9 def2omega_thms,elem 10 def2omega_thms]
	val def2omega_thms = delete 9 (delete 10 def2omega_thms)
	fun def2omega def =
	    if (is_prop def) then
	    	let val {lhs=ell,rhs=phi} = dest_eq def
		 in ((--`T`--),(--`!t:num. ^ell t = ^phi t`--),(--`T`--))
		end
	    else
		let val thm = ((PURE_REWRITE_CONV def2omega_thms) THENC
			       (PURE_REWRITE_CONV past_nx_thms)) def
		    val r = rhs(concl thm)
		    val {conj1=init_condition,conj2=rest} = dest_conj r
		    val {conj1=trans_rel,conj2=accept} = dest_conj rest
		 in (init_condition,trans_rel,accept)
		end
	val simplify_conv = rhs o  concl o ((DEPTH_CONV BETA_CONV) THENC (REWRITE_CONV[]))
	val thm0 = TEMP_DEFS_CONV t
	val defterm = rhs(concl thm0)
	val (dvars,rest) = strip_exists defterm
	val restlist = strip_conj rest
	val init_cond = hd restlist
	val defs = tl restlist
	val omega_list = map def2omega defs
	val init_condition = list_mk_conj (map (fn (x,y,z) => x) omega_list)
	val trans_rel = list_mk_conj (map (fn (x,y,z) => #Body(dest_forall y)) omega_list)
	val acceptance = list_mk_conj (map (fn (x,y,z) => z) omega_list)
	val init_condition = mk_conj{conj1=init_cond, conj2=init_condition}
	val trans_rel = mk_forall{Bvar=(--`t:num`--),Body=trans_rel}
	val init_condition = simplify_conv init_condition
	val trans_rel      = simplify_conv trans_rel
	val acceptance     = simplify_conv acceptance
	val automaton_kernel = list_mk_conj[init_condition,trans_rel,acceptance]
	val automaton = list_mk_exists(dvars,automaton_kernel)
	val goal = ([],mk_eq{lhs=defterm,rhs=automaton}):goal
	fun EX_TAC (asm,g) =
	    let val {Bvar=x,Body=t} = dest_exists g
	     in EXISTS_TAC x (asm,g)
	    end
	val tac = PURE_REWRITE_TAC[(QCONV (REPEATC(DEPTH_CONV FORALL_AND_CONV))) trans_rel]
		  THEN REWRITE_TAC def2omega_thms
		  THEN REWRITE_TAC past_nx_thms
		  THEN (CONV_TAC(DEPTH_CONV FUN_EQ_CONV)) THEN BETA_TAC
		  THEN REWRITE_TAC[]
		  THEN EQ_TAC THEN MY_STRIP_TAC THEN REPEAT EX_TAC
		  THEN RULE_ASSUM_TAC EQT_INTRO
		  THEN ASM_REWRITE_TAC[]
	val thm1 = TAC_PROOF(goal,tac)
     in TRANS thm0 thm1
    end



fun UNSAFE_LTL2OMEGA_CONV t =
    let
	val future_temp_ops = constants "Temporal_Logic"
	val past_temp_ops = constants "Past_Temporal_Logic"
	val temp_ops = future_temp_ops @ past_temp_ops
	fun elem 0 l = hd l
	  | elem i l = elem (i-1) (tl l)
	fun delete 0 (e::l) = l
	  | delete i (e::l) = (e::(delete (i-1) l))
	fun get_constants t =
	    if (is_var t) then []
	    else if (is_const t) then [t]
	    else if (is_abs t) then get_constants(body t)
	    else (* its a function application *)
		let val {Rator=f,Rand=x} = dest_comb t
		 in (get_constants f) @ (get_constants x)
		end
	fun is_prop t = null((intersect (get_constants t) temp_ops))
	val def2omega_thms = CONJUNCTS Omega_AutomataTheory.TEMP_OPS_DEFS_TO_OMEGA
	val past_nx_thms = [elem 9 def2omega_thms,elem 10 def2omega_thms]
	val def2omega_thms = delete 9 (delete 10 def2omega_thms)
	fun def2omega def =
	    if (is_prop def) then
	    	let val {lhs=ell,rhs=phi} = dest_eq def
		 in ((--`T`--),(--`!t:num. ^ell t = ^phi t`--),(--`T`--))
		end
	    else
		let val thm = ((PURE_REWRITE_CONV def2omega_thms) THENC
			       (PURE_REWRITE_CONV past_nx_thms)) def
		    val r = rhs(concl thm)
		    val {conj1=init_condition,conj2=rest} = dest_conj r
		    val {conj1=trans_rel,conj2=accept} = dest_conj rest
		 in (init_condition,trans_rel,accept)
		end
	val simplify_conv = rhs o  concl o ((DEPTH_CONV BETA_CONV) THENC (REWRITE_CONV[]))
	val thm0 = UNSAFE_TEMP_DEFS_CONV t
	val defterm = rhs(concl thm0)
	val (dvars,rest) = strip_exists defterm
	val restlist = strip_conj rest
	val init_cond = hd restlist
	val defs = tl restlist
	val omega_list = map def2omega defs
	val init_condition = list_mk_conj (map (fn (x,y,z) => x) omega_list)
	val trans_rel = list_mk_conj (map (fn (x,y,z) => #Body(dest_forall y)) omega_list)
	val acceptance = list_mk_conj (map (fn (x,y,z) => z) omega_list)
	val init_condition = mk_conj{conj1=init_cond, conj2=init_condition}
	val trans_rel = mk_forall{Bvar=(--`t:num`--),Body=trans_rel}
	val init_condition = simplify_conv init_condition
	val trans_rel      = simplify_conv trans_rel
	val acceptance     = simplify_conv acceptance
	val automaton_kernel = list_mk_conj[init_condition,trans_rel,acceptance]
	val automaton = list_mk_exists(dvars,automaton_kernel)
	val goal = ([],mk_eq{lhs=defterm,rhs=automaton}):goal
	val thm1 = mk_thm goal
     in TRANS thm0 thm1
    end







(* ************************************************************************************	*)
(* The conversions TEMP_DEFS_CONV and LTL2OMEGA_CONV require that their input is a 	*)
(* formula that is a boolean combination of formulas that start with a temporal operator*)
(* that is applied to the initial point of time, i.e., to 0. 				*)
(* Normally, users do not want to deal with such initial equivalences, but use formulas	*)
(* with free numeric variables and also with equations between signals. These formulas	*)
(* are brought into the normal form required by TEMP_DEFS_CONV and LTL2OMEGA_CONV with 	*)
(* the following conversion. It is however not really a conversion, since it requires	*)
(* to quantify over the numeric free variables. If the user does not do this, a 	*)
(* universal quantification is assumed.							*)
(* ------------------------------------------------------------------------------------	*)
(* Example: 										*)
(* val t = (--` (ALWAYS a t ==> EVENTUAL a t) /\ 					*)
(* 	        (ALWAYS (EVENTUAL a) x ==> EVENTUAL (ALWAYS a) x) /\			*)
(* 	        ( (\t. ~NEXT a t) = NEXT (\t. ~ a t) )					*)
(*         `--);									*)
(* val it =										*)
(*   |- (!t x.										*)
(*        (ALWAYS a t ==> EVENTUAL a t) /\						*)
(*        (ALWAYS (EVENTUAL a) x ==> EVENTUAL (ALWAYS a) x) /\				*)
(*        ((\t. ~(NEXT a t)) = NEXT (\t. ~(a t)))) =					*)
(*      ALWAYS (\t. ALWAYS a t ==> EVENTUAL a t) 0 /\					*)
(*      ALWAYS (\x. ALWAYS (EVENTUAL a) x ==> EVENTUAL (ALWAYS a) x) 0 /\		*)
(*      ALWAYS (\n. ~(NEXT a n) = NEXT (\t. ~(a t)) n) 0 : thm				*)
(* 											*)
(* ************************************************************************************	*)


(* ----------------------------------------------------------------------------	*)
(* Given a term t and a variable x that occurs free in t, the function closure	*)
(* finds the smallest subterm of t that contains x and quantify it depending on *)
(* the flag exquan. This function is used to get rid of free numeric variables.	*)
(* ----------------------------------------------------------------------------	*)

exception NOT_GOOD_FORMULA;

fun closure exquan x t =
	    (let val {Name=_,Ty=_} = dest_var t
	      in if x=t then
		    if exquan then mk_exists{Bvar=x,Body=t}
		    else mk_forall{Bvar=x,Body=t}
		 else t
	     end)
	 handle _=>
	    (let val {Name=_,Ty=_} = dest_const t
	      in t
	     end)
	 handle _=>
	    (let val {Bvar=y,Body=b} = dest_abs t
	      in if x=y then t
		 else mk_abs{Bvar=y,Body=(closure exquan x b)}
	     end)
	 handle _=>
	    if (is_neg t) then mk_neg (closure (not exquan) x (dest_neg t))
	    else if (is_conj t) then
		let val {conj1=t1,conj2=t2} = dest_conj t
		    val occ1 = mem x (free_vars t1)
		    val occ2 = mem x (free_vars t2)
		 in
		    if (occ1 andalso occ2) then
		        if exquan then mk_exists{Bvar=x,Body=t}
		        else mk_forall{Bvar=x,Body=t}
		    else if occ1 then
			mk_conj{conj1=(closure exquan x t1),conj2=t2}
		    else if occ2 then
			mk_conj{conj1=t1,conj2=(closure exquan x t2)}
		    else t
		end
	    else if (is_disj t) then
		let val {disj1=t1,disj2=t2} = dest_disj t
		    val occ1 = mem x (free_vars t1)
		    val occ2 = mem x (free_vars t2)
		 in
		    if (occ1 andalso occ2) then
		        if exquan then mk_exists{Bvar=x,Body=t}
		        else mk_forall{Bvar=x,Body=t}
		    else if occ1 then
			mk_disj{disj1=(closure exquan x t1),disj2=t2}
		    else if occ2 then
			mk_disj{disj1=t1,disj2=(closure exquan x t2)}
		    else t
		end
	    else if (is_imp t) then
		let val {ant=t1,conseq=t2} = dest_imp t
		    val occ1 = mem x (free_vars t1)
		    val occ2 = mem x (free_vars t2)
		 in
		    if (occ1 andalso occ2) then
		        if exquan then mk_exists{Bvar=x,Body=t}
		        else mk_forall{Bvar=x,Body=t}
		    else if occ1 then
			mk_imp{ant=(closure (not exquan) x t1),conseq=t2}
		    else if occ2 then
			mk_imp{ant=t1,conseq=(closure (not exquan) x t2)}
		    else t
		end
	    else if (is_eq t) then
		let val {lhs=t1,rhs=t2} = dest_eq t
		    val occ1 = mem x (free_vars t1)
		    val occ2 = mem x (free_vars t2)
		 in
		    if (occ1 andalso occ2) then
		        if exquan then mk_exists{Bvar=x,Body=t}
		        else mk_forall{Bvar=x,Body=t}
		    else raise NOT_GOOD_FORMULA
		end
	    else if (is_cond t) then
		let val {cond=t1,larm=t2,rarm=t3} = dest_cond t
		    val occ1 = mem x (free_vars t1)
		    val occ2 = mem x (free_vars t2)
		    val occ3 = mem x (free_vars t3)
		 in
		    if (occ1 andalso occ2 andalso occ3) then
		        if exquan then mk_exists{Bvar=x,Body=t}
		        else mk_forall{Bvar=x,Body=t}
		    else raise NOT_GOOD_FORMULA
		end
	    else raise NOT_GOOD_FORMULA;




fun TEMP_NORMALIZE_CONV t =
    let
	(* ----------------------------------------------------------------------------	*)
	(* First we check whether there is a free numeric variable. If so, we choose	*)
	(* one of them and universally quantify them and compute a prenex normal form.	*)
	(* the function tableau above and generate the corresponding hol term. 		*)
	(* ----------------------------------------------------------------------------	*)
	val num_vars = filter (fn x => (type_of x) = (==`:num`==)) (free_vars t)
	fun close_all [] t = t
	  | close_all (x::vl) t = close_all vl (closure false x t)
	val t = close_all num_vars t
	val forall_always_thm = TAC_PROOF(
		([],--`!P. (!n. P n) = ALWAYS P 0`--),
		REWRITE_TAC[Temporal_LogicTheory.ALWAYS]
		THEN BETA_TAC
		THEN REWRITE_TAC[arithmeticTheory.ADD_CLAUSES]);
	val exists_eventual_thm = TAC_PROOF(
		([],--`!P. (?n. P n) = EVENTUAL P 0`--),
		REWRITE_TAC[Temporal_LogicTheory.EVENTUAL]
		THEN BETA_TAC
		THEN REWRITE_TAC[arithmeticTheory.ADD_CLAUSES]);
	fun QUAN_TEMP_CONV t =
	    if is_forall t then
		let val b = rand t
	    	 in BETA_RULE(SPEC b forall_always_thm)
	    	end
	    else if is_exists t then
		let val b = rand t
	    	 in BETA_RULE(SPEC b exists_eventual_thm)
	    	end
	    else REFL t
	val thm1 = (QCONV
		((DEPTH_CONV FUN_EQ_CONV) THENC
		 (DEPTH_CONV BETA_CONV) THENC
		 (DEPTH_CONV (CHANGED_CONV QUAN_TEMP_CONV))
		)) t
	val thm2 = Arith.PRENEX_CONV t
     in
	TRANS (SYM thm2) thm1
    end;





(* ************************************************************************************	*)
(* The next functions deal with interfacing with the SMV system.			*)
(* The global variable print_states indicates that the state variables shall be printed.*)
(* This is not always desired, since one often wants to have the input sequence of the	*)
(* model.										*)
(* ************************************************************************************	*)

val print_states = ref false;


(* ********************************* term2smv_string **********************************	*)
(* term2smv_string translates propositional terms in the atoms (p 0), (p t) and p(SUC t)*)
(* into SMV syntax, where (p 0) and (p t) are both written as p and p(SUC t) is written	*)
(* as next(p) (this will only occur in the transition relation.				*)
(* ************************************************************************************	*)


fun term2smv_string t =
    (let val {Name=n,Ty=typ} = dest_const t
      in if n="T" then "1" else if n="F" then "0" else n
     end)
  handle _=> (* ------ propositional or temporal operator or signal evalutation -------	*)
    (let val t1 = dest_neg t
      in "!"^(term2smv_string t1)
     end)
  handle _=>
    (let val {conj1=t1,conj2=t2} = dest_conj t
      in "("^(term2smv_string t1)^" & "^(term2smv_string t2)^")"
     end)
  handle _=>
    (let val {disj1=t1,disj2=t2} = dest_disj t
      in "("^(term2smv_string t1)^" | "^(term2smv_string t2)^")"
     end)
  handle _=>
    (let val {ant=t1,conseq=t2} = dest_imp t
      in "("^(term2smv_string t1)^" -> "^(term2smv_string t2)^")"
     end)
  handle _=>
    (let val {lhs=t1,rhs=t2} = dest_eq t
      in "("^(term2smv_string t1)^" <-> "^(term2smv_string t2)^")"
     end)
  handle _=>
    (let val {cond=t1,larm=t2,rarm=t3} = dest_cond t
	 val p1 = term2smv_string t1
      in "(("^p1^" & "^(term2smv_string t2)^") | (!"^p1^" & "^(term2smv_string t3)^"))"
     end)
  handle _=> 		      (* ------ signal evalutation ------------	*)
    (let val {Rator=f,Rand=x} = dest_comb t
      in if (is_var x) then #Name(dest_var f)
	 else if (x=(--`0`--)) then #Name(dest_var f)
	 else if ((rator x)=(--`SUC`--)) then
		"next("^(#Name(dest_var f))^")"
	 else #Name(dest_var f)
     end)


fun genbuechi2smv_string b =
    let
	val (state_vars,kernel) = strip_exists b
	val {conj1=init_condition,conj2=rest} = dest_conj kernel
	val {conj1=transrel,conj2=accept} = dest_conj rest
	val inout_vars = free_vars b
	val vars = inout_vars @ state_vars
	fun var_list2smv [] = "" |
	    var_list2smv (v::vl) =
		let val {Name=n,Ty=_} = dest_var v
		 in "   "^n^" : boolean;\n"^(var_list2smv vl)
		end
	fun acceptance [] = "" |
	    acceptance (a::al) =
		let val {Bvar=_,Body=a1} = dest_forall a
		    val {Bvar=_,Body=a2} = dest_exists a1
		 in "\nFAIRNESS "^(term2smv_string a2)^(acceptance al)
		end
     in
	"MODULE main\n\n"^
	"VAR\n"^(var_list2smv vars)^"\n"^
	"TRANS \n"^(term2smv_string(#Body(dest_forall transrel)))^"\n\n"^
	(acceptance (strip_conj accept))^"\n\n"^
	"SPEC (EG 1) -> !"^(term2smv_string init_condition)^"\n\n"
    end;


fun hol2smv t =
    let val thm0 = TEMP_NORMALIZE_CONV (mk_neg t)
	val t0 = rhs(concl thm0)
	val thm1 = LTL2OMEGA_CONV t0
	val b = rhs(concl thm1)
     in
	genbuechi2smv_string b
    end




(* *************************** interpret_smv_output ***********************************	*)
(* This function interpretes the output of smv, i.e. the string list is split up into	*)
(* a sequence of state descriptions and the proved flag and the resource information.	*)
(* ************************************************************************************	*)

fun interpret_smv_output stl =
    let fun beginl [] l = true |
	    beginl (e::s) [] = false |
	    beginl (e1::s1) (e2::s2) = (e1=e2) andalso (beginl s1 s2)
	fun begins s1 s2 = beginl (explode s1) (explode s2)
	val stll = ref stl
	val proved =
	    let val (l::ll) = !stll
	     in (stll := ll; beginl [#"\n",#"e",#"u",#"r",#"t"] (rev(explode l)))
	    end
	fun skip_lines [] = []|
	    skip_lines (e::l) = if (e="\n") then skip_lines l else (e::l)
	fun read_state_lines() = (* reading lines until empty line is read *)
	    let val (l::ll) = !stll
		val _ = (stll := ll)
	     in if l="\n" then []
		else l::(read_state_lines())
	    end
	fun loop_starts() = beginl (explode "-- loop") (explode(hd(!stll)))
	fun resource_starts() = beginl (explode "resou") (explode(hd(!stll)))
	fun another_state() = beginl (explode "state") (explode(hd(!stll)))
	val init_sequence = ref ([]:string list list)
	val loop_sequence = ref ([]:string list list)
     in (if proved then ()
	 else
	    (stll := skip_lines(tl(!stll));
	     while another_state() do
		(stll := tl(!stll);
		 init_sequence := (read_state_lines())::(!init_sequence);
		 stll := skip_lines(!stll));
	     if loop_starts() then
		(stll := tl(!stll);
	         while another_state() do
		    (stll := tl(!stll);
		     loop_sequence := (read_state_lines())::(!loop_sequence);
		     stll := skip_lines(!stll)))
	     else ());
	 {Proved = proved,
	  Init_Sequence = rev(!init_sequence),
	  Loop_Sequence = if !loop_sequence=[] then [] else rev(tl(!loop_sequence)),
	  Resources = skip_lines(!stll)})
    end




(* ************************************************************************************	*)
(* Printing the countermodel on the terminal 						*)
(* ************************************************************************************	*)

fun print_smv_info smv_info =
    let val {Proved = proved,
	     Init_Sequence = init_sequence,
	     Loop_Sequence = loop_sequence,
	     Resources = resources} = smv_info
	val state_count = ref 0;
	fun s_print (s:string) = print s
	fun print_state sa = s_print(String.concat sa)
	fun s_print_sequence [] = () |
	    s_print_sequence (sa::sl) =
		(
		s_print ("================== State"^(int_to_string(!state_count)));
		s_print ("==================\n");
		state_count := (!state_count) + 1;
		print_state sa;
		s_print_sequence sl
		)
     in if proved then
	    (
	     s_print "SMV has done the proof!\n";
	     s_print (String.concat resources);
	     ()
	    )
	else
	    (
	     s_print "===============================================\n";
	     s_print "Formula is not true! Consider the countermodel:\n";
	     s_print "===============================================\n";
	     s_print_sequence init_sequence;
	     if loop_sequence=[] then ()
	     else
		(
	         s_print "\n======== A loop starts here=============\n";
		 s_print_sequence loop_sequence
		);
	     s_print "===============================================\n";
	     s_print (String.concat resources);
	     s_print "===============================================\n";
	    ()
	    )
    end



(* ************************************************************************************	*)
(* Given a generalized co-Büchi automaton, the conversion SMV_AUTOMATON_CONV checks for	*)
(* nonemptiness of the automaton. If the language accepted by the automaton is empty, 	*)
(* the conversion generates the following theorem: |- (?a_1...a_n. automaton) = F, where*)
(* a_1,...,a_n are the free variables of the given automaton formula.			*)
(* In case the language is not empty, the conversion will print out the countermodel	*)
(* that has been generated by SMV which shows a word that belongs to the language of the*)
(* automaton.										*)
(* ************************************************************************************	*)


fun SMV_RUN_FILE smv_file =
    let
  val _ = Process.system
      ((!smv_path)^(!smv_call)^" "
      ^smv_file^" > "
      ^(!smv_tmp_dir)^"smv_out")
  val file_in = TextIO.openIn((!smv_tmp_dir)^"smv_out")
  val s = ref (TextIO.inputLine file_in)
  val sl = ref ([]:string list)
  val _ = while ((!s)<>NONE) do (sl:=(valOf (!s))::(!sl); s:=TextIO.inputLine file_in)
  val _ = TextIO.closeIn file_in
  val p = interpret_smv_output(rev(!sl))
  val _ = Process.system("rm "^(!smv_tmp_dir)^"smv_file.smv")
  val _ = Process.system("rm "^(!smv_tmp_dir)^"smv_out")
     in
      if #Proved(p) then true
      else
        (print "SMV computes the following countermodel:\n";
          print_smv_info p;
          false
        )
    end

fun SMV_RUN smv_program =
    let
  val file_st = TextIO.openOut((!smv_tmp_dir)^"smv_file.smv")
  val _ = (
    TextIO.output(file_st,smv_program);
    TextIO.flushOut file_st;
    TextIO.closeOut file_st)
  in
    SMV_RUN_FILE ((!smv_tmp_dir)^"smv_file.smv")
  end




fun SMV_AUTOMATON_CONV automaton =

    let
  val smv_program = genbuechi2smv_string automaton
  val proved = SMV_RUN smv_program
  in
    if (proved) then mk_thm([],mk_eq{lhs=automaton,rhs=(--`F`--)})
    else
      (NO_CONV (--`F`--))
  end;


(* ************************************************************************************	*)
(* Finally, we can combine all the stuff together.					*)
(* ************************************************************************************	*)

fun LTL_CONV t =
    let val t0 = mk_neg t
        val thm0 = TEMP_NORMALIZE_CONV t0
	val t1 = rhs(concl thm0)
	val thm1 = LTL2OMEGA_CONV t1
	val automaton = rhs(concl thm1)
	val thm2 = SMV_AUTOMATON_CONV automaton
     in
	EQT_INTRO(REWRITE_RULE[](TRANS (TRANS thm0 thm1) thm2))
    end



fun UNSAFE_LTL_CONV t =
    let val t0 = mk_neg t
        val thm0 = TEMP_NORMALIZE_CONV t0
	val t1 = rhs(concl thm0)
	val thm1 = UNSAFE_LTL2OMEGA_CONV t1
	val automaton = rhs(concl thm1)
	val thm2 = SMV_AUTOMATON_CONV automaton
     in
	EQT_INTRO(REWRITE_RULE[](TRANS (TRANS thm0 thm1) thm2))
    end

val _ = Parse.temp_set_grammars ambient_grammars
end;

end;
