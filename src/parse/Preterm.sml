structure Preterm :> Preterm =
struct

open Exception Lib;

fun PRETERM_ERR function message =
 Exception.HOL_ERR{origin_structure = "Preterm",
                   origin_function = function,
                   message = message};


type pretype = TCPretype.pretype

datatype preterm = Var   of {Name : string,  Ty : pretype}
                 | Const of {Name : string,  Ty : pretype}
                 | Comb  of {Rator: preterm, Rand : preterm}
                 | Abs   of {Bvar : preterm, Body : preterm}
                 | Constrained of preterm * pretype
                 | Antiq of Term.term

(*---------------------------------------------------------------------------*
 * Getting "hidden" functions from Type and Term.                            *
 *---------------------------------------------------------------------------*)
local
      val dty = Type.mk_vartype"'x"
      val dtm = Term.mk_var{Name="dummy",Ty=dty}
      val constify_ref = ref (fn{Name:string,Ty:Type.hol_type} => dtm)
      val Combify_ref = ref (fn{Rator:Term.term,Rand:Term.term} => dtm)
      val _ = Term.Preterm_init constify_ref Combify_ref
in
  val constify = !constify_ref
  val Combify = !Combify_ref
end;


(*---------------------------------------------------------------------------
 * Translation to terms so that the term prettyprinter can be used when
 * type inference fails.
 *---------------------------------------------------------------------------*)

fun ptremove {Name, Ty} = {Name = Name, Ty = TCPretype.toType Ty}

fun to_term (Var n) = Term.mk_var (ptremove n)
  | to_term (Const r) = constify (ptremove r)
  | to_term (Comb{Rator,Rand}) = Combify{Rator=to_term Rator,Rand=to_term Rand}
  | to_term (Abs{Bvar,Body}) = Term.mk_abs{Bvar=to_term Bvar,Body=to_term Body}
  | to_term (Antiq tm) = tm
  | to_term (Constrained(tm,_)) = to_term tm;


fun is_atom (Var _) = true
  | is_atom (Const _) = true
  | is_atom (Constrained(tm,_)) = is_atom tm
  | is_atom t = Term.is_numeral (to_term t)


(*---------------------------------------------------------------------------
 * Type inference for HOL terms. Looks ugly because of error messages, but is
 * actually very simple, given side-effecting unification.
 *---------------------------------------------------------------------------*)
local fun -->(ty1,ty2) = TCPretype.Tyop("fun", [ty1, ty2])
      infix  -->
      fun type_of (Var{Ty, ...}) = Ty
        | type_of (Const{Ty, ...}) = Ty
        | type_of (Comb{Rator, ...}) = TCPretype.chase (type_of Rator)
        | type_of (Abs{Bvar,Body}) = type_of Bvar --> type_of Body
        | type_of (Constrained(_,ty)) = ty
        | type_of (Antiq tm) = TCPretype.fromType (Term.type_of tm)
in
fun TC printers = let
  fun default_typrinter x = "<hol_type>"
  fun default_tmprinter x = "<term>"
  val (ptm, pty) =
    case printers of
      SOME (x,y) => (Lib.say o x, Lib.say o y o TCPretype.toType)
    | NONE => (Lib.say o default_tmprinter, Lib.say o default_typrinter)
  fun check(Comb{Rator, Rand}) =
        (check Rator;
         check Rand;
         TCPretype.unify (type_of Rator)
         (type_of Rand --> TCPretype.new_uvar())
         handle (e as Exception.HOL_ERR{origin_structure="TCPretype",
                                        origin_function="unify",message})
         => let val tmp = !Globals.show_types
                val _   = Globals.show_types := true
                val Rator' = to_term Rator
                val Rand'  = to_term Rand
            in
            Lib.say "\nType inference failure: unable to infer a type \
                              \for the application of\n\n";
            ptm Rator';
            Lib.say "\n\n";
            if (is_atom Rator) then ()
            else(Lib.say"which has type\n\n";pty(type_of Rator);Lib.say"\n\n");
            Lib.say "to\n\n"; ptm Rand'; Lib.say "\n\n";
            if (is_atom Rand) then ()
            else(Lib.say"which has type\n\n";pty(type_of Rand);Lib.say"\n\n");

            Lib.say ("unification failure message: "^message^"\n");
            Globals.show_types := tmp;
            raise PRETERM_ERR"typecheck" "failed"
            end)
      | check (Abs{Bvar, Body}) = (check Bvar; check Body)
      | check (Constrained(tm,ty)) =
          (check tm; TCPretype.unify (type_of tm) ty
            handle (e as Exception.HOL_ERR{origin_structure="Type",
                                           origin_function="unify",message})
            => let val tmp = !Globals.show_types
                   val _ = Globals.show_types := true
               in
               Lib.say "\nType inference failure: the term\n\n";
               ptm (to_term tm); Lib.say "\n\n";
               if (is_atom tm) then ()
               else(Lib.say"which has type\n\n";pty(type_of tm);Lib.say"\n\n");
               Lib.say "can not be constrained to be of type\n\n";
               pty ty;
               Lib.say ("\n\nunification failure message: "^message^"\n");
               Globals.show_types := tmp;
               raise PRETERM_ERR"typecheck" "failed"
               end)
      | check _ = ()
in check
end end;

(*---------------------------------------------------------------------------
 * Post-type inference processing. Currently, this just guesses type
 * variables for the remaining unconstrained type variables.
 *---------------------------------------------------------------------------*)

fun clean shr = let
  fun cl(Var{Name,Ty})      = Term.mk_var{Name=Name,  Ty=shr Ty}
    | cl(Const{Name,Ty})    = Term.mk_const{Name=Name,Ty=shr Ty}
    | cl(Comb{Rator,Rand})  = Term.mk_comb{Rator=cl Rator,Rand=cl Rand}
    | cl(Abs{Bvar,Body})    = Term.mk_abs{Bvar=cl Bvar,Body=cl Body}
    | cl(Antiq tm)          = tm
    | cl(Constrained(tm,_)) = cl tm
in
  cl
end;


fun has_unconstrained_uvar ty = let
  open TCPretype
in
  case ty of
    Tyop(s, args) => List.exists has_unconstrained_uvar args
  | UVar(ref NONE) => true
  | UVar(ref (SOME t)) => has_unconstrained_uvar t
  | Vartype _ => false
end

fun tyVars tm =
  case tm of
    Var{Ty,...} => TCPretype.tyvars Ty
  | Const{Ty,...} => TCPretype.tyvars Ty
  | Comb{Rator,Rand} => Lib.union (tyVars Rator) (tyVars Rand)
  | Abs{Bvar,Body} => Lib.union (tyVars Bvar) (tyVars Body)
  | Antiq tm => map Type.dest_vartype (Term.type_vars_in_term tm)
  | Constrained(tm,ty) => Lib.union (tyVars tm) (TCPretype.tyvars ty)

fun cleanup tm =
  if !Globals.guessing_tyvars then let
    val V = tyVars tm
    fun cleanup tm = let
      open optmonad TCPretype
      val clean = clean o remove_made_links
      infix >> >-
    in
      case tm of
        Var{Name, Ty} =>
          replace_null_links Ty >-
          (fn _ => return (Term.mk_var{Name = Name, Ty = clean Ty}))
      | Const{Name, Ty} =>
          replace_null_links Ty >-
          (fn _ => return (Term.mk_const{Name = Name, Ty = clean Ty}))
      | Comb{Rator, Rand} =>
          cleanup Rator >-
          (fn Rator' => cleanup Rand >-
           (fn Rand' => return (Term.mk_comb{Rator=Rator', Rand=Rand'})))
      | Abs{Bvar, Body} =>
          cleanup Bvar >-
          (fn Bvar' => cleanup Body >-
           (fn Body' => return (Term.mk_abs{Bvar = Bvar', Body = Body'})))
      | Antiq t => return t
      | Constrained(tm, ty) => cleanup tm
    end
    val (newV, result) = cleanup tm V
    val guessed_vars = List.take(newV, length newV - length V)
    val _ =
      Lib.mesg (not (null guessed_vars) andalso !Globals.notify_on_tyvar_guess)
      ("inventing new type variable names: " ^
       String.concat(Lib.commafy (List.rev guessed_vars)))
  in
    valOf result
  end
 else let
   fun shr ty =
     if has_unconstrained_uvar ty then
       raise PRETERM_ERR"typecheck.cleanup"
         "Unconstrained type variable (and Globals.guessing_tyvars is false)."
     else let
       open TCPretype
     in
       clean (remove_made_links ty)
     end
 in
   clean shr tm
 end


fun typecheck pfns tm = (TC pfns tm; cleanup tm);

end; (* PRETERM *)
