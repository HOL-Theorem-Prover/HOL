structure Preterm :> Preterm =
struct

open Exception Lib;

open GrammarSpecials

fun PRETERM_ERR function message =
 Exception.HOL_ERR{origin_structure = "Preterm",
                   origin_function = function,
                   message = message};


type pretype = TCPretype.pretype

datatype preterm = Var   of {Name : string,  Ty : pretype}
                 | Const of {Name : string,  Ty : pretype}
                 | Overloaded of {Name : string, Ty : pretype,
                                  Info : Overload.overloaded_op_info}
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
  | to_term (Overloaded {Name,Ty,...}) =
      constify (ptremove {Name = Name, Ty = Ty})
  | to_term (t as Comb{Rator,Rand}) = let
    in
      case Rator of
        Const{Name,...} => if Name = nat_elim_term then to_term Rand
                           else Combify{Rator=to_term Rator,Rand=to_term Rand}
      | _ => Combify{Rator = to_term Rator, Rand = to_term Rand}
    end
  | to_term (Abs{Bvar,Body}) = Term.mk_abs{Bvar=to_term Bvar,Body=to_term Body}
  | to_term (Antiq tm) = tm
  | to_term (Constrained(tm,_)) = to_term tm;


fun is_atom (Var _) = true
  | is_atom (Const _) = true
  | is_atom (Constrained(tm,_)) = is_atom tm
  | is_atom (Overloaded _) = true
  | is_atom (t as Comb{Rator,Rand}) = let
    in
      Term.is_numeral (to_term t) orelse
      Term.is_numeral (to_term Rand) andalso
        (case Rator of
           Overloaded{Name,...} => Name = fromNum_str
         | Const{Name,...} => Name = nat_elim_term
         | _ => false)
    end
  | is_atom t = false


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
        | type_of (Overloaded {Ty,...}) = Ty
in
fun TC printers = let
  fun default_typrinter x = "<hol_type>"
  fun default_tmprinter x = "<term>"
  val (ptm, pty) =
    case printers of
      SOME (x,y) => let
        val typrint = Lib.say o y o TCPretype.toType
        fun tmprint tm =
          if Term.is_const tm then
            (Lib.say (x tm ^ " " ^ y (Term.type_of tm)))
          else Lib.say (x tm)
      in
        (tmprint, typrint)
      end
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
            handle (e as Exception.HOL_ERR{origin_structure="TCPretype",
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

val typecheck_phase1 = TC

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
    | cl(Overloaded{Name,Ty,...}) = Term.mk_const{Name=Name, Ty = shr Ty}
in
  cl
end;

fun remove_overloading_phase1 ptm = let
  (* this function will replace Overloaded _ nodes with Consts where it
     can be shown that only one of the possible constants has a type
     compatible with the type of the term as it has been inferred during
     the previous phase of type inference.  This may in turn constrain
     other overloaded terms elsewhere in the tree *)
in
  case ptm of
    Comb{Rator, Rand} => Comb{Rator = remove_overloading_phase1 Rator,
                              Rand = remove_overloading_phase1 Rand}
  | Abs{Bvar, Body} => Abs{Bvar = remove_overloading_phase1 Bvar,
                           Body = remove_overloading_phase1 Body}
  | Constrained(tm,ty) => Constrained(remove_overloading_phase1 tm, ty)
  | Overloaded{Name,Ty,Info} => let
      fun testfn possty = let
        val pty0 = TCPretype.fromType possty
        val pty = TCPretype.rename_typevars pty0
      in
        TCPretype.can_unify Ty pty
      end
      val possible_ops =
        List.filter (fn (ty,n) => testfn ty) (#actual_ops Info)
    in
      case possible_ops of
        [] =>
          (Lib.say ("\nNo possible type for overloaded constant "^Name^"\n");
           raise PRETERM_ERR "typecheck" "failed")
      | [(ty,n)] => let
          val pty = TCPretype.rename_typevars (TCPretype.fromType ty)
          val _ = TCPretype.unify pty Ty
        in
          Const{Name = n, Ty = pty}
        end
      | _ =>
        Overloaded{Name = Name, Ty = Ty,
                   Info = Overload.fupd_actual_ops (fn _ => possible_ops) Info}
    end
  | _ => ptm
end



fun remove_overloading ptm = let
  open seqmonad
  infix >- >> ++
  fun opt2seq m env =
    case m env of
      (env', NONE) => seq.empty
    | (env', SOME result) => seq.result (env', result)
  fun unify t1 t2 = opt2seq (TCPretype.safe_unify t1 t2)
  (* Note that the order of the term traversal here is very important as
     the sub-terms "pulled out" will be "put back in" later under the
     assumption that the list is in the right order.  The traversal that
     puts the constants into the place of the Overloaded nodes must also
     traverse in the same order:
       Rator before Rand, Bvar before Body
     In accumulator style, that looks as below *)
  fun overloaded_subterms acc ptm =
    case ptm of
      Overloaded x => x::acc
    | Comb{Rator, Rand} =>
        overloaded_subterms (overloaded_subterms acc Rand) Rator
    | Abs{Bvar,Body} =>
        overloaded_subterms (overloaded_subterms acc Body) Bvar
    | Constrained(tm,_) => overloaded_subterms acc tm
    | _ => acc
  val overloads = overloaded_subterms [] ptm
  val _ =
      Lib.mesg (length overloads >= 30)
      "warning: overloading resolution might have >1 billion choices"
  fun workfunction list =
    case list of
      [] => return []
    | {Name,Ty,Info}::xs => let
        val actual_ops = #actual_ops Info
        fun tryit (ty, n) = let
          val pty0 = TCPretype.fromType ty
          val pty = TCPretype.rename_typevars pty0
        in
          unify pty Ty >> return (Const{Name=n, Ty=Ty})
        end
      in
        tryall tryit actual_ops >-
        (fn c => workfunction xs >-
         (fn cs => return (c::cs)))
      end
in
  workfunction overloads
end

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
  | Overloaded _ => raise Fail "Preterm.tyVars: applied to Overloaded"

fun do_overloading_removal ptm0 = let
  open seq
  val ptm = remove_overloading_phase1 ptm0
  val result = remove_overloading ptm []
  fun apply_subst subst =
    app (fn (r, value) => r := SOME value) subst
  fun do_csubst clist ptm =
    case clist of
      [] => (ptm, [])
    | (c::cs) => let
      in
        (* must take care to keep order of traversal same as traversal in
           overloaded_subterms above *)
        case ptm of
          Comb{Rator, Rand} => let
            (* Rator before Rand *)
            val (Rator', clist') = do_csubst clist Rator
            val (Rand', clist'') = do_csubst clist' Rand
          in
            (Comb{Rator = Rator', Rand = Rand'}, clist'')
          end
        | Abs{Bvar, Body} => let
            (* Bvar before Body *)
            val (Bvar', clist') = do_csubst clist Bvar
            val (Body', clist'') = do_csubst clist' Body
          in
            (Abs{Bvar = Bvar', Body = Body'}, clist'')
          end
        | Constrained(tm,ty) => let
            val (tm', clist') = do_csubst clist tm
          in
            (Constrained(tm', ty), clist')
          end
        | Overloaded _ => (c,cs)
        | _ => (ptm, clist)
      end
in
  case cases result of
    NONE => raise PRETERM_ERR "do_overloading_removal"
      "Couldn't find a sensible resolution for overloaded constants"
  | SOME ((env,clist),xs) => let
    in
      if not (!Globals.guessing_overloads) orelse
         !Globals.notify_on_tyvar_guess
      then
        case cases xs of
          NONE => (apply_subst env; #1 (do_csubst clist ptm))
        | SOME _ => (if (not (!Globals.guessing_overloads)) then
                       raise PRETERM_ERR "do_overloading_removal"
                         "More than one resolution of overloading possble"
                     else ();
                     Lib.mesg true
                       "more than one resolution of overloading was possible";
                     apply_subst env;
                     #1 (do_csubst clist ptm))
      else
        (apply_subst env; #1 (do_csubst clist ptm))
    end
end

fun remove_elim_magics ptm =
  case ptm of
    Var _ => ptm
  | Const _ => ptm
  | Antiq _ => ptm
  | Comb{Rator = (rator as Const{Name, Ty}), Rand = ptm1} =>
      if Name = nat_elim_term then ptm1
      else Comb{Rator = rator, Rand = remove_elim_magics ptm1}
  | Comb{Rator, Rand} => Comb{Rator = remove_elim_magics Rator,
                              Rand = remove_elim_magics Rand}
  | Abs{Bvar, Body} => Abs{Bvar = remove_elim_magics Bvar,
                           Body = remove_elim_magics Body}
  | Constrained(tm, ty) => Constrained(remove_elim_magics tm, ty)
  | Overloaded _ => raise Fail "Preterm.remove_elim_magics on Overloaded"

val cleanup0 = remove_elim_magics o do_overloading_removal
val overloading_resolution = cleanup0

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
      | Overloaded _ => raise PRETERM_ERR "toTerm" "applied to Overloaded"
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

fun overloading_resolution ptm = cleanup0 ptm

val toTerm = cleanup

fun typecheck pfns tm = let
  val _ = TC pfns tm
in
  cleanup (cleanup0 tm)
end

end; (* PRETERM *)

(* test the overloading :

new_definition ("f", Term`f p q x = p x /\ q x`);
allow_for_overloading_on ("/\\", Type`:'a -> 'a -> 'a`);
overload_on ("/\\", mk_const{Name = "/\\", Ty = Type`:bool->bool->bool`});
Term`p /\ q`;
overload_on ("/\\", Term`f`);

*)