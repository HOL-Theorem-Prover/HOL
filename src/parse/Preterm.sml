structure Preterm :> Preterm =
struct

open Feedback Lib GrammarSpecials;

val ERR = mk_HOL_ERR "Preterm"


type pretype = Pretype.pretype
type hol_type = Type.hol_type
type term = Term.term

datatype preterm = Var   of {Name:string,  Ty:pretype}
                 | Const of {Name:string,  Thy:string, Ty:pretype}
                 | Overloaded of {Name:string, Ty:pretype,
                                  Info:Overload.overloaded_op_info}
                 | Comb  of {Rator:preterm, Rand:preterm}
                 | Abs   of {Bvar:preterm, Body:preterm}
                 | Constrained of preterm * pretype
                 | Antiq of Term.term


(*---------------------------------------------------------------------------
     Simple map from a preterm to a term. The argument "shr" maps from
     pretypes to types. Should Overloaded nodes be translated, or
     should the process fail if one is encountered? Currently, we
     attempt to make some sort of constant (non-deterministic), but we
     could just as well fail, since Overloaded nodes should be gone
     by the time clean is called.
 ---------------------------------------------------------------------------*)

fun clean shr = 
 let fun 
   cl(Var{Name,Ty})       = Term.mk_var(Name, shr Ty)
 | cl(Const{Name,Thy,Ty}) = Term.mk_thy_const{Name=Name,Thy=Thy,Ty=shr Ty}
 | cl(Comb{Rator,Rand})   = Term.mk_comb(cl Rator,cl Rand)
 | cl(Abs{Bvar,Body})     = Term.mk_abs(cl Bvar, cl Body)
 | cl(Antiq tm)           = tm
 | cl(Constrained(tm,_))  = cl tm
 | cl(Overloaded{Name,Ty,...}) = Term.mk_const(Name, shr Ty)
 in cl
 end;

local open Pretype
in
fun has_free_uvar (Tyop(s,A))         = List.exists has_free_uvar A
  | has_free_uvar (UVar(ref(SOME t))) = has_free_uvar t
  | has_free_uvar (UVar(ref NONE))    = true
  | has_free_uvar (Vartype _)         = false
end

fun tyVars ptm =  (* the pretype variables in a preterm *)
  case ptm of
    Var{Ty,...}         => Pretype.tyvars Ty
  | Const{Ty,...}       => Pretype.tyvars Ty
  | Comb{Rator,Rand}    => Lib.union (tyVars Rator) (tyVars Rand)
  | Abs{Bvar,Body}      => Lib.union (tyVars Bvar) (tyVars Body)
  | Antiq tm            => map Type.dest_vartype (Term.type_vars_in_term tm)
  | Constrained(ptm,ty) => Lib.union (tyVars ptm) (Pretype.tyvars ty)
  | Overloaded _        => raise Fail "Preterm.tyVars: applied to Overloaded"


(*---------------------------------------------------------------------------
    Translate a preterm to a term. Will "guess type variables"
    (assign names to type variables created during type inference),
    if a flag is set. No "Overloaded" nodes are allowed in the preterm:
    overloading resolution should already have gotten rid of them.
 ---------------------------------------------------------------------------*)

fun to_term tm =
 if !Globals.guessing_tyvars
 then
 let fun cleanup tm =
       let open optmonad infix >> >-
           val clean = Pretype.clean o Pretype.remove_made_links
       in case tm 
           of Var{Name,Ty} => Pretype.replace_null_links Ty >- (fn _ 
               => return (Term.mk_var(Name, clean Ty)))
            | Const{Name,Thy,Ty} => Pretype.replace_null_links Ty >- (fn _ 
               => return (Term.mk_thy_const{Name=Name, Thy=Thy, Ty=clean Ty}))
            | Comb{Rator, Rand} => cleanup Rator >- (fn Rator' 
                                => cleanup Rand  >- (fn Rand'  
                  => return (Term.mk_comb(Rator', Rand'))))
            | Abs{Bvar, Body} => cleanup Bvar >- (fn Bvar' 
                              => cleanup Body >- (fn Body' 
                  => return (Term.mk_abs(Bvar', Body'))))
            | Antiq t => return t
            | Constrained(tm, ty) => cleanup tm
            | Overloaded _ => raise ERR "to_term" "applied to Overloaded"
       end
    val V = tyVars tm
    val (newV, result) = cleanup tm V
    val guessed_vars = List.take(newV, length newV - length V)
    val _ =
      if not (null guessed_vars) andalso !Globals.notify_on_tyvar_guess
      then Feedback.HOL_MESG (String.concat
              ("inventing new type variable names: "
               :: Lib.commafy (List.rev guessed_vars)))
      else ()
 in
    valOf result
 end
 else
 let fun shr ty =
      if has_free_uvar ty
      then raise ERR"typecheck.to_term"
         "Unconstrained type variable (and Globals.guessing_tyvars is false)"
      else Pretype.clean (Pretype.remove_made_links ty)
 in
   clean shr tm
 end




(*---------------------------------------------------------------------------*
 *                                                                           *
 * Overloading removal.  Th function "remove_overloading_phase1" will        *
 * replace Overloaded _ nodes with Consts where it can be shown that only    *
 * one of the possible constants has a type compatible with the type of the  *
 * term as it has been inferred during the previous phase of type inference. *
 * This may in turn constrain other overloaded terms elsewhere in the tree.  *
 *                                                                           *
 *---------------------------------------------------------------------------*)

fun remove_overloading_phase1 ptm =
  case ptm of
    Comb{Rator, Rand} => Comb{Rator = remove_overloading_phase1 Rator,
                              Rand = remove_overloading_phase1 Rand}
  | Abs{Bvar, Body} => Abs{Bvar = remove_overloading_phase1 Bvar,
                           Body = remove_overloading_phase1 Body}
  | Constrained(tm,ty) => Constrained(remove_overloading_phase1 tm, ty)
  | Overloaded{Name,Ty,Info} =>
     let fun testfn possty =
           let val pty0 = Pretype.fromType possty
               val pty = Pretype.rename_typevars pty0
           in Pretype.can_unify Ty pty
           end
         val possible_ops =
           List.filter (testfn o #Ty) (#actual_ops Info)
     in
      case possible_ops of
        [] =>
          (Lib.say ("\nNo possible type for overloaded constant "^Name^"\n");
           raise ERR "typecheck" "failed")
      | [{Ty = ty,Name,Thy}] => let
          val pty = Pretype.rename_typevars (Pretype.fromType ty)
          val _ = Pretype.unify pty Ty
        in
          Const{Name=Name, Thy=Thy, Ty=pty}
        end
      | _ =>
        Overloaded{Name=Name, Ty=Ty,
                   Info=Overload.fupd_actual_ops (fn _ => possible_ops) Info}
     end
  | _ => ptm;


fun remove_overloading ptm = let
  open seqmonad
  infix >- >> ++
  fun opt2seq m env =
    case m env of
      (env', NONE) => seq.empty
    | (env', SOME result) => seq.result (env', result)
  fun unify t1 t2 = opt2seq (Pretype.safe_unify t1 t2)
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
  val _ = if length overloads >= 30
          then HOL_WARNING "Preterm" "remove_overloading"
           (String.concat["many overloaded symbols in term: ",
                          "overloading resolution might take a long time."])
          else ()
  fun workfunction list =
    case list of
      [] => return []
    | {Name,Ty,Info,...}::xs => let
        val actual_ops = #actual_ops Info
        fun tryit {Ty = ty, Name = n, Thy = thy} =
          let val pty0 = Pretype.fromType ty
              val pty = Pretype.rename_typevars pty0
          in unify pty Ty >> return (Const{Name=n, Ty=Ty, Thy=thy})
          end
      in
        tryall tryit actual_ops >- (fn c =>
        workfunction xs >- (fn cs =>
        return (c::cs)))
      end
in
  workfunction overloads
end

fun do_overloading_removal ptm0 = let
  open seq
  val ptm = remove_overloading_phase1 ptm0
  val result = remove_overloading ptm []
  fun apply_subst subst = app (fn (r, value) => r := SOME value) subst
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
    NONE => raise ERR "do_overloading_removal"
      "Couldn't find a sensible resolution for overloaded constants"
  | SOME ((env,clist),xs) =>
      if not (!Globals.guessing_overloads)
         orelse !Globals.notify_on_tyvar_guess
      then
        case cases xs
         of NONE => (apply_subst env; #1 (do_csubst clist ptm))
          | SOME _ => let in
              if not (!Globals.guessing_overloads)
                 then raise ERR "do_overloading_removal"
                         "More than one resolution of overloading possble"
                 else ();
              Feedback.HOL_MESG
                    "more than one resolution of overloading was possible";
              apply_subst env;
              #1 (do_csubst clist ptm)
            end
      else
        (apply_subst env; #1 (do_csubst clist ptm))
end

fun remove_elim_magics ptm =
  case ptm of
    Var _ => ptm
  | Const _ => ptm
  | Antiq _ => ptm
  | Comb{Rator = (rator as Const{Name, ...}), Rand = ptm1} =>
      if Name = nat_elim_term then ptm1
      else Comb{Rator = rator, Rand = remove_elim_magics ptm1}
  | Comb{Rator, Rand} => Comb{Rator = remove_elim_magics Rator,
                              Rand = remove_elim_magics Rand}
  | Abs{Bvar, Body} => Abs{Bvar = remove_elim_magics Bvar,
                           Body = remove_elim_magics Body}
  | Constrained(tm, ty) => Constrained(remove_elim_magics tm, ty)
  | Overloaded _ => raise Fail "Preterm.remove_elim_magics on Overloaded"


val overloading_resolution = remove_elim_magics o do_overloading_removal


(*---------------------------------------------------------------------------
 * Type inference for HOL terms. Looks ugly because of error messages, but is
 * actually very simple, given side-effecting unification.
 *---------------------------------------------------------------------------*)

fun is_atom (Var _) = true
  | is_atom (Const _) = true
  | is_atom (Constrained(tm,_)) = is_atom tm
  | is_atom (Overloaded _) = true
  | is_atom (t as Comb{Rator,Rand}) =
      Numeral.is_numeral (to_term (overloading_resolution t)) orelse
      Numeral.is_numeral (to_term (overloading_resolution Rand)) andalso
        (case Rator
          of Overloaded{Name,...} => Name = fromNum_str
           | Const{Name,...} => Name = nat_elim_term
           | _ => false)
  | is_atom t = false


local fun -->(ty1,ty2) = Pretype.Tyop("fun", [ty1, ty2])
      infix  -->
      fun type_of (Var{Ty, ...}) = Ty
        | type_of (Const{Ty, ...}) = Ty
        | type_of (Comb{Rator, ...}) = Pretype.chase (type_of Rator)
        | type_of (Abs{Bvar,Body}) = type_of Bvar --> type_of Body
        | type_of (Constrained(_,ty)) = ty
        | type_of (Antiq tm) = Pretype.fromType (Term.type_of tm)
        | type_of (Overloaded {Ty,...}) = Ty
      fun default_typrinter x = "<hol_type>"
      fun default_tmprinter x = "<term>"
in
fun TC printers =
 let val (ptm, pty) =
      case printers
       of SOME (x,y) =>
           let val typrint = Lib.say o y o Pretype.toType
               fun tmprint tm =
                  if Term.is_const tm
                     then (Lib.say (x tm ^ " " ^ y (Term.type_of tm)))
                     else Lib.say (x tm)
           in
              (tmprint, typrint)
           end
        | NONE => (Lib.say o default_tmprinter, Lib.say o default_typrinter)
  fun check(Comb{Rator, Rand}) =
      (check Rator;
       check Rand;
       Pretype.unify (type_of Rator)
       (type_of Rand --> Pretype.new_uvar())
       handle (e as Feedback.HOL_ERR{origin_structure="Pretype",
                                     origin_function="unify",message})
       => let val tmp = !Globals.show_types
              val _   = Globals.show_types := true
              val Rator' = to_term (overloading_resolution Rator)
              val Rand'  = to_term (overloading_resolution Rand)
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
            raise ERR"typecheck" "failed"
          end)
    | check (Abs{Bvar, Body}) = (check Bvar; check Body)
    | check (Constrained(tm,ty)) =
       (check tm; Pretype.unify (type_of tm) ty
       handle (e as Feedback.HOL_ERR{origin_structure="Pretype",
                                    origin_function="unify",message})
       => let val tmp = !Globals.show_types
              val _ = Globals.show_types := true
              val real_term = to_term (overloading_resolution tm)
                handle HOL_ERR _ =>
                  raise ERR "typecheck" "internal to_term failed"
          in
            Lib.say "\nType inference failure: the term\n\n";
            ptm real_term; Lib.say "\n\n";
            if (is_atom tm) then ()
            else(Lib.say"which has type\n\n";pty(type_of tm);Lib.say"\n\n");
            Lib.say "can not be constrained to be of type\n\n";
            pty ty;
            Lib.say ("\n\nunification failure message: "^message^"\n");
            Globals.show_types := tmp;
            raise ERR"typecheck" "failed"
          end)
    | check _ = ()
in check
end end;

val typecheck_phase1 = TC



fun typecheck pfns ptm = (TC pfns ptm; to_term(overloading_resolution ptm));

end; (* Preterm *)

(* test the overloading :

new_definition ("f", Term`f p q x = p x /\ q x`);
allow_for_overloading_on ("/\\", Type`:'a -> 'a -> 'a`);
overload_on ("/\\", mk_const{Name = "/\\", Ty = Type`:bool->bool->bool`});
Term`p /\ q`;
overload_on ("/\\", Term`f`);

*)
