structure Preterm :> Preterm =
struct

open Exception Lib;

fun PRETERM_ERR function message =
 Exception.HOL_ERR{origin_structure = "Preterm",
                   origin_function = function,
                   message = message};


datatype preterm = Var   of {Name : string,  Ty : Type.hol_type}
                 | Const of {Name : string,  Ty : Type.hol_type}
                 | Comb  of {Rator: preterm, Rand : preterm}
                 | Abs   of {Bvar : preterm, Body : preterm}
                 | Constrained of preterm * Type.hol_type
                 | Antiq of Term.term

(*---------------------------------------------------------------------------*
 * Getting "hidden" functions from Type and Term.                            *
 *---------------------------------------------------------------------------*)
local open Type
      val dty = Type.mk_vartype"'x"
      val dtm = Term.mk_var{Name="dummy",Ty=dty}
      val unify_ref = ref (fn _:hol_type => fn _:hol_type => ())
      val shrink_type_ref =
           ref (fn _:(hol_type*hol_type) list => fn _:hol_type => dty)
      val chase_ref = ref (fn _:hol_type => dty)
      val tyvars_ref = ref (fn _:hol_type => fn x:hol_type list => x)
      val constify_ref = ref (fn{Name:string,Ty:hol_type} => dtm)
      val Combify_ref = ref (fn{Rator:Term.term,Rand:Term.term} => dtm)
      val _ = Type.Preterm_init unify_ref shrink_type_ref chase_ref tyvars_ref
      val _ = Term.Preterm_init constify_ref Combify_ref
in
  val unify = !unify_ref
  val shrink_type = !shrink_type_ref
  val chase = !chase_ref
  val tyvars = !tyvars_ref

  val constify = !constify_ref
  val Combify = !Combify_ref
end;


(*---------------------------------------------------------------------------
 * Translation to terms so that the term prettyprinter can be used when
 * type inference fails.
 *---------------------------------------------------------------------------*)
fun to_term (Var n) = Term.mk_var n
  | to_term (Const r) = constify r
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
local val --> = Type.-->
      infix  -->
      fun type_of (Var{Ty, ...}) = Ty
        | type_of (Const{Ty, ...}) = Ty
        | type_of (Comb{Rator, ...}) = chase (type_of Rator)
        | type_of (Abs{Bvar,Body}) = type_of Bvar --> type_of Body
        | type_of (Constrained(_,ty)) = ty
        | type_of (Antiq tm) = Term.type_of tm
in
fun TC tyvars =
let fun check(Comb{Rator, Rand}) =
        (check Rator; check Rand;
         unify (type_of Rator)
               (type_of Rand --> Lib.state(Lib.next tyvars))
         handle (e as Exception.HOL_ERR{origin_structure="Type",
                                        origin_function="unify",message})
         => let val tmp = !Globals.show_types
                val _   = Globals.show_types := true
                val ptm = Lib.say o Hol_pp.term_to_string
                val pty = Lib.say o Hol_pp.type_to_string
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
          (check tm; unify (type_of tm) ty
            handle (e as Exception.HOL_ERR{origin_structure="Type",
                                           origin_function="unify",message})
            => let val tmp = !Globals.show_types
                   val _ = Globals.show_types := true
                   val ptm = Lib.say o Hol_pp.term_to_string
                   val pty = Lib.say o Hol_pp.type_to_string
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

local fun string_tl str = Portable_String.substring(str,1, size str - 1)
      val ascii_dollar = ordof("$",0)
in
fun zap_dollar s =
 if (s="") then raise PRETERM_ERR"zap_dollar" "empty string"
  else if (ordof(s,0) = ascii_dollar) then string_tl s
    else s
end;

val tyVars =
 let fun union [] S = S
       | union S [] = S
       | union (h::t) S = union t (insert h S)
     fun tyV (Var{Ty,...}) L       = tyvars Ty L
       | tyV (Const{Ty,...}) L     = tyvars Ty L
       | tyV (Comb{Rator,Rand}) L  = tyV Rand(tyV Rator L)
       | tyV (Abs{Bvar,Body}) L    = tyV Body(tyV Bvar L)
       | tyV (Antiq tm) L          = union (Term.type_vars_in_term tm) L
       | tyV (Constrained(tm,_)) L = tyV tm L
 in rev o C tyV []
 end;

local fun askii n = Portable_Char.toString(Char.chr (n + 97));
      fun nonzero 0 = "" | nonzero n = Int.toString n;
      nonfix div mod
      val div = Portable_Int.div and mod = Portable_Int.mod
in
fun num2tyv m = Type.mk_vartype
  (Portable_String.concat(["'",askii(mod(m,26)), nonzero(div(m,26))]))
end;


(*---------------------------------------------------------------------------
 * Use the "src" stream to generate new elements, not in "taken", up to
 * the quantity equal to the length of the list (1st parameter to V). The
 * 2nd parameter to V is just the accumulator, which is not hidden.
 *---------------------------------------------------------------------------*)
fun vary src taken =
  let fun V [] fresh = rev fresh
        | V (_::rst) fresh =
             let val _ = while (mem (state src) taken) do next src
                 val v' = state src before (next src; ())
             in V rst (v'::fresh)
             end
  in  V  end;


fun clean shr =
  let fun cl(Var{Name,Ty})      = Term.mk_var{Name=zap_dollar Name,  Ty=shr Ty}
        | cl(Const{Name,Ty})    = Term.mk_const{Name=zap_dollar Name,Ty=shr Ty}
        | cl(Comb{Rator,Rand})  = Term.mk_comb{Rator=cl Rator,Rand=cl Rand}
        | cl(Abs{Bvar,Body})    = Term.mk_abs{Bvar=cl Bvar,Body=cl Body}
        | cl(Antiq tm)          = tm
        | cl(Constrained(tm,_)) = cl tm
  in cl
  end;

fun cleanup tm =
 if !Globals.guessing_tyvars
 then let val V = tyVars tm
          val (utvs,stvs) = Lib.partition Type.is_vartype V
          val utv_src = mk_istream (fn x => x+1) 0 num2tyv
          val new_utvs = vary utv_src utvs stvs []
          val _ = Lib.mesg (not(null stvs) andalso
                            !Globals.notify_on_tyvar_guess)
             ("inventing new type variable names: "
               ^String.concat(Lib.commafy (map Type.dest_vartype new_utvs)))
      in
         clean (shrink_type (zip stvs new_utvs)) tm
      end
 else clean (shrink_type []) tm handle HOL_ERR _
      => raise PRETERM_ERR"typecheck.cleanup"
        "Unconstrained type variable (and Globals.guessing_tyvars is false).";


fun typecheck fresh_tyvs tm = (TC fresh_tyvs tm; cleanup tm);

end; (* PRETERM *)
