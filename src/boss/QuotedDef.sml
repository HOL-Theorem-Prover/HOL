structure QuotedDef :> QuotedDef =
struct

open HolKernel Parse basicHol90Lib ;

  type term     = Term.term
  type thm      = Thm.thm
  type tactic   = Abbrev.tactic
  type defn     = Defn.defn
  type proofs   = GoalstackPure.proofs
  type 'a quotation = 'a Portable.frag list 

infix THEN THENL ORELSE |->;
infixr -->;

fun DEF_ERR func mesg =
     HOL_ERR{origin_structure = "QuotedDef",
             origin_function = func,
             message = mesg};

val ind_suffix = ref "ind";
val def_suffix = ref "def";


(*---------------------------------------------------------------------------*
 * Try to find the names of to-be-defined constants from a quotation.        *
 * First, parse into type "parse_term", then look for names on the lhs       *
 * of the definition.                                                        *
 *---------------------------------------------------------------------------*)

local open parse_term
in
fun dest_binop str =
  let fun dest (COMB(COMB(VAR s, l),r)) 
           = if s=str then (l,r) 
             else raise DEF_ERR "dest_binop" ("Expected a "^Lib.quote str)
        | dest  _ = raise DEF_ERR "dest_binop"  ""
  in dest end
fun dest_binder str =
  let fun dest (COMB(VAR s, ABS p)) 
           = if s=str then p
             else raise DEF_ERR "dest_binder" ("Expected a "^Lib.quote str)
        | dest  _ = raise DEF_ERR "dest_binder"  ""
  in dest end
fun ptm_dest_conj ptm   = dest_binop  "/\\" ptm
fun ptm_dest_eq ptm     = dest_binop  "=" ptm
fun ptm_dest_forall ptm = dest_binder "!" ptm

fun ptm_dest_var(VAR s) = s
  | ptm_dest_var _ =  raise DEF_ERR "ptm_dest_comb" "Expected a VAR"

fun ptm_dest_comb (COMB(l,r)) = (l,r)
  | ptm_dest_comb   _ = raise DEF_ERR "ptm_dest_comb" "Expected a COMB"
end;

fun ptm_is_eq tm = Lib.can ptm_dest_eq tm;


fun ptm_strip dest =
  let fun strip ptm =
       let val (l,r) = dest ptm 
       in l::strip r
       end handle HOL_ERR _ => [ptm];
  in strip
  end;

fun ptm_strip_conj ptm = ptm_strip ptm_dest_conj ptm;

fun ptm_strip_comb ptm =
   let fun strip ptm A =
         let val (l,r) = ptm_dest_comb ptm 
         in strip l (r::A)
         end handle HOL_ERR _ => (ptm,A)
  in strip ptm []
  end;


fun ptm_strip_binder dest =
  let fun strip ptm =
       let val (l,r) = dest ptm 
           val (L,M) = strip r
       in (l::L,M)
       end handle HOL_ERR _ => ([],ptm)
  in strip
  end;
fun ptm_strip_forall ptm = ptm_strip_binder ptm_dest_forall ptm;


fun dollar s = "$"^s;
fun drop_dollar s =
   (if String.sub(s,0) = #"$"
    then String.substring(s,1,String.size s)
    else s)
  handle _ => raise DEF_ERR "drop_dollar" "unexpected string"

fun dest_atom tm =
  #Name(dest_var tm handle HOL_ERR _ => dest_const tm);

fun preview qthing =
 let fun preev (q as [QUOTE _]) =
         let val ptm = Parse.parse_preTerm q
             val eqs = ptm_strip_conj ptm
             val L = map (fst o ptm_dest_eq o snd o ptm_strip_forall) eqs
         in
           map (ptm_dest_var o fst o ptm_strip_comb) L
         end
       | preev qtm =  (* not clear that this is useful *)
          let val tm = Parse.Term qtm
              val eqs = strip_conj tm
              open Psyntax
              val L = map (fst o dest_eq o snd o strip_forall) eqs
          in
            map (dest_atom o fst o strip_comb) L
          end
 in 
    mk_set (map drop_dollar (preev qthing))
     handle HOL_ERR _ 
     => raise DEF_ERR "preview" 
             "unable to find name of function(s) to be defined"
end;

(*---------------------------------------------------------------------------
      MoscowML returns lists of QUOTE'd strings when a quote is spread 
      over more than one line. "norm_quotel" concatenates all adjacent
      QUOTE elements in this list. 
 ---------------------------------------------------------------------------*)

fun norm_quotel [] = []
  | norm_quotel [x] = [x]
  | norm_quotel (QUOTE s1::QUOTE s2::rst) = norm_quotel (QUOTE(s1^s2)::rst)
  | norm_quotel (h::rst) = h::norm_quotel rst;

fun Hol_fun bindstem ql = 
 let fun eqs qtm =
           let val names = preview qtm
               val allnames = map dollar names @ names
               val _ = List.app Parse.hide allnames
               val eqs = Parse.Term qtm 
                     handle e => (List.app Parse.reveal allnames; raise e)
               val _ = List.app Parse.reveal allnames
           in 
             eqs
           end 
 in
    Defn.define bindstem (eqs (norm_quotel ql))
 end;


fun const_of th =
  let val hd_eqn = 
       snd(strip_imp(snd(strip_forall(hd(strip_conj(concl th))))))
  in
    fst(strip_comb(#lhs(dest_eq hd_eqn)))
  end;

fun constants_of defn =
  let val eqns = Defn.eqns_of defn
      val nest_eqns = case Defn.aux_defn defn
                       of NONE => [] 
                        | SOME nest => [Defn.eqns_of nest]
      val mut_eqns = case Defn.union_defn defn
                      of NONE => [] 
                       | SOME mut => 
                           Defn.eqns_of mut 
                            ::(case Defn.aux_defn mut
                                of NONE => []
                                 | SOME nest => [Defn.eqns_of nest])
      val alleqns = eqns::(nest_eqns@mut_eqns)
      val consts = map const_of alleqns
  in 
      consts
  end;


(*---------------------------------------------------------------------------
    xDefine bindstem ` ... ` operates as follows:

        1. It makes the definition, using Hol_fun.
        2. If the definition is not recursive or is
           primitive recursive, the defining equations are 
           stored under bindstem_def (and returned).
        3. Otherwise, we check to see if the definition
           is schematic. If so, the induction theorem is stored
           under bindstem_ind and the recursion equations are stored
           under bindstem_def.
        4. Otherwise, an attempt is made to prove termination. If this fails, 
           then xDefine fails (and cleans up after itself).
        5. Otherwise, the termination conditions are eliminated, and
           the induction theorem is stored under bindstem_ind and
           the recursion equations are stored under bindstem_def, before
           the recursion equations are returned.
 ---------------------------------------------------------------------------*)

fun xDefine bindstem ql =
 let val defname = bindstem ^"_"^ !def_suffix
     val indname = bindstem ^"_"^ !ind_suffix
     val defn = Hol_fun bindstem (norm_quotel ql)
                 handle e => (Lib.say "Unable to define function!\n"; raise e)
 in
   if Defn.abbrev defn orelse Defn.primrec defn 
   then (Theory.set_MLname bindstem defname;
         Lib.say ("Definition stored under "^Lib.quote defname^".\n");
         Defn.eqns_of defn)
   else
   if not(null(Defn.parameters defn)) 
   then let val ind = Option.valOf (Defn.ind_of defn)
        in
          Lib.say (String.concat
           ["Schematic definition.\nEquations stored under ",
            Lib.quote defname, ".\nInduction stored under ",
            Lib.quote indname, ".\n"]);
          save_thm(indname, ind);
          save_thm(defname, Defn.eqns_of defn)
        end
   else 
    let val defn' = Halts.proveTotal defn handle HOL_ERR _ => defn
    in 
       if null(Defn.tcs_of defn')
       then let val ind = Option.valOf (Defn.ind_of defn')
            in
               Lib.say (String.concat
                ["Equations stored under ",
                 Lib.quote defname, ".\nInduction stored under ",
                 Lib.quote indname, ".\n"]);
               save_thm(indname, ind);
               save_thm(defname, Defn.eqns_of defn')
            end
       else (Lib.say (String.concat
               ["Unable to prove totality!\nUse \"Hol_fun\" to make ",
               "the definition,\nand \"Defn.tgoal <defn>\" to set up the ",
               "termination proof.\n"]);
             mapfilter delete_const (map dest_atom (constants_of defn));
             Theory.scrub();
             raise DEF_ERR "xDefine" "Unable to prove termination")
    end
 end;


(*---------------------------------------------------------------------------
    Define ` ... ` creates a bindstem for the definition to be made, 
    then calls xDefine. In the case of a single-recursive function
    with an alphanumeric name, everything is simple. If the name
    is symbolic, then the bindstem is generated from "symbol_". If 
    the definition is mutually recursive, then the name is generated
    from "mutrec" in a bizarre fashion.
 ---------------------------------------------------------------------------*)

local val mut_namesl = ref []:string list list ref
      val sort = Lib.sort (curry (op= :string*string->bool))
      fun index_of x [] i = NONE
        | index_of x (y::rst) i = if x=y then SOME i else index_of x rst (i+1)
      fun inc_mutl names =
        let val names' = sort names
        in case index_of names' (!mut_namesl) 0
            of NONE => (mut_namesl := !mut_namesl@[names']; 
                        Option.valOf(index_of names' (!mut_namesl) 0))
             | SOME i => i
        end
      val symbr = ref 0
      fun gen_symbolic_name() = 
         let val s = "symbol_"^Lib.int_to_string (!symbr)
         in Portable.inc symbr; s
         end
in
fun Define ql =
 let val qtm = norm_quotel ql
     val names = preview qtm
     val bindstem =
        case names
         of []  => raise DEF_ERR "Define" "Can't find name of function"
          | [x] => if Lexis.ok_identifier x then x
                   else let val name = gen_symbolic_name()
                        in
                          Lib.say (String.concat
                             ["Non-alphanumeric being defined.\n",
                              "Invented stem for binding(s): ", 
                              Lib.quote name,".\n"]);
                          name
                        end
          |  _  =>
             let val name = "mutrec"^Lib.int_to_string(inc_mutl names)
             in 
               Lib.say (String.concat
                  ["Mutually recursive definition.\n",
                   "Invented stem for bindings is ", 
                   Lib.quote name,".\n"]);
               name
             end
 in 
    xDefine bindstem qtm
 end               
end;


end;
