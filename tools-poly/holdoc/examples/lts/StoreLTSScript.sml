(* An LTS for a simple integer store *)

(*[ RCSID "$Id: StoreLTSScript.sml 3286 2003-06-10 18:09:44Z kw217 $" ]*)

open HolKernel boolLib Parse
infix THEN THENC |-> ##

open bossLib containerTheory finite_mapTheory

open HolDoc

local open TypeTheory ValueTheory LabelTheory in end;

val Term = Parse.Term;

val _ = new_theory "StoreLTS";

(* -------------------------------------------------- *)
(*                Rule prep                           *)
(* -------------------------------------------------- *)

val _ = add_rule { block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0)),
                   paren_style = OnlyIfNecessary,
                   fixity = Infix(NONASSOC, 420),
                   pp_elements = [HardSpace 1, TOK "/*", HardSpace 1,
                                  TM (* cat *), HardSpace 1,
                                  TOK "*/", BreakSpace(1,0),
                                  TM, (* store *)
                                  BreakSpace(1,2), TOK "--", HardSpace 1,
                                  TM, (* label *)
                                  HardSpace 1, TOK "-->", BreakSpace(1,0)],
                   term_name = "host_redn0"
                   };

val _ = add_rule { block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0)),
                   paren_style = OnlyIfNecessary,
                   fixity = Infix(NONASSOC, 420),
                   pp_elements = [HardSpace 1, TOK "/*", HardSpace 1,
                                  TM (* cat *), HardSpace 1,
                                  TOK "*/", BreakSpace(1,0),
                                  TM, (* store *)
                                  BreakSpace(1,2), TOK "--", HardSpace 1,
                                  TM, (* label *)
                                  HardSpace 1, TOK "--=>", BreakSpace(1,0)],
                   term_name = "host_redn"
                   };

val _ = add_rule { block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0)),
                   paren_style = OnlyIfNecessary,
                   fixity = Infixl 199,
                   pp_elements = [BreakSpace(1,~2), TOK "<==", HardSpace 1],
                   term_name = "revimp" };

val revimp_def = xDefine "revimp" `(q <== p) = (p ==> q)`;

val _ = Hol_datatype`
  rulecat = ret
          | call
`;


val _ = Define `
    (* initial state *)
    empty_store = (NONE, FEMPTY)
`;

(* transition rules *)

open Net_Hol_reln;
val (rules, ind, cases) =
  Net_Hol_reln`

   (!v s.

    return_1 /* ret (* return result to caller *) */
      (SOME v,s)
   -- return v -->
      (NONE,s)

   <==

      T


   (*:

   Return result [[v]] of earlier call to caller.  State [[s]] remains
   the same.

   :*)
   )

/\

   (!v s loc.

    new_1 /* call (* create a new cell *) */
      (NONE,s)
    -- new v -->
      (SOME (VLoc loc), s |+ (loc,v))

    <==

      loc NOTIN FDOM s


    (*:

    Create a new cell containing [[v]], and return it to the caller.
    $$\rho' = \rho[\mathit{loc}\mapsto v],\quad
    \mathit{loc}\notin\textbf{dom}(\rho)$$

    :*)
    )

/\

   (!loc s v.

    get_1 /* call (* create a new cell *) */
      (NONE,s)
    -- get loc -->
      (SOME (VNum v),s)

    <==

      (loc IN FDOM s) /\  (* cell must exist *)
      (v = s ' loc) (*: $\rho[\mathit{loc}]$ :*)


    (*:

    Return the value in cell [[loc]], if present.
    $$v = \rho[\mathit{loc}]$$

    :*)
    )

/\

   (!loc v s v0.

    set_1 /* call (* set the value in a cell *) */
      (NONE,s |+ (loc,v0))
    -- set (loc,v) -->
      (SOME (VUnit ()), s |+ (loc,v))

    <==

      T


    (*:

    Update the value in the given cell.
    $$\rho' = \rho[\mathit{loc}\mapsto v],\quad
    \mathit{loc}\in\textbf{dom}(\rho)$$

    :*)
    )

` handle e => Raise e;

val _ = export_theory();

