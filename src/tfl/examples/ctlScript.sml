(*---------------------------------------------------------------------------
     CTL as a concrete datatype, and valuations. From Daryl Stewart.
 ---------------------------------------------------------------------------*)
Theory ctl
Ancestors
  pred_set string


val _ = ParseExtras.temp_loose_equality()

fun mkMySuffix s prec = add_rule
    {term_name = s, fixity = Suffix prec,
     pp_elements = [HardSpace 1, TOK s],
     paren_style = OnlyIfNecessary,
     block_style = (AroundSamePrec, (PP.INCONSISTENT, 0))};

fun mkMyPrefix s prec = add_rule
    {term_name = s, fixity = Prefix prec,
     pp_elements = [TOK s, HardSpace 1],
     paren_style = OnlyIfNecessary,
     block_style = (AroundSamePrec, (PP.INCONSISTENT, 0))};

fun mkMyInfixAlias t s prec = add_rule
    {term_name = t, fixity = Infix (HOLgrammars.RIGHT, prec),
     pp_elements = [HardSpace 1, TOK s, BreakSpace(1,0)],
     paren_style = OnlyIfNecessary,
     block_style = (AroundSamePrec, (PP.INCONSISTENT, 0))};

fun mkMyInfix s prec = mkMyInfixAlias s s prec;


(*---------------------------------------------------------------------------*
 * Create the theory.                                                        *
 *---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*
 * Comments from notes from [1] Model Checking and Modular Verification      *
 * (Grumberg and Long) ACMTransactions on Programming Languages and Systems  *
 * Vol. 16, No. 3, May 1994                                                  *
 * and also [2] Model Checking (Clarke, Grumberg & Peled)                    *
 *---------------------------------------------------------------------------*)

Datatype:
     state_formula
          = TRUE
          | FALSE
          | REG 'a
          | NOT state_formula
          | SDISJ state_formula state_formula
          | SCONJ state_formula state_formula
          | E path_formula
          | A path_formula;

     path_formula
          = STATE state_formula
          | FAILS path_formula
          | PDISJ path_formula path_formula
          | PCONJ path_formula path_formula
          | X path_formula
          | FU path_formula
          | G path_formula
          | U path_formula path_formula
          | R path_formula path_formula
End

(*---------------------------------------------------------------------------
    Set-up special parsing for constructors, and inform the system
    that ~, /\, and \/ will be overloaded.
 ---------------------------------------------------------------------------*)

val _ = mkMyPrefix "REG"   950;   (* tighter than ~ *)
val _ = mkMyPrefix "E"     245;
val _ = mkMyPrefix "A"     245;
val _ = mkMyPrefix "STATE" 260;
val _ = mkMySuffix "FAILS" 250; (* tighter than ==> but weaker than \/  *)
val _ = mkMyPrefix "FU"    255;
val _ = mkMyPrefix "G"     255;
val _ = mkMyInfix  "U"     270;
val _ = mkMyInfix  "R"     270;
val _ = mkMyPrefix "X"     255;

(*---------------------------------------------------------------------------
     Things can look slightly ambiguous:

       Term `A X STATE TRUE FAILS`
         =
       Term`A ((X (STATE TRUE)) FAILS)`
 ---------------------------------------------------------------------------*)

Overload "~" = “NOT”

Overload "/\\" = “PCONJ”
Overload "/\\" = “SCONJ”

Overload "\\/" = “PDISJ”
Overload "\\/" = “SDISJ”

(*---------------------------------------------------------------------------*
 * The branching time logic CTL (Computation Tree Logic) [2:p30]
 * CTL* restricted st X, FU, G, U and R are preceded by a path quantifier
 * ie path formulae are restricted st
 * if f and g are state formulae then Xf FUf Gf fUg and fRg are path formulae
 * All CTL formulae are of type 'a state_formula
 *---------------------------------------------------------------------------*)

Definition IS_CTL_def:
       (IS_CTL (E X STATE f)                 = IS_CTL f)
  /\   (IS_CTL (E FU STATE f)                = IS_CTL f)
  /\   (IS_CTL (E G STATE f)                 = IS_CTL f)
  /\   (IS_CTL (E ((STATE f1) U (STATE f2))) = IS_CTL f1 /\ IS_CTL f2)
  /\   (IS_CTL (E ((STATE f1) R (STATE f2))) = IS_CTL f1 /\ IS_CTL f2)
  /\   (IS_CTL (A X STATE f)                 = IS_CTL f)
  /\   (IS_CTL (A FU STATE f)                = IS_CTL f)
  /\   (IS_CTL (A G STATE f)                 = IS_CTL f)
  /\   (IS_CTL (A ((STATE f1) U (STATE f2))) = IS_CTL f1 /\ IS_CTL f2)
  /\   (IS_CTL (A ((STATE f1) R (STATE f2))) = IS_CTL f1 /\ IS_CTL f2)
  /\   (IS_CTL TRUE                          = T)
  /\   (IS_CTL FALSE                         = T)
  /\   (IS_CTL (REG _)                       = T)
  /\   (IS_CTL ~f                            = IS_CTL f)
  /\   (IS_CTL (f1 \/ f2)                    = IS_CTL f1 /\ IS_CTL f2)
  /\   (IS_CTL (f1 /\ f2)                    = IS_CTL f1 /\ IS_CTL f2)
  /\   (IS_CTL (E _)                         = F)
  /\   (IS_CTL (A _)                         = F)
End

(*---------------------------------------------------------------------------*
 * Restrictions to Universally Quantified formulae (ACTL* and ACTL)
 * ACTL* is CTL* with restrictions:
 * A1) positive normal form (only negate atoms)
 * A2) no E path quantifier (only A)
 * ACTL* formulae may be of type 'a state_formula or 'a path_formula
 *---------------------------------------------------------------------------*)

Definition ACTLSTAR_FORMULA_def:
       (ACTLSTAR_STATE  TRUE      = T)
  /\   (ACTLSTAR_STATE  FALSE     = T)
  /\   (ACTLSTAR_STATE ~TRUE      = T)
  /\   (ACTLSTAR_STATE ~FALSE     = T)
  /\   (ACTLSTAR_STATE (REG _)    = T)
  /\   (ACTLSTAR_STATE (~REG _)   = T)
  /\   (ACTLSTAR_STATE ~(_)       = F)
  /\   (ACTLSTAR_STATE (f1 \/ f2) = ACTLSTAR_STATE f1 /\ ACTLSTAR_STATE f2)
  /\   (ACTLSTAR_STATE (f1 /\ f2) = ACTLSTAR_STATE f1 /\ ACTLSTAR_STATE f2)
  /\   (ACTLSTAR_STATE (E _)      = F)
  /\   (ACTLSTAR_STATE (A g)      = ACTLSTAR_PATH g)
  /\   (ACTLSTAR_PATH  (STATE f)  = ACTLSTAR_STATE f)
  /\   (ACTLSTAR_PATH  (_ FAILS)  = F)
  /\   (ACTLSTAR_PATH  (g1 \/ g2) = ACTLSTAR_PATH g1 /\ ACTLSTAR_PATH g2)
  /\   (ACTLSTAR_PATH  (g1 /\ g2) = ACTLSTAR_PATH g1 /\ ACTLSTAR_PATH g2)
  /\   (ACTLSTAR_PATH  (X g)      = ACTLSTAR_PATH g)
  /\   (ACTLSTAR_PATH  (FU g)     = ACTLSTAR_PATH g)
  /\   (ACTLSTAR_PATH  (G g)      = ACTLSTAR_PATH g)
  /\   (ACTLSTAR_PATH  (g1 U g2)  = ACTLSTAR_PATH g1 /\ ACTLSTAR_PATH g2)
  /\   (ACTLSTAR_PATH  (g1 R g2)  = ACTLSTAR_PATH g1 /\ ACTLSTAR_PATH g2)
End

(*---------------------------------------------------------------------------*
 * ACTL is CTL with restrictions A1 and A2
 * ACTL formulae ore of type 'a state_formula
 *---------------------------------------------------------------------------*)

Definition IS_ACTL_def:   IS_ACTL f = ACTLSTAR_STATE f /\ IS_CTL f
End


(*---------------------------------------------------------------------------*
 * Definition 2: of a structure M
 *
 * M = <S   a finite set of states
 *      S0  the start states, a subset of S
 *      A   finite set of atomic propositions
 *      L   function from states to sets of
 *          atomic propositions true in that state
 *      R   transition relation, a subset of SxS
 *      F   Streett acceptance condition, a subset of powerset(SxS)
 *     >
 *---------------------------------------------------------------------------*)

Datatype:
   STRUCTURE = <| states      : 'state -> bool;
                  states0     : 'state -> bool;
                  atoms       : 'varatom  -> bool;
                  valids      : 'state -> 'varatom -> bool;
                  transitions : 'state # 'state -> bool;
                  fairSets    : ('state -> bool) # ('state -> bool) -> bool
                |>
End


Definition wfSTRUCTURE_def:
 wfSTRUCTURE (M: ('state,'atom) STRUCTURE)
 = (M.states0 SUBSET M.states) /\
   (!P Q. (P,Q) IN M.fairSets ==> P SUBSET M.states /\ Q SUBSET M.states) /\
   (!s. s IN M.states ==> (M.valids s) SUBSET M.atoms)
End

(*---------------------------------------------------------------------------*
 * Definition 3: of paths PI:
 *
 * PI is infinite sequence of states s0,s1,s2... s.t. !i. R(si, si+1)
 *---------------------------------------------------------------------------*)

Datatype: Path = PATH (num -> 'state)
End

val _ = mkMyInfix "STATE_NO" 140;
val _ = mkMyInfix "IS_PATH_IN" 140;
val _ = mkMyInfix "IS_FAIR_PATH_IN" 140;
val _ = mkMyInfix "FROM" 140;

Definition STATE_NO_def:   PATH(Sn) STATE_NO n = Sn n
End

Definition IS_PATH_IN_def:
     (PI:'state Path) IS_PATH_IN  (M:('state,'atom)STRUCTURE)
       = (PI STATE_NO 0) IN M.states /\
         !n. ((PI STATE_NO n), (PI STATE_NO (n+1))) IN M.transitions
End


(*---------------------------------------------------------------------------*
 * Definition 4: of inf(PI):
 *
 * inf(PI) = {s | s=si for infinitely many i}
 *
 * and of fair Paths
 *
 * Mfair(PI) iff !(P,Q) in F. inf(PI) * P <> {} -> inf(PI) * Q <> {}
 * where * is set intersection
 *---------------------------------------------------------------------------*)

Definition INF_def:   INF PI = {s | !m. ?n. n > m /\ (PI STATE_NO m = s)}
End

Definition IS_FAIR_PATH_IN_def:
     (PI:'state Path) IS_FAIR_PATH_IN  (M:('state,'atom)STRUCTURE)
      = (PI IS_PATH_IN M) /\
        !P Q. (P,Q) IN M.fairSets
              ==> ~(((INF PI) INTER P) = {})
              ==> ~(((INF PI) INTER Q) = {})
End

(*---------------------------------------------------------------------------*
 * PISn denotes sn in PI
 * PIn denotes the Path sn,sn+1,sn+2...
 *---------------------------------------------------------------------------*)

Definition FROM_def:   PI FROM n = PATH(\x. PI STATE_NO (n+x))
End


(*---------------------------------------------------------------------------*)
(* Definition 5: Satisfaction of formulae.                                   *)
(*---------------------------------------------------------------------------*)

Definition SAT_def:
    (STATESAT ((M:('s,'a)STRUCTURE), s:'s) (TRUE:'a state_formula) = T)
 /\ (STATESAT (M,s) FALSE      = F)
 /\ (STATESAT (M,s) (REG a)    = ?PI. (PI STATE_NO 0 = s) /\
                                      (PI IS_FAIR_PATH_IN M) /\
                                      (a IN (M.valids s)))
 /\ (STATESAT (M,s)  ~f        = ~STATESAT (M,s) f)
 /\ (STATESAT (M,s) (f1 \/ f2) = STATESAT (M,s) f1 \/ STATESAT (M,s) f2)
 /\ (STATESAT (M,s) (f1 /\ f2) = STATESAT (M,s) f1 /\ STATESAT (M,s) f2)
 /\ (STATESAT (M,s) (E g1)     = ?PI. (PI IS_FAIR_PATH_IN M) /\
                                      (PI STATE_NO 0 = s) /\ PATHSAT(M,PI) g1)
 /\ (STATESAT (M,s) (A g1)     = !PI. (PI IS_FAIR_PATH_IN M) /\
                                      (PI STATE_NO 0 = s) ==> PATHSAT(M,PI) g1)

 /\ (PATHSAT (M,PI) (STATE f1) = STATESAT (M, PI STATE_NO 0) f1)
 /\ (PATHSAT (M,PI) (g1 FAILS) = ~PATHSAT (M,PI) g1)
 /\ (PATHSAT (M,PI) (g1 \/ g2) = PATHSAT (M,PI) g1 \/ PATHSAT (M,PI) g2)
 /\ (PATHSAT (M,PI) (g1 /\ g2) = PATHSAT (M,PI) g1 /\ PATHSAT (M,PI) g2)
 /\ (PATHSAT (M,PI) (X g1)     = PATHSAT (M, PI FROM 1) g1)
 /\ (PATHSAT (M,PI) (FU g1)    = ?k. k >= 0 /\ PATHSAT (M,(PI FROM k)) g1)
 /\ (PATHSAT (M,PI) (G g1)     = !i. i>=0 ==> PATHSAT (M,PI FROM i) g1)
 /\ (PATHSAT (M,PI) (g1 U g2)  = ?k. k>=0 /\ PATHSAT (M,PI FROM k) g2 /\
                                     !j. 0<=j/\j<k ==> PATHSAT(M,PI FROM j) g1)
 /\ (PATHSAT (M,PI) (g1 R g2)  = !j. j>=0
                                     ==> (!i. i<j ==> ~PATHSAT(M,PI FROM i) g1)
                                     ==> PATHSAT(M,PI FROM j) g2)
Termination
(*---------------------------------------------------------------------------
       Trivial termination proof ... the built-in termination
       prover should really get this.
 ---------------------------------------------------------------------------*)
  WF_REL_TAC `measure (\s. case s of
                               INL (x,y) => state_formula_size (\v.0) y
                             | INR (x,y) => path_formula_size (\v.0) y)`
End
