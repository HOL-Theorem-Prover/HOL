signature rlRules =
sig

  include Abbrev

  datatype axiom = Refl | Inst of term

  val match_axiom : term -> axiom list

  datatype proofstep =
    Sym of term |
    NegSym of term |
    Ap of term |
    Inj of term |
    Sub of ((int list * term) * term)

  val dest_stepsub : proofstep -> ((int list * term) * term)

  val ap_tac : term -> term
  val negsym_tac : term -> term
  val sym_tac : term -> term
  val inj_tac : term -> term

  (* board *)
  datatype board =
    TacBoard of term |
    StopBoard of (term * int list) |
    LrBoard of (term * int list) |
    ImitBoard of ((term * int list) * term) |
    ConjunctBoard of (term * term)

  type situation = bool * board

  val nntm_of_sit : situation -> term

  (* moves *)
  datatype tacchoice = SymTac | NegSymTac | ApTac | InjTac | SubTac
  val all_tacchoice : tacchoice list
  val move_tac : tacchoice -> situation -> situation

  datatype stopchoice = Stop | Continue
  val move_stop : stopchoice -> situation -> situation
  val all_stopchoice : stopchoice list
  val active_var : term

  datatype lrchoice = Left | Right
  val all_lrchoice : lrchoice list
  val move_lr : lrchoice -> situation -> situation

  datatype imitchoice = ImitZero | ImitSuc | ImitAdd
  val all_imitchoice : imitchoice list
  val apply_imit : imitchoice -> term -> term
  val move_imit : imitchoice -> situation -> situation

  datatype conjunctchoice = ConjunctLeft | ConjunctRight
  val all_conjunctchoice : conjunctchoice list
  val move_conjunct : conjunctchoice -> situation -> situation

  (* all moves *)
  datatype move =
    TacMove of tacchoice |
    StopMove of stopchoice |
    LrMove of lrchoice |
    ImitMove of imitchoice |
    ConjunctMove of conjunctchoice
  val apply_move : move -> situation -> situation
  val string_of_move : move -> string

end
