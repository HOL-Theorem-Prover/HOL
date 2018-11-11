signature tttRobberType =
sig
  
  include Abbrev
  
  (* proof steps *)
  datatype axiom = Refl | Inst of term

  datatype proofstep =
    Sym of term |
    NegSym of term | 
    Ap of term |  
    Inj of term |
    Sub of ((int list * term) * term) |

  (* policy *)
  datatype tacchoice = SymTac | NegSymTac | ApTac | InjTac | SubTac
  datatype imitchoice = ImitZero | ImitSuc | ImitAdd
  datatype stopchoice = Stop | Continue 
  datatype lrchoice = Left | Right
  datatype alternchoice = First | Second | NegFirst | NegSecond

  (* state of the proof *)
  datatype board = 
    AlternChoice of (term * term) | 
    TacChoice of term |
    StopChoice of (term * int list) |
    LrChoice of (term * int list) |
    ResChoice of ((term * int list) * term)


  val negate   : term -> term
  val is_subtm : term -> term -> bool

  val mk_suc : term -> term
  val mk_add : term * term -> term 
  val zero : term
 
  val dest_suc : term -> term
  val dest_add : term -> term

(* -------------------------------------------------------------------------
   Position tools
   ------------------------------------------------------------------------- *)

fun sub_at_pos tm (pos,res) =
  if null pos then res else
  let 
    val (oper,argl) = strip_comb tm
    fun f i x = 
      if i = hd pos then sub_at_pos x (tl pos,res) else x
    val newargl = mapi f argl
  in
    list_mk_comb (oper,newargl)
  end   

fun subtm_at_pos pos tm =
  if null pos then tm else
  let val (oper,argl) = strip_comb tm in
    subtm_at_pos (tl pos) (List.nth (argl,hd pos))
  end 

fun recover_cut tm (pos,res) =
  let val red = subtm_at_pos pos tm in mk_eq (red,res) end

(* -------------------------------------------------------------------------
   Tactic tools
   ------------------------------------------------------------------------- *)

fun ap_tac tm = (snd o only_hd o fst o AP_TERM_TAC) ([],tm); 

fun negsym_tac tm =
  let val (a,b) = dest_eq (dest_neg tm) in
    mk_neg (mk_eq (b,a))
  end

fun sym_tac tm = 
  let val (a,b) = dest_eq tm in mk_eq (b,a) end

fun inj_tac tm = 
  let
    val (a,b) = dest_eq (dest_neg tm)
    val (a',b') = (dest_suc a, dest_suc b)
  in
    mk_neg (mk_eq (a',b'))
  end






end
