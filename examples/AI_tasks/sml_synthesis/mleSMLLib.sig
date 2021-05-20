signature mleSMLLib =
sig

  include Abbrev

  exception Unbuildable

  (* types *)
  type tnn = mlTreeNeuralNetwork.tnn
  type emb = real vector
  type instr = string * int * (int list -> int)

  datatype move =
      BIns of instr
    | BTest
    | BRec
    | BProj of int
    | BStartSub of int
    | BEndSub

  datatype prog =
      Ins of instr * prog list
    | Test of prog * prog * prog
    | Rec of prog list
    | Proj of int
    | Sub of prog * prog list
  datatype progl =
    NilPL of emb | ConsPL of (emb * (emb * prog) * progl) 
  datatype progll = 
    NilPLL of emb | ConsPLL of (emb * (emb * (int * progl)) * progll)
  type board = int * (emb * int list) * progll
  type bareboard = int * int list * (int * prog list) list

  (* global parameters *)
  val maxvar : int
  val instrl : instr list
  val instrd : (string,instr) Redblackmap.dict
  
  (* tree neural network *)
  val operl : term list
  val ol_cat : term
  val getemb_progll : progll -> emb
  val fp_emb : tnn -> term -> emb list -> emb
  val infer_emb : tnn -> term -> emb
  val term_of_board : board -> term
  
  (* execute and build programs *)
  val exec : int -> prog -> int list -> int option
  val build_progll : tnn -> move -> progll -> progll
  val avail_board : move -> board -> bool  

  (* conversion between the two types of board *)
  val dropemb_board: board -> bareboard
  val emptyemb_board : bareboard -> board
  val updemb_board : tnn -> board -> board


end
