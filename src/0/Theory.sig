signature Theory = 
sig

type hol_type = Type.hol_type
type term = Term.term;
type thm = Thm.thm;
type fixity = Term.fixity
type ppstream = Portable_PrettyPrint.ppstream
type thy_addon = {sig_ps    : (ppstream -> unit) option,
                  struct_ps : (ppstream -> unit) option}

datatype ('a,'b) result = SUCCESS of 'a
                        | FAILURE of 'b

datatype 'a failed = SYSTEM   of exn     (* OS/network not right *)
                   | INTERNAL of exn     (* my mistake *)
                   | CLIENT   of 'a      (* caller fixable problem *)


(* Adding to the current theory *)

  val new_type     : {Name:string, Arity:int} -> unit
  val new_constant : {Name:string, Ty:hol_type} -> unit
  val new_infix    : {Name:string, Ty:hol_type, Prec:int} -> unit
  val new_binder   : {Name:string, Ty:hol_type} -> unit
  val new_axiom    : string * term -> thm
  val save_thm     : string * thm -> thm

(* Information on constants *)

  val is_type     : string -> bool
  val is_constant : string -> bool
  val is_binder   : string -> bool
  val is_infix    : string -> bool
  val arity       : string -> int
  val fixity      : string -> fixity
  val precedence  : string -> int

(* Delete from the current theory *)

  val delete_type    : string -> unit
  val delete_const   : string -> unit
  val delete_axiom   : string -> unit
  val delete_theorem : string -> unit

(* Information on the current theory *)

  val current_theory : unit -> string
  val parents        : string -> string list
  val ancestry       : string -> string list
  val types          : string -> {Name :string, Arity :int} list
  val constants      : string -> term list
  val infixes        : string -> term list
  val binders        : string -> term list
  val axioms         : unit -> (string * thm) list
  val definitions    : unit -> (string * thm) list
  val theorems       : unit -> (string * thm) list
  val axiom          : string -> thm
  val definition     : string -> thm
  val theorem        : string -> thm

(* Viewing the current theory *)

  val print_theory              : unit -> unit
  val print_theory_to_file      : string -> unit
  val print_theory_to_outstream : Portable.outstream -> Portable.outstream

(* Operations that change the current theory *)

  datatype clientfixable = BADNAMES of string list
                         | EXN of exn

  val prim_new_theory : string -> (unit,clientfixable failed) result
  val new_theory : string -> unit

(* Operations for making theory persistent (write it to disk) *)

  val adjoin_to_theory : thy_addon -> unit

  val prim_export_theory : unit -> (unit, string list failed) result
  val export_theory : unit -> unit
 

(* Support operations for theories-as-structures *)

  val link_parents       : string*int*int -> (string*int*int)list -> unit
  val incorporate_types  : string -> (string*int) list -> unit
  val incorporate_consts : string -> (string*hol_type*fixity)list -> unit

 val uptodate_type  : hol_type -> bool
 val uptodate_term  : term -> bool
 val uptodate_thm   : thm -> bool
 val scrub          : unit -> unit

 (* Altering parse status of constants *)
 val set_fixity : string -> Term.fixity -> unit

 (* Changing internal bindings of ML-level names to theory objects *)
 val set_MLname : string -> string -> unit

 (* Information hiding *)

  val expose_store_definition 
   :(string * (string,string list)Lib.sum * thm * term -> thm)ref
    -> unit

end;
