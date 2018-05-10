signature monadsyntax =
sig


  include Abbrev
  (* loading this module installs this function as an absyn transformer
     under the name "monadsyntax.transform_absyn"
  *)
  val transform_absyn : term_grammar.absyn_postprocessor
  val print_monads : term_grammar.userprinter

  val add_monadsyntax : unit -> unit
  val temp_add_monadsyntax : unit -> unit

  val disable_monadsyntax : unit -> unit
  val temp_disable_monadsyntax : unit -> unit

  type monadinfo =
       { bind : term,
         ignorebind : term option,
         unit : term,
         fail : term option,
         choice : term option,
         guard : term option }
  val declare_monad : string * monadinfo -> unit
  val all_monads : unit -> (string * monadinfo) list

  val enable_monad : string -> unit
  val temp_enable_monad : string -> unit

  val weak_enable_monad : string -> unit
  val temp_weak_enable_monad : string -> unit

  val disable_monad : string -> unit
  val temp_disable_monad : string -> unit


end
