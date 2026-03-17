signature PFTReader = sig

  (* Format-level handler: commands common to all rulesets *)
  type format_handler = {
    (* Type commands *)
    tyvar     : int * string -> unit,
    tyop      : int * string * int list -> unit,
    (* Term commands *)
    var       : int * string * int -> unit,
    const     : int * string * int -> unit,
    comb      : int * int * int -> unit,
    abs       : int * int * int -> unit,
    (* Kernel commands *)
    new_const : string * int -> unit,
    new_type  : string * int -> unit,
    axiom     : int * int * string option -> unit,
    (* Control commands *)
    save      : string * int -> unit,
    load      : int * string -> unit,
    del       : string * int -> unit,
    del_range : string * int * int -> unit
  }

  (* Ruleset-specific command dispatcher: called with (opcode, reader).
     The reader functions allow the dispatcher to consume arguments
     from the stream. *)
  type stream_reader = {
    readVarint : unit -> int,
    readString : unit -> string,
    readVarintList : unit -> int list,
    readVarintPairs : unit -> (int * int) list,
    readStringVarintPairs : unit -> (string * int) list,
    readStringList : unit -> string list
  }

  type ruleset_handler = int -> stream_reader -> unit

  (* Read a PFT file, calling handler functions for each command.
     Format-level commands are dispatched via format_handler.
     Ruleset-specific opcodes (0x10-0x4F) are dispatched via
     ruleset_handler.
     Returns the header info and footer (peak namespace counts). *)
  val read : {file: string, binary: bool,
              format_handler: format_handler,
              ruleset_handler: ruleset_handler}
             -> {version: int, ruleset: string,
                 n_ty: int, n_tm: int, n_th: int, n_ci: int}

  (* Read just the limits (peak namespace counts) from a PFT file
     without processing commands. Useful for pre-allocating arrays
     before a full read. Seeks to end of file to find the footer. *)
  val read_limits : {file: string, binary: bool}
                    -> {n_ty: int, n_tm: int, n_th: int, n_ci: int}

  (* Construct a ruleset_handler for the HOL4 ruleset *)
  structure HOL4 : sig
    type handler = {
      refl          : int * int -> unit,
      alpha         : int * int * int -> unit,
      beta_conv     : int * int -> unit,
      sym           : int * int -> unit,
      trans         : int * int * int -> unit,
      eq_mp         : int * int * int -> unit,
      mk_comb       : int * int * int -> unit,
      abs_thm       : int * int * int -> unit,
      ap_term       : int * int * int -> unit,
      ap_thm        : int * int * int -> unit,
      beta_thm      : int * int -> unit,
      mk_comb_thm   : int * int * int * int -> unit,
      mk_abs_thm    : int * int * int -> unit,
      assume        : int * int -> unit,
      mp            : int * int * int -> unit,
      disch         : int * int * int -> unit,
      not_intro     : int * int -> unit,
      not_elim      : int * int -> unit,
      ccontr        : int * int * int -> unit,
      deductAntisym : int * int * int -> unit,
      conj          : int * int * int -> unit,
      conjunct1     : int * int -> unit,
      conjunct2     : int * int -> unit,
      disj1         : int * int * int -> unit,
      disj2         : int * int * int -> unit,
      disj_cases    : int * int * int * int -> unit,
      gen           : int * int * int -> unit,
      spec          : int * int * int -> unit,
      specialize    : int * int * int -> unit,
      genl          : int * int * int list -> unit,
      exists        : int * int * int * int -> unit,
      choose        : int * int * int * int -> unit,
      absl          : int * int * int list -> unit,
      gen_abs       : int * int * int * int list -> unit,
      inst          : int * int * (int * int) list -> unit,
      inst_type     : int * int * (int * int) list -> unit,
      subst         : int * int * int * (int * int) list -> unit,
      eq_imp_rule1  : int * int -> unit,
      eq_imp_rule2  : int * int -> unit,
      def_tyop      : int * int * string -> unit,
      def_spec      : int * int * string list -> unit,
      def_spec_gen  : int * int * string list -> unit,
      compute_init  : int * int * int
                      * (string * int) list * (string * int) list -> unit,
      compute       : int * int * int * int list -> unit
    }

    val make_handler : handler -> ruleset_handler
  end

end
