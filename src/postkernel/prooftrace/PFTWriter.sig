signature PFTWriter = sig

  type pft_out

  (* Open a PFT output stream. binary=true for binary format, false for text. *)
  val openOut : {file: string, binary: bool} -> pft_out
  val closeOut : pft_out -> unit

  (* Header *)
  val header : pft_out -> {version: int, ruleset: string,
                           n_ty: int, n_tm: int, n_th: int, n_ci: int} -> unit

  (* Type commands *)
  val tyvar : pft_out -> int -> string -> unit
  val tyop  : pft_out -> int -> string -> int list -> unit

  (* Term commands *)
  val var   : pft_out -> int -> string -> int -> unit
  val const : pft_out -> int -> string -> int -> unit
  val comb  : pft_out -> int -> int -> int -> unit
  val abs   : pft_out -> int -> int -> int -> unit

  (* Basic theorem commands *)
  val refl      : pft_out -> int -> int -> unit
  val alpha     : pft_out -> int -> int -> int -> unit
  val assume    : pft_out -> int -> int -> unit
  val beta_conv : pft_out -> int -> int -> unit
  val eq_mp     : pft_out -> int -> int -> int -> unit
  val mp        : pft_out -> int -> int -> int -> unit
  val sym       : pft_out -> int -> int -> unit
  val trans     : pft_out -> int -> int -> int -> unit
  val conj      : pft_out -> int -> int -> int -> unit
  val conjunct1 : pft_out -> int -> int -> unit
  val conjunct2 : pft_out -> int -> int -> unit
  val disch     : pft_out -> int -> int -> int -> unit
  val disj1     : pft_out -> int -> int -> int -> unit
  val disj2     : pft_out -> int -> int -> int -> unit
  val disj_cases: pft_out -> int -> int -> int -> int -> unit
  val not_elim  : pft_out -> int -> int -> unit
  val not_intro : pft_out -> int -> int -> unit
  val ccontr    : pft_out -> int -> int -> int -> unit
  val exists    : pft_out -> int -> int -> int -> int -> unit
  val choose    : pft_out -> int -> int -> int -> int -> unit
  val gen       : pft_out -> int -> int -> int -> unit
  val spec      : pft_out -> int -> int -> int -> unit
  val specialize: pft_out -> int -> int -> int -> unit
  val genl      : pft_out -> int -> int -> int list -> unit
  val absl      : pft_out -> int -> int -> int list -> unit
  val gen_abs   : pft_out -> int -> int -> int -> int list -> unit

  (* Congruence and substitution *)
  val abs_thm       : pft_out -> int -> int -> int -> unit
  val ap_term       : pft_out -> int -> int -> int -> unit
  val ap_thm        : pft_out -> int -> int -> int -> unit
  val mk_comb       : pft_out -> int -> int -> int -> unit
  val beta_thm      : pft_out -> int -> int -> unit
  val mk_abs_thm    : pft_out -> int -> int -> int -> unit
  val mk_comb_thm   : pft_out -> int -> int -> int -> int -> unit
  val eq_imp_rule1  : pft_out -> int -> int -> unit
  val eq_imp_rule2  : pft_out -> int -> int -> unit
  val inst          : pft_out -> int -> int -> (int * int) list -> unit
  val inst_type     : pft_out -> int -> int -> (int * int) list -> unit
  val subst         : pft_out -> int -> int -> int -> (int * int) list -> unit
  val deductAntisym : pft_out -> int -> int -> int -> unit

  (* Axioms and definitions *)
  val axiom    : pft_out -> int -> int -> string option -> unit
  val def_spec : pft_out -> int -> int -> string list -> unit
  val def_tyop : pft_out -> int -> int -> string -> unit

  (* Computation *)
  val compute      : pft_out -> int -> int -> int -> int list -> unit
  val compute_init : pft_out -> int -> int -> int
                     -> (string * int) list -> (string * int) list -> unit

  (* Deletion *)
  val del       : pft_out -> string -> int -> unit
  val del_range : pft_out -> string -> int -> int -> unit

  (* Save/Load *)
  val save : pft_out -> string -> int -> unit
  val load : pft_out -> int -> string -> unit

  (* Comment (text only; ignored in binary) *)
  val comment : pft_out -> string -> unit

end
