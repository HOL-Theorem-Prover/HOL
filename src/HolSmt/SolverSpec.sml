(* Copyright (c) 2009 Tjark Weber. All rights reserved. *)

(* Specification of SMT solvers: name, command, etc. *)

structure SolverSpec :> SolverSpec = struct

  type T = {
    name           : string,
    command        : string,
    translation_fn : Term.term -> string list,
    infile         : string,
    outfiles       : string list,
    is_sat_fn      : unit -> bool,
    model_fn       : (unit -> string) option,
    proof_fn       : (unit -> string) option
  }

  (* getters *)

  fun get_name (solver : T)           = #name solver

  fun get_command (solver : T)        = #command solver

  fun get_translation_fn (solver : T) = #translation_fn solver

  fun get_infile (solver : T)         = #infile solver

  fun get_outfiles (solver : T)       = #outfiles solver

  fun get_is_sat_fn (solver : T)      = #is_sat_fn solver

  fun get_model_fn (solver : T)       = #model_fn solver

  fun get_proof_fn (solver : T)       = #proof_fn solver

  (* setters *)

  fun set_name (s : T) n =
    {name = n, command = #command s, translation_fn = #translation_fn s,
      infile = #infile s, outfiles = #outfiles s, is_sat_fn = #is_sat_fn s,
      model_fn = #model_fn s, proof_fn = #proof_fn s}

  fun set_command (s : T) c =
    {name = #name s, command = c, translation_fn = #translation_fn s,
      infile = #infile s, outfiles = #outfiles s, is_sat_fn = #is_sat_fn s,
      model_fn = #model_fn s, proof_fn = #proof_fn s}

  fun set_translation_fn (s : T) t =
    {name = #name s, command = #command s, translation_fn = t,
      infile = #infile s, outfiles = #outfiles s, is_sat_fn = #is_sat_fn s,
      model_fn = #model_fn s, proof_fn = #proof_fn s}

  fun set_infile (s : T) i =
    {name = #name s, command = #command s, translation_fn = #translation_fn s,
      infile = i, outfiles = #outfiles s, is_sat_fn = #is_sat_fn s,
      model_fn = #model_fn s, proof_fn = #proof_fn s}

  fun set_outfiles (s : T) out =
    {name = #name s, command = #command s, translation_fn = #translation_fn s,
      infile = #infile s, outfiles = out, is_sat_fn = #is_sat_fn s,
      model_fn = #model_fn s, proof_fn = #proof_fn s}

  fun set_is_sat_fn (s : T) sat =
    {name = #name s, command = #command s, translation_fn = #translation_fn s,
      infile = #infile s, outfiles = #outfiles s, is_sat_fn = sat,
      model_fn = #model_fn s, proof_fn = #proof_fn s}

  fun set_model_fn (s : T) m =
    {name = #name s, command = #command s, translation_fn = #translation_fn s,
      infile = #infile s, outfiles = #outfiles s, is_sat_fn = #is_sat_fn s,
      model_fn = m, proof_fn = #proof_fn s}

  fun set_proof_fn (s : T) p =
    {name = #name s, command = #command s, translation_fn = #translation_fn s,
      infile = #infile s, outfiles = #outfiles s, is_sat_fn = #is_sat_fn s,
      model_fn = #model_fn s, proof_fn = p}


  fun make_solver (n, c, t, i, out, sat, m, p) =
    {name = n, command = c, translation_fn = t, infile = i, outfiles = out,
      is_sat_fn = sat, model_fn = m, proof_fn = p}

  fun dest_solver (s : T) =
    (#name s, #command s, #translation_fn s, #infile s, #outfiles s,
      #is_sat_fn s, #model_fn s, #proof_fn s)

end
