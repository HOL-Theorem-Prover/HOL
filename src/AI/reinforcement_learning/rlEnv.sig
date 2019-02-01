signature rlEnv =
sig

  include Abbrev

  (*
   'a is the type of board
   'b is the type for move
   'c is the type of targets
  *)

  val logfile_glob : string ref

  type ('a,'b,'c) gamespec =
    {
    mk_startsit: 'c -> 'a psMCTS.sit,
    movel: 'b list,
    status_of : ('a psMCTS.sit -> psMCTS.status),
    apply_move : ('b -> 'a psMCTS.sit -> 'a psMCTS.sit),
    operl : (term * int) list,
    dim : int,
    nntm_of_sit: 'a psMCTS.sit -> term
    }

  val start_rl_loop : ('a, 'b, 'c) gamespec ->
    ('a psMCTS.sit list * int) -> int ->
    (term * real list) list * (term * real list) list

end
