signature rlEnv =
sig

  include Abbrev

  (* 'a is the type of board
     ''b is the type for move
     'c is the type of targets *)

  val ntarget_glob : int ref
  val ngen_glob : int ref
  val exwindow_glob : int ref
  val bigsteps_glob : int ref
  val nsim_glob : int ref
  val decay_glob : real ref
  val noise_flag : bool ref
  val maxsize_glob : int ref

  type ('a,''b,'c) gamespec =
    {
    movel : ''b list,
    string_of_move : ''b -> string,
    filter_sit : 'a psMCTS.sit -> ((''b * real) list -> (''b * real) list),
    status_of : ('a psMCTS.sit -> psMCTS.status),
    apply_move : (''b -> 'a psMCTS.sit -> 'a psMCTS.sit),
    operl : (term * int) list,
    dim : int,
    nntm_of_sit: 'a psMCTS.sit -> term
    }

  val logfile_glob : string ref
  val summary : string -> unit

  val start_rl_loop : 
    (rlGameArithGround.board, ''a, 'b) gamespec ->
      rlGameArithGround.board psMCTS.sit list ->
        (term * real list) list * (term * real list) list


end
