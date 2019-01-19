signature rlEnv =
sig

  include Abbrev

  (*
   'a is the type of board
   ''b is the type for situation_class
   'c is the type of targets (term usually)
   'd is the type of move
  *)
  type ('a,''b,'c,'d) sittools =
    {
    class_of_sit: 'a psMCTS.sit -> ''b,
    mk_startsit: 'c -> 'a psMCTS.sit,
    movel_in_sit: ''b -> 'd list,
    nntm_of_sit: 'a psMCTS.sit -> term,
    sitclassl: ''b list
    }

  val start_rl_loop : int ->
    ('a,''b,'c,'d) sittools ->
    ((term * int) list * int) ->
    ('a psMCTS.sit -> psMCTS.status) * ('d -> 'a psMCTS.sit -> 'a psMCTS.sit) ->
    ('c list * 'c list) ->
    ('c list -> ('c list * 'c list) -> ('c list * 'c list)) ->
      ('c list * 'c list) *
      (''b * ((term * real) list * (term * real list) list)) list

end
