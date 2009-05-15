signature TuringML = 
sig
  type num = numML.num
  datatype dir = L | R
  datatype
  ('alpha
  ,'state
  )TM = TM of ('state -> bool) * ('alpha -> bool) * ('alpha -> bool) *
              'state * ('state -> 'alpha -> 'state * ('alpha * dir)) *
              'state * 'state * 'alpha * 'alpha
  val TM_states : ('alpha, 'state) TM -> 'state -> bool
  val TM_inputsymbs : ('alpha, 'state) TM -> 'alpha -> bool
  val TM_tapesymbs : ('alpha, 'state) TM -> 'alpha -> bool
  val TM_init : ('alpha, 'state) TM -> 'state
  val TM_trans
     : ('alpha, 'state) TM ->
       'state -> 'alpha -> 'state * ('alpha * dir)
  val TM_accept : ('alpha, 'state) TM -> 'state
  val TM_reject : ('alpha, 'state) TM -> 'state
  val TM_blank : ('alpha, 'state) TM -> 'alpha
  val TM_star : ('alpha, 'state) TM -> 'alpha
  val TM_states_fupd
     : (('state -> bool) -> 'state -> bool) ->
       ('alpha, 'state) TM -> ('alpha, 'state) TM
  val TM_inputsymbs_fupd
     : (('alpha -> bool) -> 'alpha -> bool) ->
       ('alpha, 'state) TM -> ('alpha, 'state) TM
  val TM_tapesymbs_fupd
     : (('alpha -> bool) -> 'alpha -> bool) ->
       ('alpha, 'state) TM -> ('alpha, 'state) TM
  val TM_init_fupd
     : ('state -> 'state) -> ('alpha, 'state) TM -> ('alpha, 'state) TM
  val TM_trans_fupd
     : (('state -> 'alpha -> 'state * ('alpha * dir)) ->
        'state -> 'alpha -> 'state * ('alpha * dir)) ->
       ('alpha, 'state) TM -> ('alpha, 'state) TM
  val TM_accept_fupd
     : ('state -> 'state) -> ('alpha, 'state) TM -> ('alpha, 'state) TM
  val TM_reject_fupd
     : ('state -> 'state) -> ('alpha, 'state) TM -> ('alpha, 'state) TM
  val TM_blank_fupd
     : ('alpha -> 'alpha) -> ('alpha, 'state) TM -> ('alpha, 'state) TM
  val TM_star_fupd
     : ('alpha -> 'alpha) -> ('alpha, 'state) TM -> ('alpha, 'state) TM
  datatype
  ('a ,'state )config = config of 'a list * 'a * 'state * 'a list
  val config_left : ('a, 'state) config -> 'a list
  val config_cell : ('a, 'state) config -> 'a
  val config_state : ('a, 'state) config -> 'state
  val config_right : ('a, 'state) config -> 'a list
  val config_left_fupd
     : ('a list -> 'a list) ->
       ('a, 'state) config -> ('a, 'state) config
  val config_cell_fupd
     : ('a -> 'a) -> ('a, 'state) config -> ('a, 'state) config
  val config_state_fupd
     : ('state -> 'state) -> ('a, 'state) config -> ('a, 'state) config
  val config_right_fupd
     : ('a list -> 'a list) ->
       ('a, 'state) config -> ('a, 'state) config
  val tape_of : ('a, 'state) config -> 'a list
  val Step
     : ('a, 'state) TM -> ('a, 'state) config -> ('a, 'state) config
  val Accepting : ('a, ''state) TM -> ('a, ''state) config -> bool
  val Rejecting : ('a, ''state) TM -> ('a, ''state) config -> bool
  val Terminal : ('a, ''state) TM -> ('a, ''state) config -> bool
  val Initial : ('a, 'state) TM -> 'a list -> ('a, 'state) config
  val Run : ('a, ''b) TM -> ('a, ''b) config -> num -> ('a, ''b) config
end
