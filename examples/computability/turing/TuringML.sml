structure TuringML :> TuringML =
struct
  nonfix Run Initial Terminal Rejecting Accepting Step tape_of
         config_right_fupd config_state_fupd config_cell_fupd
         config_left_fupd config_right config_state config_cell
         config_left config TM_star_fupd TM_blank_fupd TM_reject_fupd
         TM_accept_fupd TM_trans_fupd TM_init_fupd TM_tapesymbs_fupd
         TM_inputsymbs_fupd TM_states_fupd TM_star TM_blank TM_reject
         TM_accept TM_trans TM_init TM_tapesymbs TM_inputsymbs TM_states
         TM R L * / div mod + - ^ @ <> > < >= <= := o before;
  
  type num = numML.num
  open numML
  open listML
  open combinML
  
  datatype dir = L | R
  datatype
  ('alpha
  ,'state
  )TM = TM of ('state -> bool) * ('alpha -> bool) * ('alpha -> bool) *
              'state * ('state -> 'alpha -> 'state * ('alpha * dir)) *
              'state * 'state * 'alpha * 'alpha
  fun TM_states (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) = v1
    
  fun TM_inputsymbs (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) = v2
    
  fun TM_tapesymbs (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) = v3
    
  fun TM_init (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) = v4
    
  fun TM_trans (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) = v5
    
  fun TM_accept (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) = v6
    
  fun TM_reject (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) = v7
    
  fun TM_blank (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) = v8
    
  fun TM_star (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) = v9
    
  fun TM_states_fupd f (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) =
        TM(f v1,v2,v3,v4,v5,v6,v7,v8,v9)
    
  fun TM_inputsymbs_fupd f (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) =
        TM(v1,f v2,v3,v4,v5,v6,v7,v8,v9)
    
  fun TM_tapesymbs_fupd f (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) =
        TM(v1,v2,f v3,v4,v5,v6,v7,v8,v9)
    
  fun TM_init_fupd f (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) =
        TM(v1,v2,v3,f v4,v5,v6,v7,v8,v9)
    
  fun TM_trans_fupd f (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) =
        TM(v1,v2,v3,v4,f v5,v6,v7,v8,v9)
    
  fun TM_accept_fupd f (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) =
        TM(v1,v2,v3,v4,v5,f v6,v7,v8,v9)
    
  fun TM_reject_fupd f (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) =
        TM(v1,v2,v3,v4,v5,v6,f v7,v8,v9)
    
  fun TM_blank_fupd f (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) =
        TM(v1,v2,v3,v4,v5,v6,v7,f v8,v9)
    
  fun TM_star_fupd f (TM(v1,v2,v3,v4,v5,v6,v7,v8,v9)) =
        TM(v1,v2,v3,v4,v5,v6,v7,v8,f v9)
    
  datatype
  ('a ,'state )config = config of 'a list * 'a * 'state * 'a list
  fun config_left (config(v1,v2,v3,v4)) = v1
    
  fun config_cell (config(v1,v2,v3,v4)) = v2
    
  fun config_state (config(v1,v2,v3,v4)) = v3
    
  fun config_right (config(v1,v2,v3,v4)) = v4
    
  fun config_left_fupd f (config(v1,v2,v3,v4)) = config(f v1,v2,v3,v4)
    
  fun config_cell_fupd f (config(v1,v2,v3,v4)) = config(v1,f v2,v3,v4)
    
  fun config_state_fupd f (config(v1,v2,v3,v4)) = config(v1,v2,f v3,v4)
    
  fun config_right_fupd f (config(v1,v2,v3,v4)) = config(v1,v2,v3,f v4)
    
  fun tape_of cnfg =
        APPEND (APPEND (REVERSE (config_left cnfg)) [config_cell cnfg])
          (config_right cnfg)
    
  fun Step M cnfg =
        let val (q,(b,d)) =
                TM_trans M (config_state cnfg) (config_cell cnfg)
        in
           if d = L then
          (case config_left cnfg
           of [] =>
                 config_cell_fupd (K b) (config_state_fupd (K q) cnfg)
            | h::t =>
                 config_left_fupd (K t)
                   (config_cell_fupd (K h)
                      (config_state_fupd (K q)
                         (config_right_fupd (K (b::config_right cnfg))
                            cnfg))))
        else
          case config_right cnfg
           of [] =>
                 config_left_fupd (K (b::config_left cnfg))
                   (config_cell_fupd (K (TM_blank M))
                      (config_state_fupd (K q) cnfg))
            | h::t =>
                 config_left_fupd (K (b::config_left cnfg))
                   (config_cell_fupd (K h)
                      (config_state_fupd (K q)
                         (config_right_fupd (K t) cnfg)))
        end
    
  fun Accepting M cnfg = config_state cnfg = TM_accept M
    
  fun Rejecting M cnfg = config_state cnfg = TM_reject M
    
  fun Terminal M cnfg = Accepting M cnfg orelse Rejecting M cnfg
    
  fun Initial M w = config([],TM_star M,TM_init M,w)
    
  fun Run M c n =
        if n = ZERO then c
        else
          let val c' = Run M c (- n ONE)
          in
             if Terminal M c' then
            c'
          else Step M c'
          end
    
end
