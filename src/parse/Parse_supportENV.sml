structure Parse_supportENV =
struct

  type pretype = Pretype.pretype
  type preterm = Preterm.preterm
  type env = {scope : (string * pretype) list,
              free  : (string * pretype) list,
              uscore_cnt : int,
              ptyE : Pretype.Env.t}

  type 'a PSM = env -> ('a * env)
  type preterm_in_env = preterm PSM

  val empty_env =
      {scope = [], free = [], uscore_cnt = 0, ptyE = Pretype.Env.empty}
  fun frees (e:env) = #free e


end
