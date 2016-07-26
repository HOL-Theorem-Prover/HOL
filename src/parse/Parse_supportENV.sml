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

  exception AQincompat of { nm : string, aqty : Type.hol_type,
                            loc : locn.locn, fv : bool,
                            unify_error : typecheck_error.error }

  val empty_env =
      {scope = [], free = [], uscore_cnt = 0, ptyE = Pretype.Env.empty}
  fun frees (e:env) = #free e

  fun fupd_ptyE f ({scope,free,uscore_cnt,ptyE}:env) : env =
    {scope=scope, free=free, uscore_cnt=uscore_cnt, ptyE = f ptyE}

  fun fupd_scope f ({scope,free,uscore_cnt,ptyE}:env) : env =
    {scope=f scope, free=free, uscore_cnt=uscore_cnt, ptyE = ptyE}

  fun fupd_free f ({scope,free,uscore_cnt,ptyE}:env) : env =
    {scope=scope, free=f free, uscore_cnt=uscore_cnt, ptyE = ptyE}

end
