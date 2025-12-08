structure parse_bnf :> parse_bnf =
struct

val one_ty = mk_thy_type {Thy = "one", Tyop = "one", Args = []}

fun isExisting_pty =
    dVartype _ => true
  | dAQ _ => true
  | dTyop{Thy,Tyop,Args} => isSome Thy andalso List.all isExisting_pty Args

fun build_existing pty =
    case pty of
        dVartype s => mk_vartype s
      | dAQ ty => ty
      | dTyop {Tyop,Thy,Args} =>
        mk_thy_type {Tyop = Tyop, Thy = valOf Thy, Args = map build_existing Args}

fun parse_pty currname previous_names pty =
    if isExisting_pty pty then constty (build_existing pty)
    else
      case pty of
          dTyop {Tyop,Thy = NONE, Args} =>
          if Tyop = currname then the_arg
          else opt_assoc T


fun parse_ctor (s, ptys) =
    case ptys of
        [] => constty onety
      | [pty] => constty (parse_pty pty)

fun parse2ftor asts =
    let
      open ParseDatatype
    in
      case asts of
          [] => []
        | (nm,dtyform) :: rest =>
          case dtyform of
              Constructors clist =>



end
