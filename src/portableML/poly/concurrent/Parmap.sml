structure Parmap :> Parmap =
struct

  open Future
  fun parmap f l =
    joins (forks default_params (List.map (fn x => fn () => f x) l))

end;
