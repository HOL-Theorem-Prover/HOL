signature Lock =
sig

  (* A named mutex, used to serialize a critical section.  Under Poly/ML
     this is a real Thread.Mutex; under mosml it is a no-op (mosml has
     no concurrency, so no protection is needed). *)
  type t
  val new          : string -> t
  val synchronized : t -> (unit -> 'a) -> 'a

end
