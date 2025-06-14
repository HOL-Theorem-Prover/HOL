(** Copyright (c) 2020-2021 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

(** Expression/Pattern hierarchy
  *
  * This just implements a silly little ordering:
  *   AtExp/Pat < AppExp/Pat < InfExp/Pat < Exp/Pat
  * and then e.g. `appOkay r` checks `AppExp < r`
  *)

structure ExpPatRestriction =
struct

  datatype t =
    At (* AtExp/Pat *)
  | App (* AppExp/Pat *)
  | Inf (* InfExp/Pat *)
  | None (* Exp *)

  fun appOkay restrict =
    case restrict of
      At => false
    | _ => true

  fun infOkay restrict =
    case restrict of
      At => false
    | App => false
    | _ => true

  fun anyOkay restrict =
    case restrict of
      None => true
    | _ => false

  fun bumpUp r =
    case r of
      At => App
    | App => Inf
    | Inf => None
    | None => None

end
