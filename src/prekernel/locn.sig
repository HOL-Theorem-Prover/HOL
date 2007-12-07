signature locn = sig

  (* a type representing a point in the source file *)
  datatype locn_point = LocP of int (* fragment  (0-origin) *)
                              * int (* line      (0-origin) *)
                              * int (* character (0-origin) *)
                      | LocA of int (* absolute line number in file (0-origin) *)
                              * int (* absolute column number in file (0-origin) *)
                      | LocPBeg of int (* beginning of fragment *)
                      | LocPEnd of int (* end of fragment *)

  val locn_point_toString : locn_point -> string

  (* add a line,char pair to a relative location point *)
  val rel_to_abs : int -> int -> locn_point -> locn_point

  (* a type representing a location (region) in the source file *)
  datatype locn = Loc of locn_point * locn_point (* start and end character *)
                | Loc_None                       (* compiler-generated *)
                | Loc_Unknown
                | Loc_Near of locn

      (* if there are multiple QUOTE fragments in a row, they may be
      concatenated and given the number of the first fragment; the
      numbers of subsequent fragments do not change however. *)

      (* an ANTIQUOTE fragment has no characters, so no start and end
      positions *)

      (* when a token is put back, eg with qbuf.replace_current, we
      claim the new token is near where the old one was *)

  val toString : locn -> string
  val toShortString : locn -> string (* less verbose form *)

  (* single-point region *)
  val locp : locn_point -> locn
  (* whole fragment *)
  val locfrag : int -> locn

  (* adjusting locations *)
  val move_start : int -> locn -> locn
  val split_at   : int -> locn -> (locn * locn)
  val near       : locn -> locn

  (* merging locations *)
  val between    : locn -> locn -> locn

  type 'a located = 'a * locn

end;
