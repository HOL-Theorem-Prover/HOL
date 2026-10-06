signature HM_TheoryDat =
sig

  (* Compatibility wrapper for cachekey ancestry discovery. Returns []
     on failure, conservatively retaining hash inputs. For validation
     use TheoryDat, which distinguishes failure from empty parentage. *)
  val extract_parents : string -> (string * string) list

  (* Locate a parent theory's .dat file by name, searching
     [search_dirs] for either the Poly-munged
     <dir>/.hol/objs/<thy>Theory.dat or the plain
     <dir>/<thy>Theory.dat, then falling back to sigobj and the
     symlink target of sigobj/<thy>Theory.uo.  Returns NONE if not
     found. *)
  val find_parent_dat : string list -> string -> string option

end
