signature HM_TheoryDat =
sig

  (* Textual scan of a Theory.dat header, returning the recorded
     parents as (name, sha1) pairs.  Returns [] on read or parse
     failure -- callers should treat that as "can't recover the
     ancestry chain through this file". *)
  val extract_parents : string -> (string * string) list

  (* Locate a parent theory's .dat file by name, searching
     [search_dirs] for <thy>Theory.dat, first in each directory's
     products directory (HFS_NameMunge.objdir_for), then directly in
     that directory.  Falls back to sigobj and the
     symlink target of sigobj/<thy>Theory.uo.  Returns NONE if not
     found. *)
  val find_parent_dat : string list -> string -> string option

end
