structure locn :> locn =
struct

  datatype locn_point = LocP of int
                              * int
                              * int
                      | LocPBeg of int
                      | LocPEnd of int

  fun locn_point_toString (LocP(nf,r,c))
      = "frag "^Int.toString(nf)^" row "^Int.toString(r)^" col "^Int.toString(c)
    | locn_point_toString (LocPBeg(nf))
      = "beginning of frag "^Int.toString(nf)
    | locn_point_toString (LocPEnd(nf))
      = "end of frag "^Int.toString(nf)

  datatype locn = Loc of locn_point * locn_point (* start and end character *)
                | Loc_None                       (* compiler-generated *)
                | Loc_Unknown
                | Loc_Near of locn

  (* trying to be a little clever about common cases *)
  fun toString (Loc(LocP(nf1,r1,c1),LocP(nf2,r2,c2)))
      = if nf1 <> nf2 then
            "between frag "^
            Int.toString(nf1)^" row "^Int.toString(r1)^" col "^Int.toString(c1)^
            " and frag "^
            Int.toString(nf2)^" row "^Int.toString(r2)^" col "^Int.toString(c2)
        else if r1 <> r2 then
            "in frag "^Int.toString(nf1)^", between row "^
            Int.toString(r1)^" col "^Int.toString(c1)^
            " and row "^
            Int.toString(r2)^" col "^Int.toString(c2)
        else if c1 <> c2 then
            "on frag "^Int.toString(nf1)^" row "^Int.toString(r1)^
            ", between cols "^
            Int.toString(c1)^" and "^Int.toString(c2)
        else
            "at frag "^Int.toString(nf1)^" row "^Int.toString(r1)^" col "^Int.toString(c1)
    | toString (Loc(s,e))
      = if s = e then
            "at "^locn_point_toString s
        else
            "between "^locn_point_toString s^" and "^locn_point_toString e
    | toString (Loc_None)
      = "in compiler-generated text"
    | toString (Loc_Unknown)
      = "in unknown location"
    | toString (Loc_Near(locn))
      = "roughly "^toString locn

  fun locp p = Loc(p,p)

  fun locfrag nf = Loc(LocPBeg nf,LocPEnd nf)

  fun move_start delta (Loc(LocP(nf,r,c),e)) = Loc(LocP(nf,r,c+delta),e)
    | move_start delta locn                  = locn

  fun split_at delta (Loc(LocP(nf,r,c),e))
      = (Loc(LocP(nf,r,c),LocP(nf,r,c+delta-1)),
         Loc(LocP(nf,r,c+delta),e))
    | split_at delta locn
      = (locn,locn)

  fun between (Loc(lploc,_))  (Loc(_,rploc))  = Loc(lploc,rploc)
    | between  Loc_None        rloc           = rloc
    | between  lloc            Loc_None       = lloc
    | between  Loc_Unknown     rloc           = Loc_Near rloc
    | between  lloc            Loc_Unknown    = Loc_Near lloc
    | between (Loc_Near lloc)  rloc           = Loc_Near (between lloc rloc)
    | between  lloc           (Loc_Near rloc) = Loc_Near (between lloc rloc)

  type 'a located = 'a * locn

end;
