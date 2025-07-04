structure locn :> locn =
struct

  datatype locn_point = LocP of int
                              * int
                              * int
                      | LocA of int
                              * int
                      | LocPBeg of int
                      | LocPEnd of int

  fun locn_point_toString (LocP(nf,r,c))
      = "frag "^Int.toString(nf)^" row "^Int.toString(r)^" col "^Int.toString(c)
    | locn_point_toString (LocA(r,c))
      = "line "^Int.toString(r+1)^", character "^Int.toString(c+1)
    | locn_point_toString (LocPBeg(nf))
      = "beginning of frag "^Int.toString(nf)
    | locn_point_toString (LocPEnd(nf))
      = "end of frag "^Int.toString(nf)

  fun rel_to_abs row col (LocP(nf,r,c))
      = if r = 0 then
            LocA(row,col+c)
        else
            LocA(row+r,c)
    | rel_to_abs row col locp
      = locp

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
    | toString (Loc(LocA(r1,c1),LocA(r2,c2)))
      = if r1 <> r2 then
            "between line "^
            Int.toString(r1+1)^", character "^Int.toString c1^
            " and line "^
            Int.toString(r2+1)^", character "^Int.toString c2
        else if c1 <> c2 then
            "on line "^Int.toString(r1+1)^
            ", characters "^
            Int.toString c1^"-"^Int.toString c2
        else
            "at line "^Int.toString(r1+1)^", character "^Int.toString c1
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

  fun toShortString loc = let
    fun p2str lp =
        case lp of
          LocP(f,l,c) => "f"^Int.toString f^":"^Int.toString l^":"^
                         Int.toString c
        | LocA(l,c) => Int.toString (l+1)^":"^ Int.toString c
        | LocPBeg i => "f"^Int.toString i
        | LocPEnd i => "f"^Int.toString i
  in
    case loc of
      Loc(p1,p2) => p2str p1 ^ "-" ^ p2str p2
    | Loc_None => "<no loc>"
    | Loc_Unknown => "<??>"
    | Loc_Near loc => "~" ^ toShortString loc
  end

  fun locp p = Loc(p,p)

  fun locfrag nf = Loc(LocPBeg nf,LocPEnd nf)

  fun move_start delta (Loc(LocP(nf,r,c),e)) = Loc(LocP(nf,r,c+delta),e)
    | move_start delta (Loc(LocA(r,c),e))    = Loc(LocA(r,c+delta),e)
    | move_start delta locn                  = locn

  fun split_at delta (Loc(LocP(nf,r,c),e))
      = (Loc(LocP(nf,r,c),LocP(nf,r,c+delta-1)),
         Loc(LocP(nf,r,c+delta),e))
    | split_at delta (Loc(LocA(r,c),e))
      = (Loc(LocA(r,c),LocA(r,c+delta-1)),
         Loc(LocA(r,c+delta),e))
    | split_at delta locn
      = (locn,locn)

  fun near (loc as Loc_Near _) = loc
    | near  loc                = Loc_Near loc

  fun between (Loc(lploc,_))  (Loc(_,rploc))  = Loc(lploc,rploc)
    | between  Loc_None        rloc           = rloc
    | between  lloc            Loc_None       = lloc
    | between  Loc_Unknown     rloc           = near rloc
    | between  lloc            Loc_Unknown    = near lloc
    | between (Loc_Near lloc)  rloc           = near (between lloc rloc)
    | between  lloc           (Loc_Near rloc) = near (between lloc rloc)

  type 'a located = 'a * locn

end;
