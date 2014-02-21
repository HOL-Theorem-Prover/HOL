structure Runtime :> Runtime =
struct

local
   val t = Option.valOf o Time.fromString
   val second = t "1"
   val minute = t "60"
   val hour = t "3600"
   fun divmod (x, y) = (x div y, x mod y)
   fun toStr v u = StringCvt.padLeft #"0" 2 (Int.toString v) ^ u
in
   fun timeToString t =
      if Time.< (t, second)
         then Time.fmt 5 t ^ "s"
      else if Time.< (t, minute)
         then Time.toString t ^ "s"
      else let
              val (m, s) = divmod (Time.toSeconds t, 60)
           in
              if Time.< (t, hour)
                 then Int.toString m ^ "m" ^ toStr s "s"
              else let
                     val (h, m) = divmod (m, 60)
                     val (d, h) = divmod (h, 24)
                   in
                      (if d = 0
                          then ""
                       else if d = 1
                          then "1 day "
                       else Int.toString d ^ " days ") ^
                      Int.toString h ^ "h" ^ toStr m "m" ^ toStr s "s"
                   end
           end
end

fun start_time () = Timer.startCPUTimer ()

fun end_time timer =
   let
      val {sys, usr} = Timer.checkCPUTimer timer
      val gc = Timer.checkGCTime timer
   in
      TextIO.output (TextIO.stdOut,
           "runtime: " ^ timeToString usr ^ ",\
       \    gctime: " ^ timeToString gc ^ ", \
       \    systime: " ^ timeToString sys ^ ".\n");
      TextIO.flushOut TextIO.stdOut
   end

fun time f x =
   let
      val timer = start_time ()
      val y = f x handle e => (end_time timer; raise e)
   in
      end_time timer; y
   end

end
