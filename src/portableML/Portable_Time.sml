structure Portable_Time =
    struct
	open Time
	val timestamp : unit -> time = now
	val time_to_string : time -> Portable_String.string = toString
	fun dest_time t =
	    let val sec = toSeconds t
		val usec = toMicroseconds (t - fromSeconds sec)
	    in
		{sec = sec, usec = usec}
	    end
	fun mk_time {sec,usec} = fromSeconds sec + fromMicroseconds usec
	fun time_eq (t1:time) t2 = (t1 = t2)
	fun time_lt (t1:time) t2 = Time.<(t1,t2)
    end
