(*
 *  util/tuple.sml  --  functions on tuples
 *
 *  COPYRIGHT (c) 1997 by Martin Erwig.  See COPYRIGHT file for details.
 *)

structure UTuple =
struct

  (* building *)
  fun pair x y = (x,y) 
  fun triple x y z = (x,y,z) 
 
  (* projection *)
     (** pairs **)
  fun swap (x,y) = (y,x)
  fun p1 (x,y) = x
  fun p2 (x,y) = y
     (** triples **)
  fun rotl (x,y,z) = (y,z,x)
  fun t1  (x,y,z) = x
  fun t2  (x,y,z) = y
  fun t3  (x,y,z) = z
  fun t12 (x,y,z) = (x,y)
  fun t23 (x,y,z) = (y,z)
  fun t13 (x,y,z) = (x,z)
     (** quadruples **)
  fun rotl (x,y,z,a) = (y,z,a,x)
  fun q1  (x,y,z,a) = x
  fun q2  (x,y,z,a) = y
  fun q3  (x,y,z,a) = z
  fun q4  (x,y,z,a) = a
  fun q12 (x,y,z,a) = (x,y)
  fun q23 (x,y,z,a) = (y,z)
  fun q34 (x,y,z,a) = (z,a)
      (* ... *)

  (* extension *)
     (** pairs **)
  fun pL a (x,y) = (a,x,y)
  fun pR a (x,y) = (x,y,a)
     (** triples **)
  fun tL a (x,y,z) = (a,x,y,z)
  fun tR a (x,y,z) = (x,y,z,a)

  (* distribution *)
     (** plain pairs *)
  fun P1 f (x,y) = (f x,y)
  fun P2 f (x,y) = (x,f y)
     (** plain pairs *)
  fun T1 f (x,y,z) = (f x,y,z)
  fun T2 f (x,y,z) = (x,f y,z)
  fun T3 f (x,y,z) = (x,y,f z)


  (* sectioning *)
  fun secl f x = fn y=>f (x,y)
  fun secr f y = fn x=>f (x,y)
end
