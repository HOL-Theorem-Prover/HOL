(*
 *  util/list.sml  --  some additional list utilities
 *
 *  COPYRIGHT (c) 1997 by Martin Erwig.  See COPYRIGHT file for details.
 *)

structure UList =
struct
  fun cons x l = x::l

  fun remove x []     = []
   |  remove x (y::l) = if x=y then remove x l else y::remove x l
   
  fun select _ _ []     = []
   |  select f p (x::l) = if p x then f x::select f p l else select f p l

  exception NotFound
  fun lookup _ []         = raise NotFound
   |  lookup x ((y,z)::l) = if x=y then z else lookup x l

  local 
    fun scan (_,_,_,y,[])   = y
     |  scan (f,g,w,y,x::l) = 
        let val v=g x
         in 
            if f (v,w) = w then 
               scan (f,g,w,y,l) 
            else 
               scan (f,g,v,x,l)
        end
  in
    fun thatOne (f,g) l = 
        let val (x::l') = l in scan (f,g,g x,x,l') end
  end
end
