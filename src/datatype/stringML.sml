structure stringML :> stringML = 
struct
  open String;
  type char = Char.char

  fun curry f x y = f (x,y);

end
