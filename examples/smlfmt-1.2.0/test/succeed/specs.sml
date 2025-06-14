signature FOO =
  sig
    val x : int
    and y : string

    type foo
    and bar
    and 'a baz
    and ('a, 'b) bat

    eqtype 'a functions
    and are
    and ('a, 'b) values;

    type baz = int
    type foo = baz bar
    and 'a bar = unit -> 'a

    datatype 'a foo = A
    and 'a bar = A of int
    and 'a bat = A of int | B of string | C of 'a bat * 'a bat | D | E of unit
    and karl = Crary
    and bob = Harper of int
    and umut = Acar of string | Diderot of bool
    and ('a, 'b) abstract = Nonsense
    and ('a, 'b) morphism = Commuting of 'a * 'b
    and ('a, 'b) category = Endofunctor of monad | Adjunction of 'a * 'b

    datatype foo = datatype foo2;
    datatype foo = datatype A.B.foo
    datatype foo = datatype A.B.LongNameHereGoesToSomething.foo;

    exception NotFound
    and Fail of string
    and Whatever of (int -> int) list * int
    and Failure;

    structure BooBoo: BAH_BAH
    and GooGoo: GAH_GAH where type booboo = googoo

    structure Module : MODULE
    and ModuleNameAgain : REALLYLONGSIGNATURENAME
    and Stack :
      sig
        type 'a t

        val empty : 'a t
        val push : 'a -> 'a t -> 'a t
        val pop : 'a t -> ('a * 'a t) option
      end
    and Stack :
      sig
        type 'a t
      end where type 'a t = int
    sharing type Stack.t = int = Int64.int
    sharing Module.Stack = Stack

    include FOO;
    include A B C D E F G H I J K L M N O P Q R S T U V W X Y Z
    include
      sig
        type 'a t

        val instance : 'a t
      end
    include
      sig
        type 'a t
      end where type 'a t = string

    include BAR where type t = unit

    include X Y Z
    sharing X.Y = Z = This'.is.Str
  end
