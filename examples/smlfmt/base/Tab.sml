(** Copyright (c) 2022 Sam Westrick
  *
  * See the file LICENSE for details.
  *)

structure Tab:
sig

  structure Style:
  sig
    type style
    type t = style

    val inplace: style (* default *)
    val indented: style
    val indentedAtLeastBy: int -> style
    val indentedAtMostBy: int -> style
    val indentedExactlyBy: int -> style
    val rigid: style
    val allowComments: style

    val combine: style * style -> style

    val isRigid: style -> bool
    val minIndent: style -> int
    val maxIndent: style -> int
    val isInplace: style -> bool
    val allowsComments: style -> bool
  end

  type tab
  type t = tab

  val root: tab
  val new: {parent: tab, style: Style.t} -> tab

  val parent: tab -> tab option
  val style: tab -> Style.t
  val depth: tab -> int

  val eq: tab * tab -> bool
  val compare: tab * tab -> order

  val minIndent: tab -> int
  val maxIndent: tab -> int
  val isInplace: tab -> bool
  val isRigid: tab -> bool
  val allowsComments: tab -> bool

  val name: tab -> string
  val toString: tab -> string

end =
struct

  (* ===================================================================== *)

  structure Style =
  struct

    datatype indent_style =
      Inplace
    | Indented of {minIndent: int option, maxIndent: int option}

    datatype style =
      S of {indent: indent_style, rigid: bool, allowsComments: bool}

    type t = style

    fun combineOpts g (o1, o2) =
      case (o1, o2) of
        (NONE, _) => o2
      | (_, NONE) => o1
      | (SOME x, SOME y) => SOME (g (x, y))

    fun combineIndentStyles (i1, i2) =
      case (i1, i2) of
        (Inplace, Inplace) => Inplace
      | (Inplace, Indented _) => i2
      | (Indented _, Inplace) => i1
      | ( Indented {minIndent = min1, maxIndent = max1}
        , Indented {minIndent = min2, maxIndent = max2}
        ) =>
          Indented
            { minIndent = combineOpts Int.max (min1, min2)
            , maxIndent = combineOpts Int.min (max1, max2)
            }

    fun combine (s1, s2) =
      let
        val S {indent = i1, rigid = r1, allowsComments = c1} = s1
        val S {indent = i2, rigid = r2, allowsComments = c2} = s2
      in
        S { indent = combineIndentStyles (i1, i2)
          , rigid = r1 orelse r2
          , allowsComments = c1 orelse c2
          }
      end

    val inplace = S {indent = Inplace, rigid = false, allowsComments = false}
    val indented = S
      { indent = Indented {minIndent = NONE, maxIndent = NONE}
      , rigid = false
      , allowsComments = false
      }
    fun indentedAtLeastBy i =
      S { indent = Indented {minIndent = SOME i, maxIndent = NONE}
        , rigid = false
        , allowsComments = false
        }
    fun indentedAtMostBy i =
      S { indent = Indented {minIndent = NONE, maxIndent = SOME i}
        , rigid = false
        , allowsComments = false
        }
    fun indentedExactlyBy i =
      S { indent = Indented {minIndent = SOME i, maxIndent = SOME i}
        , rigid = false
        , allowsComments = false
        }
    val rigid = S {indent = Inplace, rigid = true, allowsComments = false}
    val allowComments =
      S {indent = Inplace, rigid = false, allowsComments = true}

    fun isRigid (S {rigid, ...}) = rigid

    fun isInplace (S {indent, ...}) =
      case indent of
        Inplace => true
      | _ => false

    fun minIndent (S {indent, ...}) =
      case indent of
        Indented {minIndent = SOME mi, ...} => mi
      | _ => 0

    fun maxIndent (S {indent, ...}) =
      case indent of
        Indented {maxIndent = SOME mi, ...} => mi
      | _ => valOf Int.maxInt

    fun allowsComments (S {allowsComments = c, ...}) = c
  end

  (* ===================================================================== *)


  datatype tab =
    Tab of {id: int, style: Style.t, parent: tab}
  | Root

  type t = tab

  val tabCounter = ref 0

  fun new {parent, style} =
    let val c = !tabCounter
    in tabCounter := c + 1; Tab {id = c, style = style, parent = parent}
    end

  val root = Root

  fun parent t =
    case t of
      Root => NONE
    | Tab {parent, ...} => SOME parent

  fun style t =
    case t of
      Root => Style.inplace
    | Tab {style = s, ...} => s

  fun name t =
    case t of
      Root => "root"
    | Tab {id = c, ...} => Int.toString c

  fun toString t =
    "[" ^ name t ^ "]"

  fun compare (t1: tab, t2: tab) : order =
    case (t1, t2) of
      (Root, Root) => EQUAL
    | (Tab t1, Tab t2) => Int.compare (#id t1, #id t2)
    | (Tab _, Root) => GREATER
    | (Root, Tab _) => LESS

  fun eq (t1, t2) =
    compare (t1, t2) = EQUAL

  fun depth t =
    case t of
      Root => 0
    | Tab {parent = p, ...} => 1 + depth p

  fun isRigid t =
    Style.isRigid (style t)
  fun isInplace t =
    Style.isInplace (style t)
  fun minIndent t =
    Style.minIndent (style t)
  fun maxIndent t =
    Style.maxIndent (style t)
  fun allowsComments t =
    Style.allowsComments (style t)

end
