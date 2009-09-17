structure SharingTables :> SharingTables =
struct

open Term Type Kind

structure Map = Binarymap
structure PP = HOLPP

infixr 3 ==>

(* ----------------------------------------------------------------------
    IDs (also known as Theory-X pairs, where X is a Name for a constant,
    or Tyops for types)
   ---------------------------------------------------------------------- *)

type id = {Thy : string, Other : string}
type idtable = {idsize : int,
                idmap : (id, int) Map.dict,
                idlist : id list}

fun make_shared_id (id : id) idtable =
    case Map.peek(#idmap idtable, id) of
      SOME i => (i, idtable)
    | NONE => let
        val {idsize, idmap, idlist} = idtable
      in
        (idsize, {idsize = idsize + 1,
                  idmap = Map.insert(idmap, id, idsize),
                  idlist = id :: idlist})
      end
fun id_compare ({Other = id1, Thy = thy1}, {Other = id2, Thy = thy2}) =
    case String.compare(id1, id2) of
      EQUAL => String.compare(thy1, thy2)
    | x => x


val empty_idtable : idtable = {idsize = 0,
                               idmap = Map.mkDict id_compare,
                               idlist = []}


fun output_idtable pps name (idtable : idtable) = let
  val out = PP.add_string pps
  fun nl() = PP.add_newline pps
  val idlist = List.rev (#idlist idtable)
  fun print_id {Thy, Other} =
      out ("ID(" ^ Lib.mlquote Thy^ ", "^Lib.mlquote Other^")")
  fun print_ids [] = ()
    | print_ids [id] = print_id id
    | print_ids (id::ids) = (print_id id; out ","; PP.add_break pps (1,0);
                             print_ids ids)
in
  out ("val "^name^" = "); nl();
  out ("  let fun ID(thy,oth) = {Thy = thy, Other = oth}"); nl();
  out ("  in Vector.fromList"); nl();
  out ("[");
  PP.begin_block pps PP.INCONSISTENT 0;
  print_ids idlist;
  PP.end_block pps;
  out "]"; nl();
  out "end;"; nl()
end


(* ----------------------------------------------------------------------
    Kinds
   ---------------------------------------------------------------------- *)

datatype shared_kind = KDTY
                     | KDV of string
                     | KDARR of int * int

type kindtable = {kdsize : int,
                  kdmap : (kind, int)Map.dict,
                  kdlist : shared_kind list}

fun make_shared_kind kd table =
    case Map.peek(#kdmap table, kd) of
      SOME i => (i, table)
    | NONE => let
      in
        if kd = typ then let
            val {kdsize, kdmap, kdlist} = table
          in
            (kdsize,
             {kdsize = kdsize + 1,
              kdmap = Map.insert(kdmap, kd, kdsize),
              kdlist = KDTY :: kdlist})
          end
        else if is_var_kind kd then let
            val {kdsize, kdmap, kdlist} = table
          in
            (kdsize,
             {kdsize = kdsize + 1,
              kdmap = Map.insert(kdmap, kd, kdsize),
              kdlist = KDV (dest_var_kind kd) :: kdlist})
          end
        else let
            val (kd1,kd2) = dest_arrow_kind kd
            fun dothis (kdarg, table) = let
              val (result, table') =
                  make_shared_kind kdarg table
            in
              (result, table')
            end
            val (newarg2, table2) = dothis (kd2, table)
            val (newarg1, table1) = dothis (kd1, table2)
            val {kdsize, kdmap, kdlist} = table1
          in
            (kdsize,
             {kdsize = kdsize + 1,
              kdmap = Map.insert(kdmap, kd, kdsize),
              kdlist = KDARR (newarg1, newarg2) :: kdlist})
          end
      end

val empty_kdtable : kindtable =
    { kdsize = 0, kdmap = Map.mkDict Kind.kind_compare, kdlist = [] }

fun build_kind_vector shkdlist = let
  fun build1 (shkd, (n, kdmap)) =
      case shkd of
        KDTY  => (n + 1, Map.insert(kdmap, n, Kind.typ))
      | KDV s => (n + 1, Map.insert(kdmap, n, Kind.mk_var_kind s))
      | KDARR (i1,i2) => let
          val kd1 = Map.find(kdmap, i1)
          val kd2 = Map.find(kdmap, i2)
        in
          (n + 1, Map.insert(kdmap, n, kd1 ==> kd2))
        end
  val (_, kdmap) =
      List.foldl build1 (0, Map.mkDict Int.compare) shkdlist
in
  Vector.fromList (map #2 (Map.listItems kdmap))
end

fun output_kindtable pps {kdtable_nm} (kdtable : kindtable) = let
  val out = PP.add_string pps
  fun nl() = PP.add_newline pps
  fun output_shkind shkd =
      case shkd of
        KDTY  => out ("KDTY")
      | KDV s => out ("KDV "^Lib.mlquote s)
      | KDARR (i1,i2) => out ("KDARR (" ^ Int.toString i1 ^ "," ^ Int.toString i2 ^ ")")
  fun output_shkinds [] = ()
    | output_shkinds [x] = output_shkind x
    | output_shkinds (x::xs) = (output_shkind x; out ",";
                                PP.add_break pps (1,0);
                                output_shkinds xs)
in
  out "local open SharingTables"; nl(); out "in"; nl();
  out ("val "^kdtable_nm^" = build_kind_vector"); nl();
  out ("[");
  PP.begin_block pps PP.INCONSISTENT 0;
  output_shkinds (List.rev (#kdlist kdtable));
  PP.end_block pps;
  out "]"; nl(); out "end"; nl()
end

(* ----------------------------------------------------------------------
    Types
   ---------------------------------------------------------------------- *)

datatype shared_type = TYV of string * int * int
                     | TYC of int * int * int
                     | TYAp of int * int
                     | TYAbs of int * int
                     | TYUni of int * int

type typetable = {tysize : int,
                  tymap : (hol_type, int)Map.dict,
                  tylist : shared_type list}

fun make_shared_type ty (tables as (idtable, kdtable, table)) =
    case Map.peek(#tymap table, ty) of
      SOME i => (i, tables)
    | NONE => let
      in
        if is_vartype ty then let
            val (name, kind, rank) = dest_var_type ty
            val (kdi, kdtable') = make_shared_kind kind kdtable
            val {tysize, tymap, tylist} = table
          in
            (tysize, (idtable, kdtable',
             {tysize = tysize + 1,
              tymap = Map.insert(tymap, ty, tysize),
              tylist = TYV (name, kdi, rank) :: tylist}))
          end
        else if is_con_type ty then let
            val {Thy, Tyop, Kind, Rank} = dest_thy_con_type ty
            val (id, idtable') =
                make_shared_id {Thy = Thy, Other = Tyop} idtable
            val (kdi, kdtable') = make_shared_kind Kind kdtable
            val {tysize, tymap, tylist} = table
          in
            (tysize, (idtable', kdtable',
             {tysize = tysize + 1,
              tymap = Map.insert(tymap, ty, tysize),
              tylist = TYC (id, kdi, Rank) :: tylist}))
          end
        else if is_app_type ty then let
            val (Opr,Arg) = dest_app_type ty
            val (Opri, tables) = make_shared_type Opr tables
            val (Argi, tables) = make_shared_type Arg tables
            val (idtable, kdtable, tytable) = tables
            val {tysize, tymap, tylist} = tytable
          in
            (tysize, (idtable, kdtable,
             {tysize = tysize + 1,
              tymap = Map.insert(tymap, ty, tysize),
              tylist = TYAp (Opri,Argi) :: tylist}))
          end
        else if is_abs_type ty then let
            val (bv,body) = dest_abs_type ty
            val (bvi, tables) = make_shared_type bv tables
            val (bodyi, tables) = make_shared_type body tables
            val (idtable, kdtable, tytable) = tables
            val {tysize, tymap, tylist} = tytable
          in
            (tysize, (idtable, kdtable,
             {tysize = tysize + 1,
              tymap = Map.insert(tymap, ty, tysize),
              tylist = TYAbs (bvi,bodyi) :: tylist}))
          end
        else (* if is_univ_type ty then *) let
            val (bv,body) = dest_univ_type ty
            val (bvi, tables) = make_shared_type bv tables
            val (bodyi, tables) = make_shared_type body tables
            val (idtable, kdtable, tytable) = tables
            val {tysize, tymap, tylist} = tytable
          in
            (tysize, (idtable, kdtable,
             {tysize = tysize + 1,
              tymap = Map.insert(tymap, ty, tysize),
              tylist = TYUni (bvi,bodyi) :: tylist}))
          end
      end

val empty_tytable : typetable =
    {tysize = 0, tymap = Map.mkDict Type.compare, tylist = [] }

fun build_type_vector idv kdv shtylist = let
  fun build1 (shty, (n, tymap)) =
      case shty of
        TYV (s,kdi,rk) => let
          val kd = Vector.sub(kdv, kdi)
        in
          (n + 1, Map.insert(tymap, n, Type.mk_var_type(s,kd,rk)))
        end
      | TYC (id,kdi,rk) => let
          val kd = Vector.sub(kdv, kdi)
          val {Thy,Other} = Vector.sub(idv, id)
        in
          (n + 1,
           Map.insert(tymap, n,
                             Type.mk_thy_con_type {Thy = Thy, Tyop = Other,
                                                   Kind = kd, Rank = rk}))
        end
      | TYAp (opri,argi) => let
          val opr = Map.find(tymap, opri)
          val arg = Map.find(tymap, argi)
        in
          (n + 1,
           Map.insert(tymap, n, Type.mk_app_type (opr,arg)))
        end
      | TYAbs (bvi,bodyi) => let
          val bv = Map.find(tymap, bvi)
          val body = Map.find(tymap, bodyi)
        in
          (n + 1,
           Map.insert(tymap, n, Type.mk_abs_type (bv,body)))
        end
      | TYUni (bvi,bodyi) => let
          val bv = Map.find(tymap, bvi)
          val body = Map.find(tymap, bodyi)
        in
          (n + 1,
           Map.insert(tymap, n, Type.mk_univ_type (bv,body)))
        end
  val (_, tymap) =
      List.foldl build1 (0, Map.mkDict Int.compare) shtylist
in
  Vector.fromList (map #2 (Map.listItems tymap))
end

fun output_typetable pps {idtable_nm,kdtable_nm,tytable_nm} (tytable : typetable) = let
  val out = PP.add_string pps
  fun nl() = PP.add_newline pps
  fun ipair_string (x,y) = "("^Int.toString x^", "^Int.toString y^")"
  fun output_shtype shty =
      case shty of
        TYV (s,kdi,rk)  => out ("TYV(" ^ Lib.mlquote s ^ "," ^
                                Int.toString kdi ^ "," ^ Int.toString rk ^ ")")
      | TYC (id,kdi,rk) => out ("TYC(" ^ Int.toString id ^ "," ^
                                Int.toString kdi ^ "," ^ Int.toString rk ^ ")")
      | TYAp (opri,argi)  => out ("TYAp"  ^ ipair_string(opri,argi))
      | TYAbs (bvi,bodyi) => out ("TYAbs" ^ ipair_string(bvi,bodyi))
      | TYUni (bvi,bodyi) => out ("TYUni" ^ ipair_string(bvi,bodyi))
  fun output_shtypes [] = ()
    | output_shtypes [x] = output_shtype x
    | output_shtypes (x::xs) = (output_shtype x; out ",";
                                PP.add_break pps (1,0);
                                output_shtypes xs)
in
  out "local open SharingTables"; nl(); out "in"; nl();
  out ("val "^tytable_nm^" = build_type_vector "^idtable_nm^" "^kdtable_nm); nl();
  out ("[");
  PP.begin_block pps PP.INCONSISTENT 0;
  output_shtypes (List.rev (#tylist tytable));
  PP.end_block pps;
  out "]"; nl(); out "end"; nl()
end

(* ----------------------------------------------------------------------
    Terms
   ---------------------------------------------------------------------- *)

datatype shared_term = TMV of string * int
                     | TMC of int * int
                     | TMAp of int * int
                     | TMAbs of int * int
                     | TMTAp of int * int
                     | TMTAbs of int * int

type termtable = {termsize : int,
                  termmap : (term, int)Map.dict,
                  termlist : shared_term list}

val empty_termtable : termtable =
    {termsize = 0, termmap = Map.mkDict Term.compare, termlist = [] }

fun make_shared_term tm (tables as (idtable,kdtable,tytable,tmtable)) =
    case Map.peek(#termmap tmtable, tm) of
      SOME i => (i, tables)
    | NONE => let
      in
        if is_var tm then let
            val (s, ty) = dest_var tm
            val (ty_i, (idtable, kdtable, tytable)) =
                make_shared_type ty (idtable, kdtable, tytable)
            val {termsize, termmap, termlist} = tmtable
          in
            (termsize,
             (idtable, kdtable, tytable,
              {termsize = termsize + 1,
               termmap = Map.insert(termmap, tm, termsize),
               termlist = TMV (s, ty_i) :: termlist}))
          end
        else if is_const tm then let
            val {Thy,Name,Ty} = dest_thy_const tm
            val (id_i, idtable) =
                make_shared_id {Thy = Thy, Other = Name} idtable
            val (ty_i, (idtable, kdtable, tytable)) =
                make_shared_type Ty (idtable, kdtable, tytable)
            val {termsize, termmap, termlist} = tmtable
          in
            (termsize,
             (idtable, kdtable, tytable,
              {termsize = termsize + 1,
               termmap = Map.insert(termmap, tm, termsize),
               termlist = TMC (id_i, ty_i) :: termlist}))
          end
        else if is_comb tm then let
            val (f, x) = dest_comb tm
            val (f_i, tables) = make_shared_term f tables
            val (x_i, tables) = make_shared_term x tables
            val (idtable, kdtable, tytable, tmtable) = tables
            val {termsize, termmap, termlist} = tmtable
          in
            (termsize,
             (idtable, kdtable, tytable,
              {termsize = termsize + 1,
               termmap = Map.insert(termmap, tm, termsize),
               termlist = TMAp(f_i, x_i) :: termlist}))
          end
        else  if is_abs tm then (* must be an abstraction *) let
            val (v, body) = dest_abs tm
            val (v_i, tables) = make_shared_term v tables
            val (body_i, tables) = make_shared_term body tables
            val (idtable, kdtable, tytable, tmtable) = tables
            val {termsize, termmap, termlist} = tmtable
          in
            (termsize,
             (idtable, kdtable, tytable,
              {termsize = termsize + 1,
               termmap = Map.insert(termmap, tm, termsize),
               termlist = TMAbs(v_i, body_i) :: termlist}))
          end
        else if is_tycomb tm then let
            val (f, a) = dest_tycomb tm
            val (f_i, tables) = make_shared_term f tables
            val (idtable, kdtable, tytable, tmtable) = tables
            val (a_i, (idtable, kdtable, tytable)) =
                make_shared_type a (idtable, kdtable, tytable)
            val {termsize, termmap, termlist} = tmtable
          in
            (termsize,
             (idtable, kdtable, tytable,
              {termsize = termsize + 1,
               termmap = Map.insert(termmap, tm, termsize),
               termlist = TMTAp(f_i, a_i) :: termlist}))
          end
        else  (* must be a type abstraction *) let
            val (a, body) = dest_tyabs tm
            val (a_i, (idtable, kdtable, tytable)) =
                make_shared_type a (idtable, kdtable, tytable)
            val tables = (idtable, kdtable, tytable, tmtable)
            val (body_i, tables) = make_shared_term body tables
            val (idtable, kdtable, tytable, tmtable) = tables
            val {termsize, termmap, termlist} = tmtable
          in
            (termsize,
             (idtable, kdtable, tytable,
              {termsize = termsize + 1,
               termmap = Map.insert(termmap, tm, termsize),
               termlist = TMTAbs(a_i, body_i) :: termlist}))
          end
      end

fun build_term_vector idv tyv shtmlist = let
  fun build1 (shtm, (n, tmmap)) =
      case shtm of
        TMV (s, tyn) => (n + 1,
                         Map.insert(tmmap, n, mk_var(s, Vector.sub(tyv, tyn))))
      | TMC (idn, tyn) => let
          val {Thy, Other} = Vector.sub(idv, idn)
          val ty = Vector.sub(tyv, tyn)
        in
          (n + 1, Map.insert(tmmap, n, mk_thy_const {Name = Other, Thy = Thy,
                                                     Ty = ty}))
        end
      | TMAp (f_n, xn) =>
        (n + 1, Map.insert(tmmap, n, mk_comb(Map.find(tmmap, f_n),
                                             Map.find(tmmap, xn))))
      | TMAbs (vn, bodyn) =>
        (n + 1, Map.insert(tmmap, n, mk_abs(Map.find(tmmap, vn),
                                            Map.find(tmmap, bodyn))))
      | TMTAp (f_n, an) =>
        (n + 1, Map.insert(tmmap, n, mk_tycomb(Map.find(tmmap, f_n),
                                               Vector.sub(tyv, an))))
      | TMTAbs (an, bodyn) =>
        (n + 1, Map.insert(tmmap, n, mk_tyabs(Vector.sub(tyv, an),
                                              Map.find(tmmap, bodyn))))
  val (_, tmmap) = List.foldl build1 (0, Map.mkDict Int.compare) shtmlist
in
  Vector.fromList (map #2 (Map.listItems tmmap))
end

fun output_termtable pps names (tmtable: termtable) = let
  val {idtable_nm,tytable_nm,termtable_nm} = names
  val out = PP.add_string pps
  fun nl() = PP.add_newline pps
  fun ipair_string (x,y) = "("^Int.toString x^", "^Int.toString y^")"
  fun output_shtm shtm =
      case shtm of
        TMV (s, tyn) => out ("TMV(" ^ Lib.mlquote s ^", "^Int.toString tyn^")")
      | TMC p => out ("TMC"^ipair_string p)
      | TMAp p => out ("TMAp"^ipair_string p)
      | TMAbs p => out ("TMAbs"^ipair_string p)
      | TMTAp p => out ("TMTAp"^ipair_string p)
      | TMTAbs p => out ("TMTAbs"^ipair_string p)
  fun output_shtms [] = ()
    | output_shtms [t] = output_shtm t
    | output_shtms (t::ts) = (output_shtm t; out (",");
                              PP.add_break pps (1, 0);
                              output_shtms ts)
in
  out ("local open SharingTables"); nl();
  out ("in"); nl();
  out ("val "^termtable_nm^" = build_term_vector "^idtable_nm^" "^
       tytable_nm); nl();
  out ("[");
  PP.begin_block pps PP.INCONSISTENT 0;
  output_shtms (List.rev (#termlist tmtable));
  PP.end_block pps;
  out ("]"); nl();
  out "end"; nl()
end;


(* ----------------------------------------------------------------------
    Theorems
   ---------------------------------------------------------------------- *)





end;
