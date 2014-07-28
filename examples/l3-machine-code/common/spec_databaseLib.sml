structure spec_databaseLib :> spec_databaseLib =
struct

open HolKernel boolLib bossLib

val ERR = Feedback.mk_HOL_ERR "spec_databaseLib"

(* ------------------------------------------------------------------------ *)

datatype ''opt entry = Pending of thm * term | Built of (''opt list * thm) list

fun thm_eq thm1 thm2 = Term.aconv (Thm.concl thm1) (Thm.concl thm2)

(* -------------------------------------------------------------------------
   mk_spec_database

   Tools for maintaining a database of specification theorems.

   The type ''opt represents configuration options.

    - basic_opt : unit -> ''opt

      Get the options corresponding with the specification that comes directly
      from applying "basic_spec".

    - default_opt

      The default build option.

    - proj_opt

      Used to determine if the current option setting is different from
      "basic_opt".

    - closeness : ''opt -> ''opt -> int

      Gives value to ease with which one options setting can be converted to
      another. A negative result corresponds with "impossible", whereas
      a high value indicates a close match.

    - convert_opt_rule

      Gives the rule for conversting from one option setting to another.

    - get_opcode

      Extracts the database index key (usual the instructions op-code) from
      the specification theorom.

    - basic_spec : thm * term -> thm

      Gives the basic spcification.
   ------------------------------------------------------------------------- *)

fun mk_spec_database basic_opt (default_opt: ''opt) proj_opt closeness
      convert_opt_rule get_opcode basic_spec =
   let
      val current_opt = ref default_opt
      fun set_current_opt opt = current_opt := opt
      fun get_current_opt () = !current_opt
      val db = ref (LVTermNet.empty: (''opt entry) LVTermNet.lvtermnet)
      val add1 =
         fn x as Pending (_, tm) =>
               db := LVTermNet.insert (!db, ([], get_opcode (ASSUME tm)), x)
          | x as Built [] => raise ERR "add1" ""
          | x as Built ((_, thm) :: _) =>
               db := LVTermNet.insert (!db, ([], get_opcode thm), x)
      val add1_pending = add1 o Pending
      fun reset_db () =
         ( print "\nResetting specifications database.\n\n"
         ; db := LVTermNet.empty
         )
      fun current_opt_rule target = convert_opt_rule (basic_opt ()) target
      fun not_basic (opt: ''opt) = proj_opt opt <> proj_opt (basic_opt ())
      fun sub1 k = db := fst (LVTermNet.delete (!db, k))
      fun replace f (k, tm: term, new) =
         let
            val l = List.filter (f tm) (LVTermNet.find (!db, k))
         in
            sub1 k; List.app add1 (l @ [Built new])
         end
      val replace_pending =
         replace (fn tm => fn Pending (_, t) => t <> tm | _ => true)
      val replace_built =
         replace (fn tm => fn Built ((_, th) :: _) => Thm.concl th <> tm
                            | _ => true)
      fun closest target = fst o utilsLib.maximal Int.compare (closeness target)
      fun find_closest target =
         (closest target ## I) o fst o
         utilsLib.maximal Int.compare (closeness target o closest target o fst)
      fun insert_thm (opt: ''opt, thm) =
         let
            val eq_thm = thm_eq thm
            fun iter a =
               fn [] => ([opt], thm) :: List.rev a
                | (h as (opts, th)) :: t =>
                    if eq_thm th
                       then List.revAppend (a, (opt :: opts, th) :: t)
                    else iter (h :: a) t
         in
            iter []
         end
      val extract_spec =
         fn (k, Pending (x as (thm, tm))) =>
            let
               val opt = !current_opt
               val () = print "+"
               val basic = basic_spec x
               val l = [([basic_opt ()], basic)]
               val l = if not_basic opt
                          then insert_thm (opt, current_opt_rule opt basic) l
                       else l
            in
               replace_pending (k, tm, l)
               ; (true, Lib.with_exn (snd o hd) l (ERR "extract_spec" "empty"))
            end
          | (_, Built []) => raise ERR "extract_spec" "empty built"
          | (k, Built (l as (_, th) :: _)) =>
            let
               val opt = !current_opt
            in
              (false,
               case List.find (Lib.mem opt o fst) l of
                  SOME (_, thm) => thm
                | NONE => let
                             val (close_opt, close_thm) = find_closest opt l
                             val thm = convert_opt_rule close_opt opt close_thm
                          in
                             replace_built
                                (k, Thm.concl th, insert_thm (opt, thm) l)
                             ; thm
                          end)
            end
      fun find_thms opc =
         case LVTermNet.match (!db, opc) of
            [] => NONE
          | l => let
                    val (new, thms) = ListPair.unzip (List.map extract_spec l)
                 in
                    SOME (List.exists I new, thms)
                 end
       fun list_db () = List.map (snd ## I) (LVTermNet.listItems (!db))
   in
      (reset_db, set_current_opt, get_current_opt, add1_pending, find_thms,
       list_db)
   end

(* ------------------------------------------------------------------------ *)

end
