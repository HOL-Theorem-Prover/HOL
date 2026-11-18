(* ========================================================================= *)
(* FILE          : hhCache.sml                                               *)
(* DESCRIPTION   : Persistent HolyHammer prover-result cache                  *)
(* ========================================================================= *)

structure hhCache :> hhCache =
struct

type key_parts =
  {prover : string, version : string option, argv : string list,
   problem : string}

fun join a b = OS.Path.concat (a, b)

fun frame text = Int.toString (String.size text) ^ ":" ^ text

fun normalized_argument problem content_hash argument =
  if argument = problem then content_hash
  else
    let
      val prefix = "-file:"
    in
      if String.isPrefix prefix argument andalso
         String.extract (argument, String.size prefix, NONE) = problem
      then prefix ^ content_hash
      else argument
    end

fun key_of ({prover, version, argv, problem} : key_parts) =
  let
    val content_hash = SHA1.sha1_file {filename = problem}
    val normalized = map (normalized_argument problem content_hash) argv
    val version_string = case version of NONE => "" | SOME text => text
    val material =
      String.concat
        (map frame
          (prover :: version_string :: Int.toString (length normalized) ::
           normalized @ [content_hash]))
  in
    aiLib.sha1_string material
  end

fun json_string_option NONE = JSON.NULL
  | json_string_option (SOME text) = JSON.STRING text

fun json_string_list_option NONE = JSON.NULL
  | json_string_list_option (SOME values) =
      JSON.ARRAY (map JSON.STRING values)

fun result_json ({szs, used_axioms, time, version, ...}
                 : hhProver.run_result) =
  JSON.OBJECT
    [("szs", JSON.STRING (hhProver.szs_to_string szs)),
     ("used_axioms", json_string_list_option used_axioms),
     ("time", JSON.FLOAT time),
     ("version", json_string_option version)]

fun field name value = JSONUtil.lookupField value name

fun optional decoder JSON.NULL = NONE
  | optional decoder value = SOME (decoder value)

fun result_of_json value : hhProver.run_result =
  {szs = hhProver.szs_of_string (JSONUtil.asString (field "szs" value)),
   used_axioms =
     optional (JSONUtil.arrayMap JSONUtil.asString)
       (field "used_axioms" value),
   time = JSONUtil.asNumber (field "time" value),
   version = optional JSONUtil.asString (field "version" value),
   output_file = ""}

fun cache_path (options : hhConfig.hh_options) key =
  join (#cache_dir options) key

fun remove path = OS.FileSys.remove path handle OS.SysErr _ => ()

fun read_result path = result_of_json (JSONParser.parseFile path)

fun write_result path result =
  hhConfig.write_atomically
    {open_out = TextIO.openOut, close_out = TextIO.closeOut} path
    (fn output => JSONPrinter.print (output, result_json result))

fun lookup (options : hhConfig.hh_options) key =
  if not (#cache options) then NONE
  else
    (let
       val path = cache_path options key
     in
       if not (OS.FileSys.access (path, [OS.FileSys.A_READ])) then NONE
       else
         ((let
             val result = read_result path
             val _ = OS.FileSys.setTime (path, NONE) handle OS.SysErr _ => ()
           in
             SOME result
           end)
          handle Interrupt => raise Interrupt
               | _ => (remove path; NONE))
     end
     handle Interrupt => raise Interrupt
          | _ => NONE)

fun store (options : hhConfig.hh_options) key result =
  if not (#cache options) then ()
  else
    ((hhConfig.ensure_dir (#cache_dir options);
      write_result (cache_path options key) result)
     handle Interrupt => raise Interrupt
          | _ => ())

fun is_hex character =
  Char.isDigit character orelse
  (#"a" <= character andalso character <= #"f")

fun is_entry_name name =
  String.size name = 40 andalso List.all is_hex (String.explode name)

fun entry_names directory =
  List.filter is_entry_name (hhConfig.directory_names directory)

fun cache_entries directory names =
  let
    fun entry name =
      let val path = join directory name in
        if hhConfig.is_dir path then NONE
        else SOME (OS.FileSys.modTime path, name, path)
      end
      handle OS.SysErr _ => NONE
  in
    List.mapPartial entry names
  end

fun entry_before (time1, name1, _) (time2, name2, _) =
  case Time.compare (time1, time2) of
      LESS => true
    | GREATER => false
    | EQUAL => String.compare (name1, name2) <> GREATER

fun ninety_percent maximum =
  if maximum <= 0 then 0
  else (maximum div 10) * 9 + ((maximum mod 10) * 9) div 10

fun prune (options : hhConfig.hh_options) =
  if not (#cache options) then ()
  else
    ((let
        val directory = #cache_dir options
        val names = entry_names directory
        val maximum = #cache_max_entries options
      in
        (* Count names first: stat every entry only when over the limit. *)
        if length names <= maximum then ()
        else
          let
            val entries = cache_entries directory names
            val target = ninety_percent maximum
            val oldest = aiLib.first_n (length entries - target)
              (Portable.sort entry_before entries)
          in
            List.app (remove o #3) oldest
          end
      end)
     handle Interrupt => raise Interrupt
          | _ => ())

end
