(* ========================================================================= *)
(* FILE          : hhSlice.sml                                               *)
(* DESCRIPTION   : HolyHammer slice schedule construction                    *)
(* ========================================================================= *)

structure hhSlice :> hhSlice =
struct

(* Each entry consumes the next unused entry of that prover's slice table.
   The built-in tables are subsequences of hhProver.portfolio, so walking
   its provers reproduces the portfolio order. *)
val rotation = map #prover hhProver.portfolio

val distinct = aiLib.mk_sameorder_set hhConfig.prover_compare

fun round_robin count items =
  let
    fun loop 0 _ result = List.rev result
      | loop _ [] result = List.rev result
      | loop n (item :: rest) result =
          loop (n - 1) (if null rest then items else rest) (item :: result)
  in
    loop count items []
  end

fun schedule_of_provers requested count =
  if count <= 0 then []
  else
    let
      val requested' = distinct requested
      val initial =
        List.filter (fn prover => Lib.mem prover requested') rotation
      val initial_count = length initial
    in
      if count <= initial_count then aiLib.first_n count initial
      else initial @ round_robin (count - initial_count) requested'
    end

fun cap NONE nfacts = nfacts
  | cap (SOME maximum) nfacts = Int.min (maximum, nfacts)

fun overridden override value = if override = "" then value else override

datatype encoding =
    Legacy
  | Generated of {format : hhTptpProblem.format,
                  type_enc : hhTypeEnc.type_enc,
                  lam_trans : hhLamTrans.mode}

fun encoding_of ({format, type_enc, lam_trans, ...} : hhProver.slice) =
  let
    val parsed_format = hhTypeEnc.format_of_string format
    val parsed_type_enc = hhTypeEnc.adjust_type_enc parsed_format
      (hhTypeEnc.of_string type_enc)
    fun invalid () =
      raise Fail ("invalid HolyHammer lambda translation '" ^ lam_trans ^
        "' for (" ^ format ^ ", " ^ type_enc ^ ")")
  in
    case parsed_type_enc of
        hhTypeEnc.LegacySP => if lam_trans = "" then Legacy else invalid ()
      | _ =>
          if hhLamTrans.valid_mode lam_trans then
            Generated {format = parsed_format, type_enc = parsed_type_enc,
                       lam_trans = hhLamTrans.mode_of_string lam_trans}
          else invalid ()
  end

fun validate_slice (config : hhProver.prover_config)
    (slice : hhProver.slice) =
  let
    val format = #format slice
    val filter = #filter slice
    val _ = encoding_of slice
    val _ =
      if List.exists (fn supported => supported = format)
          (#supported_formats config)
      then ()
      else raise Fail ("HolyHammer prover '" ^ #name config ^
        "' does not support format '" ^ format ^ "'")
    val _ =
      if filter <> "" andalso filter = hhConfig.trim filter andalso
         hhConfig.valid_filter filter then ()
      else raise Fail ("invalid HolyHammer premise filter '" ^ filter ^ "'")
  in
    slice
  end

fun adjust_slice (options : hhConfig.hh_options)
    (slice : hhProver.slice) : hhProver.slice =
  {prover = #prover slice,
   format = overridden (#format options) (#format slice),
   type_enc = overridden (#type_enc options) (#type_enc slice),
   lam_trans = overridden (#lam_trans options) (#lam_trans slice),
   nfacts = cap (#max_facts options) (#nfacts slice),
   filter = overridden (#filter options) (#filter slice),
   extra_opts = #extra_opts slice,
   slice_size = #slice_size slice}

val same_slice = hhProver.same_slice

fun mk_schedule (options : hhConfig.hh_options) =
  let
    val requested = distinct (#provers options)
    val tables =
      map (fn prover =>
        let val config = hhProver.config_of prover
        in (prover, config, #slices config) end) requested
    val order = schedule_of_provers requested (#slices options)

    fun consume _ [] = NONE
      | consume prover ((entry as (other, config, slices)) :: rest) =
          if prover = other then
            (case slices of
                 [] => NONE
               | slice :: tail =>
                   SOME (config, slice, (other, config, tail) :: rest))
          else
            case consume prover rest of
                NONE => NONE
              | SOME (config', slice, rest') =>
                  SOME (config', slice, entry :: rest')

    fun walk _ _ [] result = List.rev result
      | walk tables seen (prover :: rest) result =
          case consume prover tables of
              NONE => walk tables seen rest result
            | SOME (config, slice, tables') =>
                let
                  val adjusted =
                    validate_slice config (adjust_slice options slice)
                in
                  if List.exists (same_slice adjusted) seen then
                    walk tables' seen rest result
                  else
                    walk tables' (adjusted :: seen) rest
                      ((config, adjusted) :: result)
                end
  in
    walk tables [] order []
  end

(* Each distinct filter in first-use order, with its largest fact count. *)
fun filter_maxima schedule =
  let
    fun add slice [] = [(#filter slice, #nfacts slice)]
      | add slice ((filter, maximum) :: rest) =
          if #filter slice = filter then
            (filter, Int.max (maximum, #nfacts slice)) :: rest
          else
            (filter, maximum) :: add slice rest
  in
    foldl (fn ((_, slice), maxima) => add slice maxima) [] schedule
  end

fun slice_budget schedule_len (options : hhConfig.hh_options)
    (slice : hhProver.slice) =
  if schedule_len <= 0 orelse #cores options <= 0 then 0.0
  else
    let
      (* Deliberately use the actual schedule length.  Unlike Sledgehammer's
         requested-count formula, this does not starve short slice tables. *)
      val batches = (schedule_len + #cores options - 1) div #cores options
    in
      Real.fromInt (#slice_size slice) * Real.fromInt (#timeout options) /
      Real.fromInt batches
    end

end
