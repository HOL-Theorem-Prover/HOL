structure PFTTranscode :> PFTTranscode = struct

fun transcode {input, input_binary, output, output_binary} =
  let
    val {version, ruleset} =
      PFTReader.read_header {file = input, binary = input_binary}
    val descs = PFTOpcodes.descs_for_ruleset ruleset
    val out = PFTWriter.openOut
      {file = output, binary = output_binary,
       version = version, ruleset = ruleset}

    val fh : PFTReader.format_handler = {
      tyvar     = fn (id, n)        => PFTWriter.tyvar out id n,
      tyop      = fn (id, n, args)  => PFTWriter.tyop out id n args,
      var       = fn (id, n, ty)    => PFTWriter.var out id n ty,
      const     = fn (id, n, ty)    => PFTWriter.const out id n ty,
      comb      = fn (id, a, b)     => PFTWriter.comb out id a b,
      abs       = fn (id, a, b)     => PFTWriter.abs out id a b,
      new_const = fn (n, ty)        => PFTWriter.new_const out n ty,
      new_type  = fn (n, a)         => PFTWriter.new_type out n a,
      axiom     = fn (id, tm, nOpt) => PFTWriter.axiom out id tm nOpt,
      save      = fn (n, th)        => PFTWriter.save out n th,
      load      = fn (id, n)        => PFTWriter.load out id n,
      del       = fn (ns, id)       => PFTWriter.del out ns id,
      del_range = fn (ns, lo, hi)   => PFTWriter.del_range out ns lo hi
    }

    val rh : PFTReader.ruleset_handler = fn opc => fn sr =>
      let val desc = PFTOpcodes.lookup_desc descs opc
          val result = #readVarint sr ()
          val args = PFTReader.read_raw_args desc sr
      in PFTWriter.write_raw out
           {opcode=opc, desc=desc, result=result, args=args}
      end

    val {n_ty, n_tm, n_th, n_ci, ...} =
      PFTReader.read {file = input, binary = input_binary,
                      format_handler = fh, ruleset_handler = rh}
  in PFTWriter.closeOut out
       {n_ty = n_ty, n_tm = n_tm, n_th = n_th, n_ci = n_ci}
  end

end
