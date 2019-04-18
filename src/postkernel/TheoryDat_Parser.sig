signature TheoryDat_Parser =
sig

  val raw_read_dat : TheoryDat_Reader.buffer -> TheoryDat_Types.dat_info
  val read_dat_file : {filename:string} -> TheoryDat_Types.dat_info

end
