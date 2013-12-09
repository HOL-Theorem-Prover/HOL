signature x64_compilerLib =
sig

  include Abbrev

  val x64_compile      : term frag list -> thm * thm * thm

end
