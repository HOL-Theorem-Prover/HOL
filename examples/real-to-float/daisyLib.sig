signature daisyLib =
sig

    include Abbrev

    val run_daisy : string -> term -> thm

end
