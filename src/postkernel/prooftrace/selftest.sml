open testutils
val _ = PFTMerge.merge
val _ = PFTReplay.replay
val _ = PFTWriter.openOut
val _ = use "selftest-pftreader.sml"
val _ = use "selftest-pftmerge.sml"
