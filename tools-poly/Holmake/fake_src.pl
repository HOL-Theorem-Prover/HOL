while (<>) {
  s|^val HOLDIR = .*$|val HOLDIR = "/local/scratch/mn200/Work/hol98/"|;
  s|^val MOSMLDIR = .*$|val MOSMLDIR = "/local/scratch/kxs/200/"|;
  s|^val DEPDIR = .*$|val DEPDIR = ".HOLMK"|;
  s|^fun MK_XABLE file = .*$|fun MK_XABLE file = (Process.system ("chmod a+x "^file); file)|;
  s|^val DEFAULT_OVERLAY = .*$|val DEFAULT_OVERLAY = SOME "Overlay.ui"|;
  print;
}
