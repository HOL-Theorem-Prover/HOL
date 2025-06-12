{ buildKakounePluginFrom2Nix
, lib
}:

buildKakounePluginFrom2Nix {
  pname = "hol-kak";
  version = "0.0.1";
  src = lib.sources.sourceFilesBySuffices ./. [".kak"];
}
