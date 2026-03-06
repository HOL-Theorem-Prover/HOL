let pkgs = import <nixpkgs> { }; in pkgs.callPackage ./hol-kak.nix { inherit (pkgs.kakouneUtils) buildKakounePluginFrom2Nix; }
