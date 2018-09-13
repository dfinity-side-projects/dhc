{ pkgs ? import <nixpkgs> {}, compiler ? "ghc822" }:
with pkgs; let
  dhc = haskellPackages.callCabal2nix "dhc" ../dhc {};
  drv = haskellPackages.callCabal2nix "hero" ./. { inherit dhc; };
in if pkgs.lib.inNixShell 
  then stdenv.lib.overrideDerivation drv.env (oldAttrs : 
    {
      nativeBuildInputs = oldAttrs.nativeBuildInputs ++ [ cabal-install stack ];
    })
  else drv
