{
  description = "Isabelle arithmetization flake";
  nixConfig.bash-prompt = "[nix-develop-isabelle:] ";

  outputs = { self, nixpkgs }: {

    devShells.x86_64-linux.default =
      with nixpkgs.legacyPackages.x86_64-linux;
      stdenv.mkDerivation {
        name = "isabelle-shell";
        buildInputs = [ isabelle ];
        src = ./.;
      };

  };
}
