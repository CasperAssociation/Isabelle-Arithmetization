{
  description = "Isabelle arithmetization flake";
  nixConfig.bash-prompt = "[nix-develop-isabelle:] ";

  outputs = { self, nixpkgs }: {

    devShells.x86_64-linux.default =
      with nixpkgs.legacyPackages.x86_64-linux;
      stdenv.mkDerivation {
        name = "isabelle-shell";
        buildInputs = [ isabelle fontconfig ];
        src = ./.;
      };

   packages.x86_64-linux.default =
     with nixpkgs.legacyPackages.x86_64-linux;
      stdenv.mkDerivation {
        name = "isabelle-theories";
        buildInputs = [ isabelle util-linux fontconfig ]
          ++ texlive.luatex.pkgs;
        src = ./.;
        buildPhase = ''
          export UUID=$(uuidgen)
          mkdir -p /tmp/$UUID
          HOME=/tmp/$UUID isabelle build -D .
        '';
      };

  };
}
