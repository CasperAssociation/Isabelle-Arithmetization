{
  description = "Isabelle arithmetization flake";
  nixConfig.bash-prompt = "[nix-develop-isabelle:] ";

  outputs = { self, nixpkgs }: 
    let pkgs = nixpkgs.legacyPackages.x86_64-linux;
        buildInputs = with pkgs;
          [ isabelle fontconfig util-linux
            (texlive.combine {
              inherit (texlive) scheme-basic collection-luatex ulem txfonts;
            })
          ];
    in
    {

      devShells.x86_64-linux.default =
        pkgs.stdenv.mkDerivation {
          name = "isabelle-shell";
          inherit buildInputs;
          src = ./.;
        };

      packages.x86_64-linux.default =
        pkgs.stdenv.mkDerivation {
           name = "isabelle-arithmetization-theories";
           inherit buildInputs;
           src = ./theories;
           buildPhase = ''
             export UUID=$(uuidgen)
             mkdir -p /tmp/$UUID
             HOME=/tmp/$UUID isabelle build -D .
           '';
           installPhase = ''
             mkdir -p $out
           '';
        };

    };
}
