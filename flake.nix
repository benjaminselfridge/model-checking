{
  description = "Introduction to model checking, written in literate Haskell";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        haskellPackages = pkgs.haskellPackages;
        packageName = "model-checking";
      in
      {
        packages = {
          ${packageName} =
            (haskellPackages.callCabal2nix packageName self { }).overrideAttrs
              (old: {
                nativeBuildInputs = old.nativeBuildInputs ++ [ pkgs.pandoc.out ];
                postInstall =
                  let
                    pandoc-gen-html = { title, name }: ''
                      pandoc -s --toc --metadata title="${title}" \
                      -f markdown+lhs -t html -c pandoc.css \
                      -o $doc/share/doc/${old.pname}-${old.version}/html/src/${name}.html src/${name}.lhs
                    '';
                    pandoc-gen-md = { title, name }: ''
                      pandoc -s --metadata title="${title}" \
                      -f markdown+lhs -t markdown \
                      -o $doc/share/doc/${old.pname}-${old.version}/html/src/${name}.md src/${name}.lhs
                    '';
                    articles = [
                      {
                        title = "Model Checking in Haskell, Part 1: Transition Systems and Invariants";
                        name = "ModelChecking1";
                      }
                      {
                        title = "Model Checking in Haskell, Part 2: From Programs to Transition Systems";
                        name = "ModelChecking2";
                      }
                    ];
                  in
                  old.postInstall or ""
                  + (pkgs.lib.strings.concatLines [
                    "cp css/pandoc.css -t $doc/share/doc/${old.pname}-${old.version}/html/src/"
                    (pkgs.lib.strings.concatMapStrings pandoc-gen-html articles)
                    (pkgs.lib.strings.concatMapStrings pandoc-gen-md articles)
                  ]);
              });
          default = self.packages.${system}.${packageName}.doc;
        };
        defaultPackage = self.packages.${system}.${packageName};
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            cabal-install
            pandoc
          ];
          inputsFrom = [ self.packages.${system}.default.env ];
        };
      });

  nixConfig.bash-prompt = ''\n\[\e[1;32m\][\[\e[0m\]\[\e[1;34m\]devshell\[\e[0m\]\[\e[1;32m\]:\w]\$\[\[\e[0m\] '';
}

