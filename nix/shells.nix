{
  perSystem =
    { self', pkgs, ... }:
    {
      devShells.default = pkgs.mkShell {
        buildInputs = with self'.packages; [
          agda
          (pkgs.python312.withPackages (p: [
            p.matplotlib
          ]))
          pkgs.texlab
          pkgs.ltex-ls
          pkgs.pandoc
          pkgs.gnumake
          tex
          lipics
          pkgs.fira-mono
          pkgs.dejavu_fonts
          pkgs.fontconfig
          pkgs.julia-mono
        ];
      };
    };
}
