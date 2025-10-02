with import <nixpkgs> {};
mkShell {
  packages = [
    bashInteractive
    dafny
  ];
}
