Overview
========

The ambient tool is a static binary verification tool for proving that weird machines in programs do (or do not) execute without errors under a variety of environmental conditions.

See the requirements and design documents in the ``doc`` directory for more details on the motivation and structure of the verifier:

- `Requirements <doc/Requirements.rst>`_
- `Design <doc/Design.rst>`_

Building
========

The verifier is built with the GHC Haskell compiler (versions 8.8 and 8.10). To get the compiler, use your distribution packages or the `ghcup tool <https://www.haskell.org/ghcup/>`_::
  ghcup install ghc 8.10.5
  ghcup install cabal 3.4.0.0

To build the verifier, first clone this repository and then::
  cd verifier
  ln -s cabal.project.dist cabal.project
  cabal configure -w ghc-8.10.5 pkg:ambient-verifier
  cabal build pkg:ambient-verifier


