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

User-specified Function Overrides
=================================

When verifying programs, it is almost always useful to be able to stub out program functionality that is not important for the verification.  For example, one may want to turn calls to ``printf`` into no-ops to significantly speed up verification.  Normally, these function overrides are written in Haskell; this is expressive, but not user friendly (end users are unlikely to know Haskell or to have a Haskell build environment available).

To better support end users, and enable faster experimentation, ``ambient-verifier`` supports a concrete syntax for overrides that is based on a simple s-expression grammar.  The concrete syntax is documented in the `crucible-syntax <https://github.com/GaloisInc/crucible/blob/master/crucible-syntax/README.txt>`_ repository.  In addition to the base constructs provided by the core concrete syntax, ``ambient-verifier`` supports additional primitives.  A directory containing overrides can be specified to the verifier using the ``--overrides`` command line option.

Example::
  (defun @padd ((p1 Pointer) (p2 (Bitvector 64))) Pointer
  (start start:
    (let res (pointer-add p1 p2))
    (return res)))

Types
-----

The main type addition is for representing pointers:

- ``Pointer``

Unlike C/C++, these pointers are untyped and essentially correspond to ``uint8_t*``.

Operations
----------

The extra operations supported in ``ambient-verifier`` are:

- ``pointer-add :: Pointer -> Bitvector w -> Pointer`` where ``w`` is the number of bits in a pointer (usually 32 or 64).
- ``pointer-sub :: Pointer -> Bitvector w -> Pointer`` where ``w`` is the number of bits in a pointer (usually 32 or 64).
- ``pointer-eq :: Pointer -> Pointer -> Bool``.
- ``pointer-read :: Nat -> Endianness -> Pointer -> Bitvector w`` where the first argument is the size of the read in bytes, the second argument is ``le`` or ``be``, and ``w`` is the size of the read in bits (will match the ``Nat`` argument).
- ``pointer-write :: Nat -> Endianness -> Pointer -> Bitvector w -> Unit`` where the first argument is the size of the write in bytes, the second argument is ``le`` or ``be``, and ``w`` is the size of the write in bits (must match the ``Nat`` argument).
