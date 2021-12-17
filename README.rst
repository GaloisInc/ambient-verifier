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

The ``overrides`` directory contains various overrides that we have curated for particular applications.

Types
-----

One main type addition is for representing pointers:

- ``Pointer``

Unlike C/C++, these pointers are untyped and essentially correspond to ``uint8_t*``.

``ambient-verifier`` also adds a few wrappers around ``Bitvector`` types for portability and convenience:

- ``Byte`` is an alias for ``Bitvector 8``.
- ``Int`` is an alias for ``Bitvector 32``.
- ``Long`` is an alias for ``Bitvector 32`` on Arm32 and ``Bitvector 64`` on X86_64.
- ``PidT`` is an alias for ``Bitvector 32``.
- ``SizeT`` is an alias for ``Bitvector 32`` on Arm32 and ``Bitvector 64`` on X86_64.
- ``UidT`` is an alias for ``Bitvector 32``.

Operations
----------

The extra operations supported in ``ambient-verifier`` are:

- ``bv-typed-literal :: Type -> Integer -> Bitvector w`` where the first argument is a ``Bitvector`` type alias (see the Types section), the second argument is the value the ``Bitvector`` should contain, and ``w`` is the number of bits in the returned ``Bitvector`` (will match the width of the ``Type`` argument).
- ``make-null :: Pointer`` returns a null pointer.
- ``pointer-add :: Pointer -> Bitvector w -> Pointer`` where ``w`` is the number of bits in a pointer (usually 32 or 64).
- ``pointer-diff :: Pointer -> Pointer -> Bitvector w`` where ``w`` is the number of bits in a pointer (usually 32 or 64).
- ``pointer-sub :: Pointer -> Bitvector w -> Pointer`` where ``w`` is the number of bits in a pointer (usually 32 or 64).
- ``pointer-eq :: Pointer -> Pointer -> Bool``.
- ``pointer-read :: Nat -> Endianness -> Pointer -> Bitvector w`` where the first argument is the size of the read in bytes, the second argument is ``le`` or ``be``, and ``w`` is the size of the read in bits (will match the ``Nat`` argument).
- ``pointer-write :: Nat -> Endianness -> Pointer -> Bitvector w -> Unit`` where the first argument is the size of the write in bytes, the second argument is ``le`` or ``be``, and ``w`` is the size of the write in bits (must match the ``Nat`` argument).

Limitations
===========

The verifier only supports statically linked programs at present (`related issue <https://gitlab-ext.galois.com/ambient/verifier/-/issues/6>`_). Moreover, the implementations of the ``_start()`` function in ``glibc`` (`related issue <https://gitlab-ext.galois.com/ambient/verifier/-/issues/22>`_) and ``musl`` (`related issue <https://gitlab-ext.galois.com/ambient/verifier/-/issues/23>`_) gives the verifier trouble. To work around these issues, it is recommended that you:

1. Implement a custom ``_start()`` function in your binary like so::

     void _start(void) {
       main();
     }

   While this is too simple of an implementation of ``_start()`` for actually running the binary, it avoids the complexities of ``_start()``'s actual implementation in ``glibc`` and ``musl``.
2. Compile the binary with the following flags::

   $ ${CC} -static -nostartfiles -no-pie foo.c -o foo.exe
