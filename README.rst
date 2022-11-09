Overview
========

The ambient tool is a static binary verification tool for proving that weird machines in programs do (or do not) execute without errors under a variety of environmental conditions.

See the requirements and design documents in the ``doc`` directory for more details on the motivation and structure of the verifier:

- `Requirements <doc/Requirements.rst>`_
- `Design <doc/Design.rst>`_

Building
========

To build the verifier, first clone this repository with::

  git clone git@gitlab-ext.galois.com:ambient/verifier.git
  cd verifier
  git submodule update --init

Note: if these steps complete successfully, the directories in ``submodules/`` will be populated (not empty).

Important: do not use ``--recursive`` - it's not needed, and will result in downloading unnecessary content.

The verifier is built with the GHC Haskell compiler (versions 8.10, 9.0, and 9.2). To get the compiler, use your distribution packages or the `ghcup tool <https://www.haskell.org/ghcup/>`_::

  ghcup install ghc 9.2.4
  ghcup install cabal 3.6.2.0

Then, in the ``verifier`` directory::

  ln -s cabal.project.dist cabal.project
  cabal configure -w ghc-9.2.4 pkg:ambient-verifier
  cabal build pkg:ambient-verifier

Note that there is an optional dependency on a C compiler (``gcc`` by default)
that is used when running C overrides. (See the "User-specified Function
Overrides" section for more details.)

Running
=======

Functionality in the verifier is broken into subcommands:

- ``verify``: Verify a given binary with inputs satisfies verification
  conditions
- ``test-overrides``: Run tests present in user override files

More details on available options for the top level verifier, as well as the
various subcommands can be found using ``--help``::

  cabal run exe:ambient-verifier -- --help
  cabal run exe:ambient-verifier -- verify --help
  cabal run exe:ambient-verifier -- test-overrides --help

To run the verifier's test suite, run::

  cabal run test:ambient-tests

To record the results of a test suite run to a ``junit.xml`` file, run::

  cabal run test:ambient-tests -- --xml=junit.xml

Profiling
---------

The verifier includes functionality for profiling its performance. To generate
a profiling report, pass ``--profile-to <DIR>`` to an invocation of ``verify``.
This will generate a ``<DIR>/profile.html`` file that can be viewed in a web
browser. The data that this HTML file presents will be periodically regenerated
as the verifier runs on the program. A typical example looks like:

.. image:: screenshots/profile-example.png

The profiling report presents a hierarchical view of the functions that are
invoked during the simulation of a program. The x-axis represents the time,
and the y-axis shows the call stack depth, counting from zero at the bottom.
Each stack frame is given a score based on some simulator heuristics (the time
spent simulating it, its number of allocations, its numbers of merges, etc.).
Generally speaking, the higher the score, the more likely it is to be a
performance bottleneck.

Docker
------

There is also a nightly Docker image that gets built after each commit to the
``master`` branch. To run the verifier through Docker, take a verifier command
and replace the ``cabal run exe:ambient-verifier --`` bit with
``docker run artifactory.galois.com:5017/nightly``::

  docker run artifactory.galois.com:5017/nightly --help
  docker run artifactory.galois.com:5017/nightly verify --help
  docker run artifactory.galois.com:5017/nightly test-overrides --help

The verifier's test suite can also be run through Docker, although it requires
changing the entrypoint to use ``ambient-tests`` instead::

  docker run --entrypoint ambient-tests artifactory.galois.com:5017/nightly

To record the results of a test suite run to a ``junit.xml`` file, run::

  docker run --entrypoint ambient-tests --volume $(pwd):/test-output artifactory.galois.com:5017/nightly --xml=/test-output/junit.xml

The ``--volume $(pwd):/test-output`` mounts the current directory to
``/test-output`` in the container so that when the test suite records the
results to ``/test-output/junit.xml``, the ``junit.xml`` file is copied back
to the current directory on your host machine.

User-specified Function Overrides
=================================

When verifying programs, it is almost always useful to be able to stub out program functionality that is not important for the verification.  For example, one may want to turn calls to ``printf`` into no-ops to significantly speed up verification.  Normally, these function overrides are written in Haskell; this is expressive, but not user friendly (end users are unlikely to know Haskell or to have a Haskell build environment available).

To better support end users, and enable faster experimentation, ``ambient-verifier`` supports defining custom overrides in the following languages:

* The crucible syntax language, which is based on a simple s-expression grammar.  The concrete syntax is documented in the `crucible-syntax <https://github.com/GaloisInc/crucible/blob/master/crucible-syntax/README.txt>`_ repository. In addition to the base constructs provided by the core concrete syntax, ``ambient-verifier`` supports additional primitives.

  Example::

    (defun @padd ((p1 Pointer) (p2 (Bitvector 64))) Pointer
      (start start:
        (let res (pointer-add p1 p2))
        (return res)))

* A limited subset of the C language, which we compile into crucible syntax. See the `overrides-dsl <https://gitlab-ext.galois.com/ambient/overrides-dsl>`_ repository for more information. Note that this is not currently at feature parity with crucible syntax overrides, so if you encounter a missing feature, please open an issue at `this issue tracker <https://gitlab-ext.galois.com/ambient/overrides-dsl/-/issues>`_.

  Example::

    int abs(int x) {
        int ret = x;
        if(x < 0) {
            ret = -x;
        }
        return ret;
    }

  Note that the verifier uses a C compiler to preprocess the C file, so a C
  compiler must be available on your ``PATH``. By default, the verifier looks
  for ``gcc``, but this can be overridden using the ``--with-cc`` option.

A directory containing overrides can be specified to the verifier using the ``--overrides`` command line option.
The ``overrides`` directory in this repo contains various overrides that we have curated for particular applications.

Directory Conventions
---------------------

The ``--overrides <DIR>`` option expects the name of a directory ``DIR`` whose
contents look like: ::

  DIR/
  ├── function/
  │   ├── fun1.cbl
  │   ├── fun2.cbl
  │   ├── fun3.c
  │   ├── fun4.c
  │   └── ...
  └── overrides.yaml (optional)

The ``function`` subdirectory contains ``.cbl`` and ``.c`` files for crucible
syntax and C overrides, respectively. Each of these file should be named after
the function that should be overridden. For instance, ``printf.cbl`` would
correspond to an override for the ``printf`` function.

The ``overrides.yaml`` is an optional file that can be present if one desires
more fine-grained control over which functions in a binary should receive
particular overrides. The contents of an ``overrides.yaml`` file will look
like this: ::

  function address overrides:
    main.exe:
      0x123: "foo"
      0x456: "bar"
      ...
    libc.so:
      0x123: "baz"
      0x456: "quux"
      ...

  startup overrides:
  - "start1"
  - "start2"
  - ...

Here:

* ``function address overrides`` specifies an optional mapping from function
  addresses to override names. This can be useful for situations where a
  function in a binary has no corresponding symbol name (for instance, as in
  stripped binaries). A separate mapping is specified for each binary or shared
  library. The name that each address maps to must correspond the name of an
  override file in the ``function`` subdirectory (not including the file
  extension).

  Note that the mapping only cares about the file names of each binary and does
  not care about the parent directories. For example, if the verifer is invoked
  on ``/foo/bar/main.exe``, then the ``overrides.yaml`` only needs to specify
  ``main.exe``, not its full path.

* ``startup overrides`` specifies a list of overrides to run at the very start
  of simulating a binary, before the entry point (e.g., ``main``) is run. Each
  override will be run in the order it appears in the list. Each startup
  override is expected to have no arguments and return ``Unit``. Attempting to
  specify a startup override with a different type will result in an error
  before simulation begins.

  A key use case for startup overrides is for initializing the values of global
  variables, especially in conjunction with the ``get-global-pointer-addr``,
  ``get-global-pointer-named``, and ``malloc-global`` functions. This can serve
  as a more straightforward way to initialize global state than, say,
  simulating everything in ``glibc``'s ``_start`` function.

Override Precedence
-------------------

Override names that appear in ``function address overrides`` take precedence
over other overrides. To illustrate how this works, suppose a user specifies
``--overrides DIR``, where the contents of ``DIR`` are the following: ::

  DIR/
  ├── function/
  │   ├── foo.cbl
  │   └── bar.cbl
  └── overrides.yaml

Where the contents of ``overrides.yaml`` are as follows: ::

  function address overrides:
    main.exe:
      0x123: "bar"

Now suppose that the verifier encounters a function in ``main.exe`` at address
``0x123`` named ``foo``. Although there is a ``foo.cbl`` override present, the
``function address overrides`` mapping also maps the address ``0x123`` to
``bar``. In such situations, the ``function address overrides`` take higher
precedence, so the verifier will use the ``bar`` override.

Functions
---------

Each ``<name>.{cbl,c}`` file is expected to define a function named ``@<name>``.
For instance, an ``add_bvs.cbl`` file should define an ``@add_bvs`` function,
e.g.: ::

  (defun @add_bvs ((x (Bitvector 32)) (y (Bitvector 32))) (Bitvector 32)
    (start start:
      (let sum (+ x y))
      (return sum)))

An override file is also permitted to define other functions. These functions
are considered local to the file defining it and are not visible to other
files. For instance, an alternative way to implement ``add_bvs.cbl`` would
be: ::

  (defun @add_bvs ((x (Bitvector 32)) (y (Bitvector 32))) (Bitvector 32)
    (start start:
      (let res (funcall @add_bvs_2 x y))
      (return res)))

  ; Local to this file
  (defun @add_bvs_2 ((x (Bitvector 32)) (y (Bitvector 32))) (Bitvector 32)
    (start start:
      (let sum (+ x y))
      (return sum)))

An override file is allowed to invoke functions defined in other override files
by way of *forward declarations*. A forward declaration states the type of a
function that is not defined in the file itself, but will be provided later by
some other means. For instance, suppose that ``@add_bvs_2`` were defined in its
own ``.cbl`` file and that you want to invoke it from ``add_bvs.cbl``. To do
so, one must declare ``add_bv_2``'s type using a forward declaration in
``add_bvs.cbl``: ::

  (declare @add_bvs_2 ((x (Bitvector 32)) (y (Bitvector 32))) (Bitvector 32))

  (defun @add_bvs ((x (Bitvector 32)) (y (Bitvector 32))) (Bitvector 32)
    (start start:
      (let res (funcall @add_bvs_2 x y))
      (return res)))

The verifier will ensure that the invocation of ``add_bvs_2`` will be resolved
to the same function defined in ``add_bvs_2.cbl``. The verifier will raise an
error if it cannot find a function of the same name, or if it finds a function
with a different type than what is stated in the forward declaration.

Currently, forward declarations can be resolved to overrides defined in other
override files as well as overrides that are built into the verifier (e.g.,
the override for ``memcpy``). Note that forward declarations cannot be used to
resolve functions that are local to a particular override file. Resolving
forward declarations to functions defined in binaries is not currently
supported.

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
- ``pointer-read :: forall (t :: Type) -> Endianness -> Pointer -> t`` where the first argument is the type of the value to read and the second argument is ``le`` or ``be``. ``Type`` must either be ``Bitvector (8 * w)`` (for some positive number ``w``) or one of the type aliases listed above.
- ``pointer-write :: forall (t :: Type) -> Endianness -> Pointer -> t -> Unit`` where the first argument is the type of the value to read and the second argument is ``le`` or ``be``. ``Type`` must either be ``Bitvector (8 * w)`` (for some positive number ``w``) or one of the type aliases listed above.


Built-in Overrides
------------------

There are some overrides that are built-in to the verifier, as they cannot
easily be defined in terms of the primitives that the syntax override language
provides. The following overrides can be invoked from both binaries and syntax
overrides:

* ``accept :: Int -> Pointer -> Pointer -> Int``
* ``bind :: Int -> Pointer -> SizeT -> Int``
* ``calloc :: SizeT -> SizeT -> Pointer``
* ``close :: Int -> Int``
* ``connect :: Int -> Pointer -> SizeT -> Int``
* ``execve :: Pointer -> Pointer -> Pointer -> Int``
* ``exit :: Int -> Void``
* ``getppid :: PidT``
* ``listen :: Int -> Int -> Int``
* ``recv :: Int -> Pointer -> SizeT -> Int -> SizeT``
* ``malloc :: SizeT -> Pointer``
* ``memcpy :: Pointer -> Pointer -> SizeT -> Pointer``
* ``memset :: Pointer -> Int -> SizeT -> Pointer``
* ``mkdir :: Pointer -> SizeT -> Int``
* ``open :: Pointer -> Int -> SizeT -> Int``
* ``read :: Int -> Pointer -> SizeT -> SizeT``
* ``send :: Int -> Pointer -> SizeT -> Int -> SizeT``
* ``shmat :: Int -> Pointer -> Int -> Pointer``
* ``shmget :: SizeT -> SizeT -> Int -> Int``
* ``socket :: Int -> Int -> Int -> Int``
* ``read :: Int -> Pointer -> SizeT -> SizeT``
* ``write :: Int -> Pointer -> SizeT -> SizeT``

The following overrides can be invoked from both binaries and syntax overrides,
but with the limitation that they can only be invoked from syntax overrides
without any variadic arguments:

* ``sprintf :: Pointer -> Pointer -> ... -> Int``
* ``sscanf :: Pointer -> Pointer -> ... -> Int``

The following overrides can only be invoked from syntax overrides:

* ``malloc-global :: SizeT -> Pointer`` is like ``malloc``, except that it is
  explicitly meant for allocating memory for use in global variables.
* ``read-bytes :: Pointer -> Vector (Bitvector 8)`` reads a null-terminated,
  sequence of concrete bytes from the ``Pointer``. Unlike ``read-c-string``,
  this reads the raw bytes without converting to a particular text encoding.
* ``read-c-string :: Pointer -> String Unicode`` reads a null-terminated,
  UTF-8–encoded, concrete string from the ``Pointer`` and converts it to a
  ``String``. Representing it as a ``String`` can be more convenient in the
  syntax override language, as it is easier to manipulate and check for
  equality.
* ``write-bytes :: Pointer -> Vector (Bitvector 8)`` writes a sequence of
  concrete bytes to a ``Pointer``, including a null terminator. Unlike
  ``write-c-string``, this writes the raw bytes without converting to a
  particular text encoding. For example, to write the string ``"abc"``,
  supply ``(vector (bv 8 97) (bv 8 98) (bv 8 99))`` as an argument, as
  the bytes ``97``, ``98``, and ``99`` correspond to the numeric values of the
  ``a``, ``b``, and ``c`` characters, respectively.
* ``write-c-string :: Pointer -> String Unicode -> Unit`` writes a
  UTF-8–encoded, concrete string to a ``Pointer``, including a null
  terminator.

  Note that in order to write an escaped Unicode character, one must supply an
  extra backslash. For instance, to write the ``☃`` character, supply the
  string ``"\\9731"``. Note that some Unicode characters require multiple bytes
  in the UTF-8 encoding, so make sure that the ``Pointer`` has enough space
  allocated to store all of the bytes.
* ``print-pointer :: Pointer -> String Unicode`` converts a pointer to a string
  representation.  This prints the pointer as ``(block, offset)``, or simply
  ``offset`` if ``block`` is ``0``.

The following overrides can only be invoked from syntax overrides when using
the ``verify`` command, as they require interfacing with a binary. Attempting
to use any of these overrides from the ``test-overrides`` command (which
operates independently of any binary) will result in an error:

* ``get-global-pointer-addr :: String Unicode -> SizeT -> Pointer`` will return
  a pointer to a global variable, where:

  * The first argument must be a concrete string that indicates the binary in
    which the global variable is defined.
  * The second argument must be a concrete address for the global variable.

  Note that only the file names of the binary needs to be specified,
  not the full path. For example, if a global variable is located in
  ``/foo/bar/main.exe``, then the first argument should simply be ``main.exe``.
* ``get-global-pointer-named :: String Unicode -> String Unicode -> Pointer``
  will return a pointer to a global variable, where

  * The first argument must be a concrete string that indicates the binary in
    which the global variable is defined.
  * The second argument must be a concrete string that indicates the name of
    for the global variable. At present, only unversioned names are supported.

  The same caveats about full paths mentioned in ``get-global-pointer-addr``
  also apply to ``get-global-pointer-named``.

Global Variables
----------------

Overrides may declare global variables using ``defglobal`` at the top level::

  (defglobal $$varname Type)

The verifier permits global variable declarations anywhere in the top level,
including after their use sites. Global variables are scoped to the files they
are declared in. The verifier instantiates global variables as fresh symbolic
values.  To change the value of a global variable, use ``set-global!``::

  (set-global! $$varname value)

A ``.cbl`` file can also access global variables defined externally by using an
*extern*. An extern declaration states the type of a global variable that is
not defined in the file itself, but will be provided later by some other means.
(Externs are to global variables what forward declarations are to functions.)

For instance, suppose we have overrides for functions named ``f`` and ``g``,
where ``f`` defines a global variable::

  (defglobal $$f-glob Int)

  (defun @f () Unit
    (start start:
      (let val (bv-typed-literal Int 42))
      (set-global! $$f-glob val)
      (return ())))

And ``g`` accesses ``f``'s global variable::

  (extern $$f-glob Integer)

  (defun @g () Int
    (start start:
      (return $$f-glob))

Suppose that we first invoke ``f``, then ``g``. By the time that ``g`` is
invoked, the value of ``$$f-glob`` will already have been set to ``42``, so
``g`` will return ``42``.

Currently, externs can be resolved to global variables defined in other
override files. Note that the verifier will raise an error if it cannot find a
global variable of the same name, or if it finds a global variable with a
different type than what is stated in the ``extern`` declaration.  Resolving
externs to global variables defined in binaries is not currently supported.

Tests
-----

Crucible syntax files may optionally contain functions starting with ``@test_``
that use ``assert!`` to test the behavior of an override.  Under normal
operation the verifier ignores these test functions, but when run with the
``test-overrides`` subcommand the verifier will execute any test functions it
finds and report test results.  The ``test-overrides`` subcommand has two
mandatory options:

- ``--overrides`` must point to the directory containing crucible syntax
  overrides.
- ``--abi`` must be either ``X86_64Linux`` or ``AArch32Linux``.  This flag
  sets the ABI to use when interpreting crucible syntax overrides.  For
  example, using the ``X86_64Linux`` will cause the verifier to execute
  function override tests using the X86_64 ``Bitvector`` type aliases.

Entry Points
============

By default, the verifier begins simulating binaries at the ``main()`` function
rather than ``_start()``. This is because the implementations of ``_start()``
in ``glibc`` (`related issue
<https://gitlab-ext.galois.com/ambient/verifier/-/issues/22>`_) and ``musl``
(`related issue <https://gitlab-ext.galois.com/ambient/verifier/-/issues/23>`_)
often give the verifier trouble. Beginning at ``main()`` is usually an effective
workaround, but this comes at the expense of skipping initialization-related
code in ``_start()``, which may be important for certain binaries. If you are
brave start simulation at a different entry point, you can do so with the
``--entry-point-name <function-name>`` option.

Note that the verifier is only able to discover a ``main()`` function is the
binary contains the relevant function symbol. If a binary is stripped, however,
then the verifier will not be able to discover the ``main`` symbol and will
give up as a result. To work around this problem, one can manally specify the
address of the entry point function (be in ``main()`` or otherwise) with the
``--entry-point-addr <function-address>`` option.

Static and Dynamic Binaries
===========================

The verifier fully supports statically linked libraries and has partial support
for dynamically linked libraries. In order to simulate a dynamically linked
library, it is required to put all of the shared libraries into a single
directory and pass the ``--shared-objects <lib-dir>`` option to the verifier.

Be aware of the following limitations in the verifier's support for dynamically
linked libraries:

1. The verifier makes certain assumptions about the layout of PLT stubs that do
   not hold for binaries compiled with ``-fcf-protection``, which is now the
   default for many versions of GCC (e.g., the one provided on recent versions of
   Ubuntu). See `this issue
   <https://gitlab-ext.galois.com/ambient/verifier/-/issues/62>`_. To avoid any
   issues, it is recommended that you compile binaries with
   ``-fcf-protection=none``.

2. The verifier currently only supports a small number of dynamic relocations
   and will abort if it encounters a relocation that it doesn't support. See `this
   issue <https://gitlab-ext.galois.com/ambient/verifier/-/issues/93`_. If you
   encounter an unsupported relocation, please file an issue.
