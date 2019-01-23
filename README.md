# Recovery refinement

[![Build Status](https://travis-ci.org/mit-pdos/argosy.svg?branch=concur)](https://travis-ci.org/mit-pdos/argosy)

Proving crash safety of systems by proving an implementation refines a
specification. Supports implementations that run a recovery procedure, as well
as abstracting away the behavior of the recovery procedure.

## Overview

The [src](src/) subdirectory contains the Coq development. Within that directory:

* The folder [Helpers](src/Helpers) contains various useful libraries:

    * [Disk.v](src/Helpers/Disk.v) -- a model of disks as lists of blocks.
      Blocks themselves are treated as an abstract type, with a few properties
      axiomatized -- during extraction, they are mapped to Haskell ByteStrings.

    * [RelationAlgebra.v](src/Helpers/RelationAlgebra.v) -- defines relational
      combinators and proves their basic properties.

    * [RelationRewriting.v](src/Helpers/RelationRewriting.v) -- provides tactics
      to normalize and rewrite by equational/inequational laws for relations.

* The folder [Spec](src/Spec) contains files for the semantics of programs and
  reasoning about them.

    * [Proc.v](src/Spec/Proc.v) -- definition of the syntax and semantics of
      programs as free monads generated by set of basic operations.

    * [Layer.v](src/Spec/Layer.v) -- defines layers, which define an "API" as a
      bundle of operations and a form of state. Also describes how to implement a
      layer in terms of another, compilation between layers, and the notion of
      layer refinement (which we also call "recovery refinement"). The theorem
      `compile_exec_seq_ok` proves that layer refinements preserve the semantics
      of complete interactions. `refinement_transitive` composes two
      implementations and shows the composition is also a recovery refinement.

    * [Hoare.v](src/Spec/Hoare.v) -- our embedding of Crash Hoare Logic (CHL),
      which we use to help prove that an implementation is a layer refinement.

* The folder [Examples](src/Examples) contains examples of using the framework to prove
  recovery refinement.

    * [ReplicatedDisk](src/Examples/ReplicatedDisk) -- contains an example
      proving that a disk replication implementation is a recovery refinement
      from a layer with a single robust disk, into a layer with two faulty
      disks. [OneDiskAPI.v](src/Examples/ReplicatedDisk/OneDiskAPI.v) and
      [TwoDiskAPI.v](src/Examples/ReplicatedDisk/TwoDiskAPI.v) define the source
      and target layers, while
      [ReplicatedDiskImpl.v](src/Examples/ReplicatedDisk/ReplicatedDiskImpl.v)
      is the implementation and proof that it is a refinement.

    * [Logging](src/Examples/Logging) -- contains an example proving that a
      write-ahead logging implementation is a recovery refinement from a
      transactional disk layer into a layer with one disk.

        * [TxnDiskAPI.v](src/Examples/Logging/TxnDiskAPI.v) defines the
          transactional layer.

        * [Impl.v](src/Examples/Logging/Impl.v) is the
          write-ahead logging code.

        * [HoareProof.v](src/Examples/Logging/Impl.v) is
          the proof of recovery refinement.

        * [ComposedRefinement.v](src/Examples/Logging/ComposedRefinement.v)
          composes the refinement proof with the replicated disk example to
          obtain a refinement from the transactional disk to the two disks.

The [vendor](vendor/) subdirectory contains various submodules for Coq libraries
that we use in the development. See the README files within each submodule for
documentation.

The [logging-client](logging-client/) subdirectory contains code to extract and
run the composed logging and replication implementation, which provides a
transactional API on top of two unreliable disks. See its separate
[README.md](logging-client/README.md) for details.

## Compiling

We develop Argosy using Coq master. It should be compatible with Coq v8.9+beta
and Coq v8.8.2, which are tested as part of continuous integration.

This project uses git submodules to include several dependencies. If building
from a packaged release, these dependencies should be included. Otherwise, you
can either use `git clone --recurse-submodules` or (after cloning) `git
submodule update --init --recursive` to set that up.

To compile just run `make` with Coq on your `$PATH`.

Details on extraction for the logging example are in its own
[README.md](logging-client/README.md).
