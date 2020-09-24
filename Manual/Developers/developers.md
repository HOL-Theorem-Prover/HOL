---
title: HOL Developers’ Manual
author: HOL4 Developers
numbersections: yes
---

# Introduction

This manual attempts to provide documentation for people wishing to develop HOL4, a process that will likely involve frequent re-compilations or rebuilds of the core sources.

As *per* [the standard installation instructions](http://hol-theorem-prover.org/#get), once one has an SML installation, there are two stages to the process of building HOL4:

1.  The first step is the *configuration* of the system (see [Configuration](#configuration) below).
    This is achieved with the command

           smlsystem < tools/smart-configure.sml

    where `smlsystem` is either `poly` or `mosml`.
    This command must be issued from the root of the HOL installation, where the path `tools/smart-configure.sml` makes sense.
    This should complete quickly.

2.  Second, one needs to *build* the system (see [Build](#build) below).
    This is achieved with the command

           bin/build

    assuming one is still in the root HOL directory.
    Note however, that `build` can be executed from anywhere.
    In particular, if `<holdir>/bin` is in one’s path, it is reasonable to run `build` from any directory.

    When first executed, the build process will take a while because it proves all of the theorems in the core system, writing theories to disk as it goes.
    Building should terminate with the message

           Hol built successfully.

    Repeated calls to `build` should complete quickly: theorem-proving work will not be redone unnecessarily.
    The building of the theory graph can be slow however, and this *does* happen with every invocation of `build` by default.
    To avoid this use `build`’s `--nograph` option.

# Configuration

The configuration process is responsible for

* calculating important environmental details, such as the SML implementation, the nature of the operating system, and important paths;
* the creation of core system tools: standard SML tools (`mlyacc`, `mllex`), and HOL-specific tools (most importantly, the quotation filter, `Holmake` and `build`).

The first thing that configuration does is to figure out which SML implementation is being run.
This is important because the compilation and creation of executables differs so dramatically in Poly/ML and Moscow\ ML.
Once this determination is made, actual configuration work is done in either `tools-poly/configure.sml` or `tools/configure.sml`
(See [Sources](#sources) below for more on how these sources are organised.)

## Building `Holmake`

Because `Holmake` is not assumed to exist when `Holmake` is built, the configuration script is responsible for assembling the constituent sources.
In the case of Moscow\ ML, this means that it makes the successive calls to `mosmlc` as necessary.
With Poly/ML, the work is orchestrated by `tools-poly/Holmake/poly-Holmake.ML`.
That script is a sequence of calls to `use`, followed by the boilerplate necessary to create an object-code file.
The configuration script then calls the C compiler to link that object code into the final executable.

Note that we can’t simplify the Moscow\ ML build in a way analogous to what happens with Poly/ML because the complicated sequence of instructions are command-line invocations of `mosmlc`, rather than calls to `use` within a Poly/ML program.
We might attempt to create a shell-script containing the calls to `mosmlc`, but it seems more OS-independent to invoke `OS.Process.system` from within `configure.sml`.

# Build

The standard options to build are described in its help documentation, which is accessible by invoking `build --help` (or `build -h`, or `build -?`, but not `build help` because this builds the HOL documentation).
The file containing this information about options is located at `tools/buildhelp.txt`.

The most frequently used options to build are those to do with “selftest” level, and the selection of kernel.

## Regression Testing

The build program’s `--selftest` option can be given as is (in which case the selftest level is 1), or followed by a positive number, which gives the selftest level explicitly.
The higher the number, the more regression tests are executed.
Developers are expected to categorise their tests so that those at level 1 will complete quickly, those at level 2 will execute in moderate time, and those at level 3 can take as long as is necessary.[^selftestnote]
As this document is written (late 2015), there are no regression tests that require a level greater than 3.

[^selftestnote]: As of 2015, our automatic testing infrastructure runs selftest level 1 tests 6 times each day, and level 3 tests twice daily.

There are two standard ways to the install a test that can be run by `build`:

1.  Create a `selftest.exe` executable in an existing directory that build works on.
    This executable will be run if `build`’s selftest level is non-zero, and will be passed the level as the executable’s one and only command-line argument.
    (The `selftest.exe` can thus choose to do nothing if the level is too low, or to do more if the level is higher.)

    There are a number of examples of constructing `selftest.exe` executables in the sources.
    See for example `src/boss/selftest.sml` and `src/boss/Holmakefile`.
    Though the `Holmakefile` gives build commands in terms of `$(HOLMOSMLC)`, the `selftest.exe` executable will also be built correctly if running Poly/ML.

2.  Extend the build sequence with a new directory for build to operate on.
    As explained in the documentation at the head of `tools/build-sequence`, the name of this directory should be preceded by as many exclamation mark characters\ (`!`) as its desired selftest level.
    Using this approach is necessary if the tests need to examine behaviours to do with theory export and loading.

## Kernel Selection

There are currently three kernels that can be built to underlie a HOL installation.
The *standard kernel* uses a de\ Bruijn representation for terms, with bound variables represented as numbers.
Free variables are represented as a pair of name and type.
This kernel also implements explicit substitutions internally, allowing for efficient call-by-value execution with tools such as `EVAL`.
This kernel is the default choice, and can be explicitly selected by passing the `--stdknl` option to `build`.

The *experimental kernel* uses name-type pairs for all sorts of variables.
This means that the functions `mk_abs` and `dest_abs` operate in constant time.
(In the standard kernel, these functions must switch between de\ Bruijn indices and free variables in the body when called, making them run in time linear in the size of the body.)
The experimental kernel can be selected by passing the `--expk` option to `build`.

The *OpenTheory kernel* is based on the experimental kernel, but adds proof-logging to the primitive inference rules so that OpenTheory theory packages can be exported from HOL.
This kernel can be selected by passing the `--otknl` option to `build`.

## Build Sequences

When `build` runs, it choreographs its calls to `Holmake` by referring to a specified sequence of directories.
By default this sequence is that specified in the file `tools/build-sequence`, which in turn refers to other files *via* `#include` directives.
It is possible to provide a different sequence by using the `--seq` commandline option to `build`.
Such sequences can be constructed more easily by referring to sequence fragments in the `tools/sequences` directory, and including these with `#include` commands.
The details of the required format for sequence files is spelled out in a comment at the head of the `tools/build-sequence` file.

# Sources and Their Organisation {#sources}

HOL comes with two `tools` directories, `tools` and `tools-poly`, as well as a `developers` directory.
The `tools-poly` directory is for sources that are specific to the Poly/ML implementation.
The `tools` directory is for general sources, and for sources specific to the Moscow\ ML implementation.
Apart from sources for tools that are genuine command-line executables, the `tools` directory also includes some configuration files and editor “modes”.

## Tool Executables

The tools distributed with HOL are described below.
Unless otherwise noted, they are built by the configuration process.

`build`
:   Described [above](#build).
    The top-level driver code is in files called `build.sml` in `tools` and `tools-poly`.
    Shared code is in `tools/buildutils.sml`.

`cmp`
:   A simple-minded tool for comparing two files, returning (*via* exit code) 0 (success) if the two command-line arguments are byte-for-byte identical.
    Useful in regression testing of other tools.
    Built on demand *via* a Holmakefile.

`Holmake`
:   The user-facing tool for building HOL developments.
    Use of this tool is described in the Description manual.
    The `tools/Holmake` directory contains almost all of the sources, but the Poly/ML-specific implementation of the `Systeml` module (on top of which everything else in the system is built) is in `tools-poly/Holmake`.
    The Poly/ML specific code implementing concurrent `Holmake` is in `tools/Holmake/poly`.

`mllex`
:   The tool from SML/NJ.

`mllyacc`
:   The tool from SML/NJ.

`quote-filter`
:   The quotation filter that runs over sources before they are seen by SML implementations.
    This is used interactively (*via* a Unix filter that preprocesses all user-input), and non-interactively (by being applied to source files).

## Other Tools Directories

`tools/build-logs` and `tools-poly/build-logs`
:   As each build proceeds, log files recording execution times *per* theory are generated and stored in these directories.

`tools-poly/poly`
:   Implementations of `Binarymap`, `Binaryset`, `Listsort` and `Help` (from the Moscow\ ML library) so that these libraries can be used in Poly/ML.
    These implementations are all `use`-d in `poly-init.ML`.
    That file also provides an implementation of a structure called `Mosml`, which provides a simple way of calling a shell command-line and getting back the string of that command’s output.

    In `poly-init2.ML`, there is a definition of `load`, which implements the functionality that automatically loads “object code” and dependencies into running sessions.
    The `poly-init2.ML` file also `use`-s `poly-init.ML`.
    Calls are made to `use "poly-init2.ML"` in the construction of the first HOL heap (`hol.state0`), and in the scripts generated by `Holmake` run before that heap is built.
    These calls ensure that `load` is available to interactive and non-interactive uses thereafter.

    The module `holpathdb` implements a very simple mapping from “environment variables” to paths.
    These environment variables are used by `load` to let “object files” list dependencies without having to use absolute paths.
    This file is `use`-d in, and so made available by, `poly-init.ML`.
    Subsequently, there needs to be a call made to initialise the database with an entry for the `HOLDIR` key.
    This is done in `Holmake` within `poly/BuildCommand.sml`, and also within `poly-init2.ML` (for interactive use).

`tools/sequences`
:   Build sequence files.
    These are “modularised” so that, in principle, custom build sequences can be constructed more easily.

`tools/vim`
:   Implementation of the vim editor mode.


<!-- # Appropriate Idioms  -->



<!--  LocalWords:  executables mosmlc sml categorise
 -->
