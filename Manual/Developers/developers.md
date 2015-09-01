---
title: HOL Developers’ Manual
author: HOL4 Developers
numbersections: yes
---

# Introduction

This manual attempts to provide documentation for people wishing to develop HOL4, a process that will likely involve frequent re-compilations or rebuilds of the core sources.

As *per* [the standard installation instructions](http://hol-theorem-prover.org/InstallKananaskis.html), once one has an SML installation, there are two stages to the process of building HOL4:

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

The standard options to build are described in its help documentation, which is accessible by invoking `build –help` (but not `build help` because this builds the HOL documentation).
The file containing this information about options is located at `tools/buildhelp.txt`.

The most frequently used options to build are those to do with “selftest” level, and the selection of kernel.

## Regression Testing

The build program’s `-selftest` option can be given as is (in which case the selftest level is 1), or followed by a positive number, which gives the selftest level explicitly.
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



# Sources and Their Organisation {#sources}

# Appropriate Idioms



<!--  LocalWords:  executables mosmlc sml categorise
 -->
