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
As of 2022, there are no regression tests that require a level greater than 3,and we will likely keep things this way.

[^selftestnote]: As of 2022, our automatic testing infrastructure runs one selftest at level 3 each day, and one at level 2, with the latter testing the experimental kernel. Yes, this means that things only in level 3 are not getting tested for the experimental kernel.

There are two standard ways to the install a test that can be run by `build`:

1.  Create a `selftest.exe` executable in an existing directory that build works on.
    The `Holmakefile` in this directory will need to specify how to build this executable, and then additionally include an

         ifdef HOLSELFTESTLEVEL
         endif

    block to get the executable to be run.  Just checking if the variable is set, will cause execution at all non-zero levels. To fire a test only at particular levels, use the `ifeq` and related commands. It may also be a good idea to have this block produce a log-file recording the execution of the selftest; this can be done effectively with the `Holmake` function `$(tee ...)`.

    There are a number of examples of constructing `selftest.exe` executables in the sources.
    See for example `src/boss/selftest.sml` and `src/boss/Holmakefile`.
    Though the `Holmakefile` gives build commands in terms of `$(HOLMOSMLC)`, the `selftest.exe` executable will also be built correctly if running Poly/ML.

2.  Create a new directory for build to operate on.
    This directory can be inserted into the early stages of the build sequence, as explained in the documentation at the head of `tools/build-sequence`.
    If the testing happens after `bossLib` and (in Poly/ML) the creation of the standard `hol.state` heap, the directory should be included in the `Holmakefile` in `src/parallel_builds/core`.
    The various tests in that file can be used to insert regression test directories into the big parallel build of all the post-`bossLib` directories.
    Using a test-directory is necessary if the tests need to examine behaviours to do with theory export and loading.

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

Past the initial prefix of this process, most directories in the build sequence are actually listed in the `Holmakefile` in `src/parallel_builds/core`.
This arrangement allows parallel processing of lots of directories at once.
The sequence file `upto-parallel` gives the sequence of build targets up this point, so is a reasonable argument to `--seq` for tests of the core system.

## Rebuilding

It is often possible to repeat `build` to get the system to rebuild itself in the face of changed source files.
If source files have moved directories, or disappeared entirely, `build` (more accurately `Holmake` when `build` calls it) may get confused by stale dependency information.
In this situation, cleaning everything first with `build cleanall` may be necessary.

# Things in `bin`

The build process deposits various tools in the `bin` directory.
Under both Moscow&nbsp;ML and Poly/ML the following are created:

`build`
: the build tool as above

`hol`
: the standard executable, which loads a `bossLib` based logical context. This is designed for use by “every user”.

`hol.bare`
: the “bare” executable, which includes `boolLib` and the goalstack infrastructure but no theories past `bool`.

`Holmake`
: the Holmake tool, again designed for every user.

`mkmunge.exe`
: This tool creates LaTeX mungers, as described in the *DESCRIPTION* manual.

`unquote`
: This is the quotation filter embodied as a Unix filter, with a variety of options to specify behaviour. Note that this is not used by Poly/ML HOL, but can be useful there to see what the filter (as embodied by the `QFRead` module) is doing when it messes with user input.

Under Poly/ML, the following additional files will appear:

`buildheap`
:   this is the core execution engine of all Poly/ML HOL (but not `Holmake` or `build`). It will appear as the process name for HOL executions when working interactively, or when scripts are run to generate a theory file. It embodies the quotation handling by implementing a copy of the standard Poly/ML REPL that fiddles with the lexer.

`genscriptdep`
:   Given a filename, this utility executable will generate a list of a script files dependencies.

`heapname`
:   this little executable reads the startup directory’s `Holmakefile` (if present) to determine which heap should be used as the basis for interactive execution in this directory.  It is called by `hol`, but *not* `hol.bare`.

    `Holmake` reads `Holmakefile`s for `HOLHEAP` information for every invocation, so interactive execution of HOL in directories such as `src/pred_set/src` and `src/list/src` will have to use `hol.bare` (these are before bossLib), and will not get to use the `numheap` executable created in `src/num/termination`, even though non-interactive builds do get that benefit.

`hol.state`
:   the Poly/ML heap used by `hol` by default. This embodies `bossLib` and is created in `src/boss`.

`hol.state0`
:   the Poly/ML heap used by `hol.bare`. This is built in `src/proofman`.

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

`mlyacc`
:   The tool from SML/NJ.

`quote-filter`
:   The quotation filter that runs over sources before they are seen by SML implementations.
    This is used interactively (*via* a Unix filter that preprocesses all user-input under Moscow ML, or built into the Poly/ML REPL), and non-interactively (by being applied to source files).

`unicode-grep`
:   Our tool for enforcing code style ([as documented below](#coding-standardsrequirements)).
    The command-line specifies the directories to scan, and options dictate which requirements are enforced/checked for.

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

## Coding Standards/Requirements

We are fairly liberal in the style of code we accept, which is almost required given the long history of our sources (see `arithmeticScript.sml` for lots of old comments).
However, the regression machinery does enforce some coding requirements, and these requirements may tighten over time.
As of September 2024, the requirements are:

-   No use of Unicode characters under `src/` except for Greek lambda (`U+03BB`), and four quotation marks (“ ” ‘ ’—`U+2018`, `U+2019`, `U+201C` and `U+201D`).
    Use of all five exceptions is _encouraged_.
    In some situations, _e.g._, in a comment, it is extremely useful to be able to use Unicode characters.
    If this is required, the line on which this occurs can be exempted by having that line include the substring `UOK` (typically inside an SML comment).
    All Unicode is accepted under `examples`.

-   No use of TABs anywhere.

-   No trailing whitespace.

We encourage developers to keep their lines under 80 columns in width.


<!-- # Appropriate Idioms  -->

# Glossary of common abbreviations in the source code

These appear with either capitalisation.
There is a slight tendency to having all upper-case SML identifiers refer to theorems, or functions that returns theorems.

`abs`
:   Abstraction.

`ant`
:   Antecedent of an implication.

`asm`
:   Assumptions of a theorem or goal.

`conseq`
:   Consequent of an implication.

`_conv`
:   Optional suffix to indicate a conversion. Useful to distinguish between a conversion, tactic and derived inference rule that perform the same basic function.

`dest_`
:   “destroy”, i.e.: decompose an object into simpler constituents.

`g`
:   Goal of a tactic.

`gen_`
:   As a prefix of functions indicates that this function is the more general version of the function without the prefix.

`ho`
:   “higher-order”, as opposed to first-order. Typically in the context of term matching.

`l`
:   - A list.
:   - Suffix for a variant of a function whose difference is that it operates on a list instead of a single element. E.g: the tactical `THENL` compared to `THEN`.

`lhs`
:   Left-hand side of an equation.

`mk_`
:   “make”, i.e.: create an object from simpler constituents.

`prim_`
:   “primitive”. Optional prefix for the name of internal functions that contain most of the implementation. The function without the prefix is a thin wrapper that implements the public interface.

`q_` or just `q`
:   Optional prefix in the name of a tactical to indicates that it takes a term quotation which is parsed in the context of the goal. Example: `qabbrev_tac`.

`rand`
:   Ope*rand* of a combination.

`rator`
:   Ope*rator* of a combination.

`rhs`
:   Right-hand side of an equation.

`_rule`
:   Optional suffix to indicate a derived inference rule. Often used for a variant of a conversion that applies the conversion to the conclusion of a theorem. See `CONV_RULE`.

`t`
:   A term.

`_tac`
:   Optional suffix for tactics or tacticals.

`th`
:   A theorem.

`_then`
:   Optional suffix for theorem-tacticals. See the section on tactics in the HOL description manual.

`thm`
:   A theorem.

`x_`
:   * Optional prefix to indicate a variant that takes a term or quotation. E.g.: The tactical `X_GEN_TAC` compared to `GEN_TAC`.
:   * In a tactical that takes a theorem-tactic and applies it to assumptions, indicates a variant that removes the assumption which was acted on.

<!--  LocalWords:  executables mosmlc sml categorise
 -->
<!--
Local variables:
compile-command: "Holmake"
End:
-->
