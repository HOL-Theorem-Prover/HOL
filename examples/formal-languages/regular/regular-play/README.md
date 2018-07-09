<!-- https://github.com/adam-p/markdown-here/wiki/Markdown-Cheatsheet -->

# ITP2017 project - A verified regular expression library

This is an SML library for regular expression matching. Its three implementations are verified in the HOL4 theorem prover and exported to SML using HOL's EmitML. Furthermore, unified wrappers for each of the implementations, including a reference which is part of the HOL4 source code, are provided. The three implementations use a straight forward functional implementation, an implementation with position marking, and an implementation with position marking and property caching respectively.

We implemented the three regular expression implementations proposed in the beginning of the following work ([link](http://dl.acm.org/citation.cfm?id=1863594)):<br />
Fischer, Sebastian, Frank Huch, and Thomas Wilke. "A play on regular expressions: functional pearl." ACM Sigplan Notices. Vol. 45. No. 9. ACM, 2010.

An extendable test and benchmark library is used for conformance testing in the typical HOL4 selftest style. Both, test and benchmark can be started individually by using the corresponding test and benchmark suite scripts after compilation.


## Authors and credits

This is the project work of Andreas and Marcus Lindner in the ITP course, which was given in spring 2017 at KTH, Stockholm. We want to credit Thomas Tuerk for his help and comments during the course and this project. Furthermore, we provide the sources of further inspirations in the code in form of links in comments.

The course slides can be found under the [documentation section](https://hol-theorem-prover.org/#doc) of the HOL web page and is linked [here](https://hol-theorem-prover.org/hol-exercises.tar.gz).


## Limitations

The regular expression data structure only allows epsilon, a symbol of type α, an alternative operator, a sequence operator, and a repetition operator.


## How to compile

<!-- 1. Clone the repository using `git clone https://gitr.sys.kth.se/lindnera/itp2017-regexproj.git`. -->
1. Compile the example by:
  * running `Holmake` in this directory, or
  * build HOL using selftest level 2 by using `bin/build -t2` (HOL's `tools/build-sequence` file guides the build process here as usual).
1. Run a selftest using `./selftest.exe` to check for conformance of the emitted code with respect to the reference library.
1. Run a performance test by running `hol < test/performance.sml > test/performance.log` in the project root directory.


## Directory and file structure

* `src`  - Contains the HOL4 theory sources and the HOL4 to ML emit script.
* `emit` - Appears after compiling `src`, then contains the emitted libraries.
* `lib`  - Contains the wrapper libraries around the emitted code and the HOL4 `regexpMatch` module. Uses `emit`.
* `test` - Contains the test case library and the benchmark script. Uses the wrapper libraries in `lib`.
* `selftest.sml` - HOL4 style selftest script. Runs conformance tests on the emitted code. Uses the wrapper libraries in `lib` and the test cases in `test`.


## Performance results

The results of the performance runs are written to the file `test/performance.log`. The small test suite is run on all regex implementations first, and depending on the flag `runPerformanceTests` in `test/performance.sml`, the performance test cases are run afterwards as well.

The test suite results on the four implementations `_ref`, `_exec`, `_exec_marked`, and `_exec_mark_cache` are listed as the booleans `res1`, `res2`, `res3`, and `res4` respectively in `test/performance.log`.

The performance test cases are purely artificial and consist of two regular expressions, which are matched against a random sequence. `test/data` contains the script to generate test data and a pregenerated set. `test/regexTest.sml` contains the test suite and the regular expressions for the performance tests. `test/performance.sml` is the orchestration script that launches the tests and `test/test_regexScript.sml` launches them from `Holmake`.


## Performance evaluation

For the simple test suite, runtime of the four implementations is not big enough to say anything. For slightly larger input string lengths (about 20 characters) and two different simple regular expressions (performance suite with a short regular expression), the implementation `_exec` drops down to 0.66s on a simple desktop PC while the others are still way below 0.001s.

With the same regular expression performance suite and an input size of about 100000 characters, the reference SML implementation `_ref` is still not in a measurable range, while the code from emitML using marking and caching takes around 2s. The code that implements caching (2.2s) is even slower than the code that does not implement this (2.1s). This is most likely due to the chosen regular expression and input data.

When we increase the size of the regular expression that we feed into the implementations, the two implementations using marking and caching outperform the reference implementation. When providing an input string of length 10000 and a regex sequence of 600 characters, the reference implementation takes 13.2s while both implementations using marked expression and also caching use around 0.4s. When we increase the input to a 100000 character string and a regex which is a 10000 character sequence, it takes 53.4s and 44.6s for marked and cached expression matching respectively.



