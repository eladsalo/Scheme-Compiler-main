# Scheme Compiler

The compiler above is a OCaml based compiler, written as part of my Compiler Construction academic course.


## Usage

We will run your compiler on files written in Scheme code. For example, foo.scm will be the given file to compile.
First, run the following command from the project's root

```bash
  testfile=foo; \
  echo testfile = $testfile; \
  make -f ./compiler/Makefile $testfile; \
  expected_file=$([ -f $testfile.expected ] && echo $testfile.expected || echo $testfile.scm); \
  echo expected_file = $expected_file; \
  o1=`scheme -q < $expected_file`; \
  o2=`./$testfile`; \
  echo "(equal? '($o1) '($o2))" > test.scm; \
  scheme -q < test.scm
```
Then run the next command

```bash
 tests/test_compiler.sh foo
```
# Scheme-Compiler-main
