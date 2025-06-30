# RegressionTests - CI for Tamarin Prover

RegressionTests is a script that runs tests for Tamarin either locally or on [Travis](https://travis-ci.com/github/tamarin-prover/tamarin-prover). 



## Usage

Basic usage is to execute the script without any arguments. To do so, go to the directory root:

```bash
$ cd tamarin-prover
```

and type:

```bash
$ python3 regressionTests.py
```



## What does the script do?

- it calls `stack install` (prevented by `-noi`)
- it calls `make case-studies` (prevented by `-nom`) with the options
  - `-j` for parallel execution
  - `fast-case-studies FAST=y` if not `-s` (slow) is given
- for each `.spthy` in the folder `case-studies`
  - it searches for the equivalent in `case-studies-regression` (or another folder specified by `-d`)
  - it parses the steps and times for both files
  - it assures that the files have the same amount of lemmas and they have the same outcome (verified vs. trace-found)
- it outputs the comparison of steps and times depending on the level of verbosity `-v`
- it repeats running the regression tests `-r` times to provide more confidence in time measurements
- it returns `1` if some result/stepcount/file missmatches or other major problems happen

Warning:
- The make command with can take more than an hour to run, consider `-j` if you run on a server with many cores
- The tool does not show any differences in the proofs if the step count didn't change



## Arguments

Here is the output of `python3 regressionTest.py -h`:

```
usage: regressionTests.py [-h] [-s] [-noi] [-nom] [-j JOBS] [-d DIRECTORY]
                          [-r REPEAT] [-v VERBOSE]

optional arguments:
  -h, --help            show this help message and exit
  -s, --slow            Run all (not only fast) tests
  -noi, --no-install    Do not call 'stack install' before starting the tests
  -nom, --no-make       Do not run regression tests, i.e., do not call 'make case-studies'
  -j JOBS, --jobs JOBS  The amount of Tamarin instances used simultaneously. Each Tamarin instance should have 3 threads and 16GB RAM available
  -d DIRECTORY, --directory DIRECTORY
                        The directory to compare the test results with. The default is case-studies-regression
  -r REPEAT, --repeat REPEAT
                        Repeat everything r times (except for 'stack install'). This gives more confidence in time measurements
  -v VERBOSE, --verbose VERBOSE
                        Level of verbosity, values are from 0 to 5. Default is 2
                        0: show only critical error output and changes of verified vs. trace found
                        1: show summary of time and step differences
                        2: show step differences for changed lemmas
                        3: show time differences for all lemmas
                        4: show shell command output
                        5: show diff output if the corresponding proofs changed
```



## Adding new files to test

To add new files to test, you have to put a reference file in the `case-studies-regression` directory. This reference file **must** **be** an output of a make command.

If you want to add it in fast-tests (and so in Travis), you need to add a Target in the Makefile after `fast-case-studies` and to add the reference file in the `case-studies-regression/fast-tests` subdirectory. The CI offers the for download in the action "Store case-studies as artifacts".



## Travis

To execute this script on Travis, you should think about two things:

- Create all directories and subdirectories in `case-studies` in the `before_install` part of your file `.travis.yml`. Something like this: `  - mkdir -p case-studies case-studies/ake ...`
- Add the following command in the script part: `python3 regressionTests.py -noi`



## Makefile

The Makefile is also important. To make the `fast-case-studies` (used in the script with the fast tests), you should use the command `make fast-case-studies FAST=y`. If you don't precise `FAST=y`, the files will be in the directory `case-studies` and not `case-studies/fast-tests` and the script won't work.





## Contact

For any problem, please contact Philip Lukert.
