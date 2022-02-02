#!/usr/bin/python3

from distutils.spawn import find_executable
import re
import argparse
import subprocess
import os
import itertools
import sys
import subprocess
import shutil

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

# Timeout for the jobs in seconds
JOB_TIMEOUT = 5

# Tamarins heustics
HEURISTICS = [ 's', 'S', 'c', 'C', 'i', 'I' ]
DEEPSEC = "deepsec"
SPTHY = "spthy"
PROVERIF = "proverif"
TAMARIN_COMMAND = "tamarin-prover-proverif-output"
PROVERIF_COMMAND = "proverif"
DEEPSEC_COMMAND = "deepsec"
TIME_COMMAND = '/usr/bin/time'
PROOF = "proof"
COUNTEREXAMPLE = 'counterexample'
INCONCLUSIVE = 'inconclusive'
NOT_STARTED = 'not_started'
STARTED = 'started'
FINISHED = 'finished'
TIMEOUT = 'timeout'
ERROR = 'error'
PARSE_ERROR = "parse_error"

# Colors
GREEN = '\033[92m'
WARNING = '\033[93m'
FAIL = '\033[91m'
ENDC = '\033[0m'

# These job classes only exists to dynamically decide how we execute a job
# The arguments are fixed in the 'generate_tamarin/non_tamarin_jobs' functions
class Job():
    def __init__(self, arguments, lemma):
        # Arguments to execute the job
        self.arguments = arguments
        # Lemmas the proofs
        # For a Deepsec/ProVerif job, this will be a singleton list
        self.lemma = lemma
        # A dict mapping lemma names to results
        # Results are a tuple (status, time)
        # i.e. (proof, 1second) or (counterexample, 34seconds)
        self.results = dict()
        # returncode of job
        self.returncode = 0
        # Status of the job
        self.status = NOT_STARTED

    def __str__(self):
        return str(self.arguments)

    def __repr__(self):
        return str(self)

    def execute(self):
        self.status = STARTED
        call =  str(self)
        print("Executing " + call + "\n")
        try:
            finishedjob = subprocess.run([TIME_COMMAND] + self.arguments,
                                    capture_output=True,
                                    universal_newlines=True,
                                    timeout=JOB_TIMEOUT)
            if finishedjob.returncode != 0:
                # Check if job completed correctly
                # Save returncode to later report it
                self.returncode = finishedjob.returncode
                self.status = ERROR
                return
            # Get the results
            self.parse_results(finishedjob)
            if self.status == PARSE_ERROR:
                return

            self.status = FINISHED
        except subprocess.TimeoutExpired:
            self.status = TIMEOUT

class TamarinJob(Job):

    def parse_results(self, finishedjob):
        # Parse the results for the self.lemma from the output
        # and save them in self.results
        # If no lemmas was specified, we assume that there is
        # only one lemma in a .spthy file
        # Search for the time Tamarin took
        time = get_elapsed_time(finishedjob.stderr)
        stdout = finishedjob.stdout
        basepattern = self.lemma + " .*: "
        verpattern = re.compile(basepattern + "verified")
        falsepattern =  re.compile(basepattern + "falsified")
        incpattern = re.compile(basepattern + "analysis incomplete")
        result = ""
        if verpattern.search(stdout):
            result = PROOF
        elif falsepattern.search(stdout):
            result = COUNTEREXAMPLE
        elif incpattern.search(stdout):
            result = INCONCLUSIVE
        else:
            self.status = PARSE_ERROR
            return

        self.results[self.lemma] = (result, time)


class ProverifJob(Job):

    def parse_results(self, finishedjob):
        # Parse the results for the self.lemma from the output
        # and save them in self.results
        # We assume that there is only one query in a .pv file
        # Search for the time ProVerif took
        time = get_elapsed_time(finishedjob.stderr)
        # Search for the result in ProVerif stdout
        stdout = finishedjob.stdout
        result = ""
        if re.search(r"RESULT .* is true", stdout):
            result = PROOF
        elif re.search(r"RESULT .* is false", stdout):
            result = COUNTEREXAMPLE
        elif re.search(r"RESULT .* cannot be proved", stdout):
            result = INCONCLUSIVE
        else:
            self.status = PARSE_ERROR
            return
        # Update dict
        self.results[self.lemma] = (result, time)

class DeepsecJob(Job):

    def parse_results(self, finishedjob):
        # Parse the results for the self.lemma from the output
        # and save them in self.results
        # We assume that there is only one query in a .dps file
        # Search for the time Deepsec took
        time = get_elapsed_time(finishedjob.stderr)
        stdout = finishedjob.stdout
        result = ""
        if re.search(r"not session equivalent", stdout):
            result = COUNTEREXAMPLE
        elif re.search(r"session equivalent", stdout):
            result = PROOF
        else:
            self.status = PARSE_ERROR
            return

        self.results[self.lemma] = (result, time)



# Dict mapping tool to file type
TOOL_TO_FILE_TYPE = { SPTHY: ".spthy", PROVERIF: ".pv", DEEPSEC: ".dps" }
TOOL_TO_JOB_CLASS = { SPTHY: TamarinJob, PROVERIF: ProverifJob,
                      DEEPSEC: DeepsecJob }

def add_double_dashes_to_arguments(cliarguments):
    return [['--' + argument for argument in argumentlist] for argumentlist \
           in cliarguments ]

def add_dashes_to_arguments(cliarguments):
    return [['-' + argument for argument in argumentlist] for argumentlist \
           in cliarguments ]

def get_elapsed_time(stderr):
    match = re.search(r'(\d+:\d+\.\d+)elapsed', stderr)
    return match.group(1)

def report_results(results):
    for lemma in results:
        call = results[lemma][1]
        outcome = results[lemma][0][0]
        time = results[lemma][0][1]
        lemmastring = " for " + lemma if lemma else ""
        color = GREEN if outcome == PROOF else \
                (FAIL if outcome == COUNTEREXAMPLE else INCONCLUSIVE)
        print("=" * 80)
        print("Reporting results" + lemmastring + ":\n")
        print(" ".join(call) + " finished in " + time + " seconds\n")
        print("Result: " +  color + outcome + ENDC + '\n')

def collect_results(joblist):
    results = dict()
    for joblist in jobs:
        for job in joblist:
            # String for error reporting
            call = " ".join(job.arguments)
            # Make sure every job ran
            assert job.status == FINISHED or job.status == TIMEOUT or \
                   job.status == ERROR or job.status == PARSE_ERROR
            if job.returncode != 0:
                eprint(FAIL + "ERROR: " + ENDC + \
                       "'" + call + "'" + " returned returncode " + \
                       str(job.returncode))
                continue
            if job.status == TIMEOUT:
                eprint(WARNING + "WARNING: " + ENDC + \
                       "'" + call + "'" + " timed out after " + \
                       str(JOB_TIMEOUT) + " seconds")
                continue
            if job.status == PARSE_ERROR:
                eprint(FAIL + "ERROR: " + ENDC + "The result from "\
                       "'" + call + "'" + " could not be parsed.")
                continue
            # Job finished with zero returncode
            for lemma, (result, time) in job.results.items():
                if lemma not in results:
                    # New entry
                    results[lemma] = (result, time), job.arguments
                else:
                    (oldresult, oldtime), oldjob = results[lemma]
                    if oldresult != result:
                        # the old result is different from the new result
                        # i.e. the tool(s) disagree. Tamarin proofs. Pv gives ce.
                        oldcall = " ".join(oldjob)
                        eprint(FAIL + "ERROR: " + ENDC + "'" + oldcall + "'" + \
                               " had result: " + oldresult)
                        eprint(FAIL + "ERROR: " + ENDC + "'" + call + "'" + \
                               " had result: " + result)
                        eprint("\n")
                    else:
                        # Results agree
                        if oldtime > time:
                            # new result is faster; update results
                            results[lemma] = (result, time), job.arguments
    return results



def intermediate_file_name(input_file, tool, lemma):
    """
        This function generates a file name for the intermediate generated
        for deepsec/proverif.
        TODO: Once we can generate files on a per lemma basis, we need to
        include the name of the lemma in the file name as well.
    """
    # Get input_file without '.spthy'
    file_name, _ = os.path.splitext(input_file)
    lemmastring = lemma + "_" if lemma else ""
    return file_name + "_" + lemmastring + tool + TOOL_TO_FILE_TYPE[tool]

def generate_files(input_file, flags, lemmas, argdict, diff):
    """
        This function generates files for all tools in argdict except
        for Tamarin. For Tamarin, we do not need to generate intermediate
        files, but can use the original input file.
    """
    # Format flags in the way the Tamarin CLI wants them
    flags = [ '-D=' + flag for flag in flags ] if flags else []

    # Diff mode?
    diffstring = " --diff" if diff else ""


    for tool in argdict.keys():
        if tool == SPTHY:
            # Skip Tamarin/spthy. Tamarin does not need intermediate files.
            # It works on the sapic file itself.
            continue

        # For each tool generate a file using Tamarin -m

        # Charlie, Robert, and Niklas discussed this via Mattermost.
        # They plan to add a --lemma parameter to Tamarin which
        # makes Tamarin only export the specified lemma.
        # For now, we can only prove files that contain a single lemma?!
        # Once --lemma has been changed, we need to change the call to Tamarin
        # to include this parameter!
        # Build command

        # Hack to make the loop work if not lemmas are specified
        lemmas = lemmas if lemmas else [""]

        for lemma in lemmas:
            # TODO: Once Tamarin can export a single lemma, change the call
            # to do it!
            cmd = " ".join([TAMARIN_COMMAND, '-m='+tool] + flags + [input_file])
            # Add diff flag
            cmd = cmd + diffstring
            # Change file type according to current tool
            destination = " > " + intermediate_file_name(input_file, tool, lemma)
            # Concatenate the cmd and destination, and run it
            subprocess.run(cmd + destination, shell=True, check=True)

def generate_jobs(input_file, lemmas, argdict, flags):
    """
        This function generates the jobs that we want to concurrently execute.
        A job is a list of arguments that, when used by a Popen call,
        correspond to a call to Tamarin/Deepsec/Proverif on a file/lemma we
        want to time.

        For instance:
            [ proverif, example.pv, -test]
        is a valid job. Another example:
            [ deepsec, example.dps, --local-workers 12]
        is also a valid job.
    """
    jobs = []
    # Hack to make the loop work even if not lemmas were specified
    lemmas = lemmas if lemmas else [""]

    for lemma in lemmas:
        jobs_for_lemma = []
        # For every lemma create the jobs for each tool
        for tool in argdict.keys():
            if tool == SPTHY:
                jobs_for_lemma += generate_tamarin_jobs(
                            input_file, lemma, argdict, flags)
            else:
                jobs_for_lemma += generate_non_tamarin_jobs(
                            tool, input_file, lemma, argdict)

        jobs.append(jobs_for_lemma)
    return jobs


def generate_non_tamarin_jobs(tool, input_file, lemma, argdict):
    """
        Returns a list of jobs (list of lists).
    """
    jobs = []
    toolcmd = TOOL_TO_COMMAND[tool]
    toolclass = TOOL_TO_JOB_CLASS[tool]
    if not argdict[tool][0]:
        # If there were no CLI params specified.
        jobs += [toolclass([toolcmd,  \
                 intermediate_file_name(input_file, tool, lemma)], lemma)]
    else:
        # If CLI params were specified, we use them.
        jobs += [toolclass([toolcmd, intermediate_file_name(input_file, \
                 tool, lemma)] + list(tuple), lemma) \
                 for tuple in itertools.product(*argdict[tool])]

    return jobs

def generate_tamarin_jobs(input_file, lemma, argdict, flags):
    # TODO: Might need to revisit this once the Tamarin CLI has changed
    lemmacli = [ '--prove=' + lemma ] if lemma else ["--prove"]
    # heuristics = [] if argdict.
    flags = [ '-D=' + flag for flag in flags ] if flags else []
    toolcmd = TOOL_TO_COMMAND[SPTHY]
    jobs = []
    if not argdict[SPTHY]:
        jobs = [TamarinJob([toolcmd, input_file] + lemmacli + flags, lemma)]
    else:
        jobs = [TamarinJob([toolcmd, input_file] + lemmacli + flags + \
                list(tuple), lemma) for tuple in itertools.product(*argdict[SPTHY])]

    return jobs



if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('-l', '--lemma', action='extend', nargs='+', type=str,
                        help='prove the given lemmas. If no lemmas are \
                        specified, the tool assumes that there is only one \
                        lemma in the given .spthy')
    # Flags for Tamarin's preprocessor. Used during file/model generation
    parser.add_argument('-D', '--defines', action='extend', nargs='+', type=str,
                        help="flags for Tamarin's preprocessor")
    # The source file we built the models from
    parser.add_argument('input_file', type=str, help='the sapic file')
    # Args for ProVerif.
    parser.add_argument('-p', '--proverif', action='append',
                        nargs='*', type=str, help='arguments for ProVerif')
    # Args for Tamarin
    parser.add_argument('-t', '--tamarin', action='append',
                        nargs='*', type=str, help='arguments for Tamarin')
    # Heuristics for Tamarin
    parser.add_argument('-H', '--heuristic', action='extend',
                        nargs='+', type=str, choices=HEURISTICS,
                        help='heuristics Tamarin should use')
    # Args for Deepsec
    parser.add_argument('-d', '--deepsec', action='append',
                        nargs='*', type=str, help='arguments for Deepsec')
    # Arg for Tamarin diff mode
    parser.add_argument('--diff', action='store_true',
                        help="use Tamarin's diff mode for file generation")
    # Custom Tamarin command
    parser.add_argument('-tname', '--tname', action='store', type=str,
                        help='customize how Tamarin is called; defaults to \
                              "tamarin-prover"')
    # Custom ProVerif command
    parser.add_argument('-pname', '--pname', action='store', type=str,
                        help='customize how ProVerif is called; defaults to \
                              "proverif"')
    # Custom Deepsec command
    parser.add_argument('-dname', '--dname', action='store', type=str,
                        help='customize how Deepsec is called; defaults to \
                              "deepsec"')
    # Custom Time command
    parser.add_argument('-time', '--time', action='store', type=str,
                        help='customize how "time" is called; defaults to \
                              "/usr/bin/time"')
    # Custom timeout
    parser.add_argument('-to', '--timeout', action='store',
                        type=int, help='timeout for the jobs')

    args = parser.parse_args()
    # Error handling
    if args.deepsec is None and args.tamarin is None and args.proverif is None:
        eprint("Provide command line arguments for at least one tool!")
        sys.exit(1)


    # Update time command
    if args.time:
        TIME_COMMAND = args.time

    # Check whether 'usr/bin/time' is available
    if find_executable(TIME_COMMAND) is None:
        eprint(TIME_COMMAND + " executable was not found!")
        sys.exit(1)

    # Change tool commands if specified
    if args.tname:
        TAMARIN_COMMAND = args.tname

    if args.dname:
        DEEPSEC_COMMAND = args.dname

    if args.pname:
        PROVERIF_COMMAND = args.pname

    if args.timeout:
        JOB_TIMEOUT = args.timeout

    # Map tools to their command
    TOOL_TO_COMMAND = { SPTHY: TAMARIN_COMMAND, PROVERIF: PROVERIF_COMMAND,
                       DEEPSEC: DEEPSEC_COMMAND }

    # Extract the list of lemmas
    lemmas = args.lemma if args.lemma else []
    # Extract the list of preprocessor Flags
    flags = args.defines if args.defines else []
    # Create a dict that maps tool (Tamarin=spthy, ProVerif=proverif,
    # and Deepsec=deepsec) to the parsed args
    argdict = dict()
    if args.deepsec:
        argdict[DEEPSEC] = add_double_dashes_to_arguments(args.deepsec)
    if args.proverif:
        argdict[PROVERIF] = add_dashes_to_arguments(args.proverif)
    if args.tamarin:
        if args.tamarin[0]:
            # Actual arguments, not only -t
            tamarinargs = add_double_dashes_to_arguments(args.tamarin)
            argdict[SPTHY] = tamarinargs
        else:
            tamarinargs = []
        if args.heuristic:
            heuristics = [ '--heuristic=' + heuristic for heuristic in \
                         args.heuristic ]
            tamarinargs.append(heuristics)
        argdict[SPTHY] = tamarinargs


    # Generate desired model files from the input file
    generate_files(args.input_file, flags, lemmas, argdict, args.diff)

    # Generate the jobs that we want to concurrently execute
    jobs = generate_jobs(args.input_file, lemmas, argdict, flags)
    # TODO: Concurrent execution!
    for joblist in jobs:
        for job in joblist:
            job.execute()
    # Go through the jobs and collect the results
    results = collect_results(joblist)
    # TODO: pretty print results
    report_results(results)
    sys.exit(0)
