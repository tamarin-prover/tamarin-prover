#!/usr/bin/python3

import signal
import multiprocessing
import re
import argparse
import subprocess
import os
import itertools
import sys
import subprocess
import shutil
import time

def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

# Timeout for the jobs in seconds
JOB_TIMEOUT = 5

# Tamarins heustics
HEURISTICS = [ 's', 'S', 'c', 'C', 'i', 'I' ]
DEEPSEC = "deepsec"
SPTHY = "spthy"
PROVERIF = "proverif"
TAMARIN_COMMAND = "tamarin-prover"
PROVERIF_COMMAND = "proverif"
DEEPSEC_COMMAND = "deepsec"
PROOF = "proof"
COUNTEREXAMPLE = 'counterexample'
INCONCLUSIVE = 'inconclusive'
NOT_STARTED = 'not_started'
STARTED = 'started'
FINISHED = 'finished'
TIMEOUT = 'timeout'
INTERRUPTED = 'interrupted'
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
        # The result of the job
        self.result = None
        # returncode of job
        self.returncode = None
        # Status of the job
        self.status = NOT_STARTED
        # Time the job took
        self.time = ""

    def __str__(self):
        return str(self.arguments)

    def __repr__(self):
        return str(self)

    def execute(self, result_queue):
        """
        Executes the job specified by self.arguments and, iff
        it was sucessful, returns a dictionary containing the result
        """
        self.status = STARTED
        call =  "'" + " ".join(self.arguments) + "'"
        print("Executing " + call)
        try:
            p = None
            def execute_signal_handler(signum, frame):
                self.status = INTERRUPTED
                if p:
                    # If the job already started
                    p.terminate()
                    # kill own process
                    sys.exit(1)

            # Register new signal handler
            signal.signal(signal.SIGINT, execute_signal_handler)
            signal.signal(signal.SIGTERM, execute_signal_handler)
            p = subprocess.Popen(self.arguments, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, universal_newlines=True)
            # Start timer
            starttime = time.time()
            stdout_data, stderr_data = p.communicate(timeout=JOB_TIMEOUT)
            # calculate time
            self.time = format(time.time() - starttime, '.4f')
            if p.returncode != 0:
                # Check if job completed correctly
                # Save returncode to later report it
                self.returncode = p.returncode
                self.status = ERROR
                return
            # Get the results
            self.parse_results(stdout_data, stderr_data)
            if self.status == PARSE_ERROR:
                return

            self.status = FINISHED
        except subprocess.TimeoutExpired:
            self.status = TIMEOUT
        finally:
            result = (self.status, call, self.lemma, self.returncode, self.result, self.time)
            result_queue.put(result)
            print_single_result(result)


class TamarinJob(Job):

    def parse_results(self, stdout, stderr):
        # Parse the results for the self.lemma from the output
        # and save them in self.results
        # If no lemmas was specified, we assume that there is
        # only one lemma in a .spthy file
        # Search for the time Tamarin took
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

        self.result = result


class ProverifJob(Job):

    def parse_results(self, stdout, stderr):
        # Parse the results for the self.lemma from the output
        # and save them in self.results
        # We assume that there is only one query in a .pv file
        # Search for the time ProVerif took
        # Search for the result in ProVerif stdout
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
        self.result = result

class DeepsecJob(Job):

    def parse_results(self, stdout, stderr):
        # Parse the results for the self.lemma from the output
        # and save them in self.results
        # We assume that there is only one query in a .dps file
        # Search for the time Deepsec took
        result = ""
        if re.search(r"not session equivalent", stdout):
            result = COUNTEREXAMPLE
        elif re.search(r"session equivalent", stdout):
            result = PROOF
        else:
            self.status = PARSE_ERROR
            return

        self.result = result



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


def execute_joblist(joblist, queue):
    # Concurrently execute the jobs in the joblist.
    processes = [None] * len(joblist)
    result_queue = multiprocessing.SimpleQueue()
    for i in range(len(processes)):
        job = joblist[i]
        processes[i] = multiprocessing.Process(target=job.execute,
                       args=(result_queue, ))

    try:
        for p in processes:
            p.start()
        # Counter to abort once all jobs are done
        counter = len(processes)
        # We want the results as they finish
        results = []

        while counter:
            result = result_queue.get()
            counter -= 1
            results.append(result)
            # Check job status
            if result[0] == FINISHED:
                # abort all jobs as we got a valid result
                for p in processes:
                    if p.is_alive():
                        os.kill(p.pid, signal.SIGINT)
                break

    finally:
        for p in processes:
            p.join()

    # return results via queue
    queue.put(results)



def print_single_result(result):
    status, call, lemma, returncode, outcome, time = result
    if status == ERROR:
        eprint(FAIL + "ERROR: " + ENDC + \
               call + " returned returncode " + str(returncode))
    elif status == TIMEOUT:
        eprint(WARNING + "WARNING: " + ENDC + \
                call + " timed out after " + str(JOB_TIMEOUT) + " seconds")
    elif status == INTERRUPTED:
        eprint(WARNING + "INTERRUPTED: " + ENDC + call)
    elif status == PARSE_ERROR:
        eprint(FAIL + "ERROR: " + ENDC + "The result from "\
                + call + " could not be parsed.")
    elif status == FINISHED:
        color = GREEN if outcome == PROOF else \
                (FAIL if outcome == COUNTEREXAMPLE else INCONCLUSIVE)
        print("Finished " + call + " after " + str(time) + " seconds: " + color + outcome + ENDC)


def report_results(results):
    # Here we save the good results
    for results_per_lemma in results:
        # get lemma name, ugly... but yeah
        # Initialize best result to None
        best_result = None
        bad_results = []
        lemma = ""
        for result in results_per_lemma:
            lemma = result[2]
            # String for error reporting
            status, call, lemma, returncode, outcome, time = result
            # Make sure every job ran
            assert status == FINISHED or status == TIMEOUT or \
                   status == ERROR or status == PARSE_ERROR
            if status != FINISHED:
                # Report error/timeout etc.
                bad_results.append(result)
                continue
            # Result is good
            if best_result is None:
                best_result = result

            if best_result[0] != status:
                # Report mismatch
                oldcall = best_result[1]
                oldresult = best_result[5]
                eprint(FAIL + "ERROR: " + ENDC + "'" + oldcall + "'" + \
                       " had result: " + oldresult)
                eprint(FAIL + "ERROR: " + ENDC + "'" + call + "'" + \
                       " had result: " + outcome)
            elif best_result[5] > time:
                # compare time
                best_result = result


        # Report results for this lemma
        print("=" * 90)
        lemmastring = " for " + lemma if lemma else ""
        if bad_results:
            print("Reporting errors" + lemmastring + ":\n")
            for bad_result in bad_results:
                print_single_result(bad_result)

        if best_result:
            print("Reporting result" + lemmastring + ":\n")
            print_single_result(best_result)

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


def std_signal_handler(sig, frame):
    # Standard signal handler that exits.
    # We use this to catch SIGINT
    print("Std sig handler called")
    sys.exit(1)


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
    # Custom timeout
    parser.add_argument('-to', '--timeout', action='store',
                        type=int, help='timeout for the jobs')

    args = parser.parse_args()
    # Error handling
    if args.deepsec is None and args.tamarin is None and args.proverif is None:
        eprint("Provide command line arguments for at least one tool!")
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
    # For every lemma/joblist start a concurrent execution of its jobs.
    # This first layer of concurrency uses a worker per lemma/joblist
    processes = [None] * len(jobs)

    # Register signal handler
    # This handler is inherited by the child processes
    signal.signal(signal.SIGINT, std_signal_handler)
    signal.signal(signal.SIGTERM, std_signal_handler)
    for i in range(len(processes)):
        # Processes[i] = jobs[i] + queue for communication
        q = multiprocessing.SimpleQueue()
        processes[i] = multiprocessing.Process(target=execute_joblist,
                       args=(jobs[i], q, )), q



    try:
        # Start all the processes
        for p, q in processes:
            p.start()
        # !!! There is a race condition here. If the main process receives
        # !!! a signal before the code below executes, the started child
        # !!! processes are not terminated correctly.


        # Collect the results of the Processes
        results = [ q.get() for p, q in processes ]
        # q.get() blocks until a result is available

    finally:
        for p, q in processes:
            p.join()

    # Current results list contains results with timeouts, errors etc.
    # Sort these out of the list, and report them.
    results = report_results(results)
    # report_results(results)

    sys.exit(0)
