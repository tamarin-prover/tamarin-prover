#!/usr/bin/python3

import argparse
import subprocess
import os
import itertools

# Tamarins heustics
HEURISTICS = [ 's', 'S', 'c', 'C', 'i', 'I' ]
DEEPSEC = "deepsec"
SPTHY = "spthy"
PROVERIF = "proverif"
TAMARIN_COMMAND = "tamarin-prover-proverif-output"
# Dict mapping tool to file type
TOOL_TO_FILE_TYPE = { "spthy": ".spthy", "proverif": ".pv", "deepsec": ".dps" }

def intermediate_file_name(input_file, tool, lemma):
    """
        This function generates a file name for the intermediate generated
        for deepsec/proverif.
        TODO: Once we can generate files on a per lemma basis, we need to
        include the name of the lemma in the file name as well.
    """
    # Get input_file without '.spthy'
    file_name, _, _ = input_file.partition('.')
    return file_name + "_" + tool + TOOL_TO_FILE_TYPE[tool]

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
            # Skip Tamarin/spthy.
            continue

        # For each tool generate a file using Tamarin -m
        # TODO: In the future, we want to do this for every lemma.
        # However, currently Tamarin does not support this.

        # Charlie, Robert, and Niklas discussed this via Mattermost.
        # They plan to add a --lemma parameter to Tamarin which
        # makes Tamarin only export the specified lemma.
        # For now, we can only prove files that contain a single lemma?!
        # Once --lemma has been changed, we need to change the call to Tamarin
        # to include this parameter!
        # Build command
        cmd = " ".join([TAMARIN_COMMAND, '-m='+tool] + flags + [input_file])
        # Add diff flag
        cmd = cmd + diffstring
        print(cmd)
        # Change file type according to current tool
        # TODO: Add lemma parameter to file name
        destination = " > " + intermediate_file_name(input_file, tool, "")
        # Concatenate the cmd and destination, and run it
        subprocess.run(cmd + destination, shell=True, check=True)

def generate_jobs(input_file, lemmas, argdict):
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
    for tool in argdict.keys():
        # Generate jobs for each tool
        if tool == SPTHY:
            # Special case for Tamarin. We do not generate a file per lemma
            # for Tamarin. Instead, we need to use its CLI/lemma selector.
            # Thus, generating jobs for Tamarin is different than generating
            # jobs for ProVerif/Deepsec.
            jobs += generate_tamarin_jobs()

        # TODO: For debugging/simplification we convert the iterable object
        # other_jobs into a list here. This might not be the most efficient
        # way. Revisit this at a later point.
        jobs += list(generate_non_tamarin_jobs(tool,
                                               input_file, lemmas, argdict))
    return jobs

def generate_non_tamarin_jobs(tool, input_file, lemmas, argdict):
    """
        Returns a list of jobs (list of lists).
    """
    jobs = []
    for lemma in lemmas:
        print(tool, input_file, lemma, argdict[tool])
        # Build the crossproduct of tool, input_file, CLI parameters
        # * is the unpack operator. It extracts all items in the list
        # argdict[tool] and adds them to the function call.
        if not argdict[tool][0]:
            # If there were no CLI params specified.
            jobs += list(itertools.product([tool]
                   ,[intermediate_file_name(input_file, tool, lemma)]))
        else:
            # If CLI params were specified, we use them.
            jobs += list(itertools.product([tool]
                   ,[intermediate_file_name(input_file, tool, lemma)]
                   ,*argdict[tool]))
    return jobs


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('-l', '--lemma', action='extend', nargs='+', type=str,
                        help='prove the given lemmas')
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
                        help="Flag to use Tamarin's diff mode\
                        for file generation")

    args = parser.parse_args()
    # Extract the list of lemmas
    lemmas = args.lemma
    # Extract the list of preprocessor Flags
    flags = args.defines
    # Create a dict that maps tool (Tamarin=spthy, ProVerif=proverif,
    # and Deepsec=deepsec) to the parsed args
    argdict = dict()
    if args.deepsec:
        argdict[DEEPSEC] = args.deepsec
    if args.proverif:
        argdict[PROVERIF] = args.proverif
    if args.tamarin:
        argdict[SPTHY] = args.tamarin
    if args.heuristic:
        if SPTHY in argdict:
            argdict[SPTHY].append(args.heuristic)
        else:
            argdict[SPTHY] = args.heuristic

    # Generate desired model files from the input file
    # generate_files(args.input_file, flags, lemmas, argdict, args.diff)
    # print(lemmas)
    # print(flags)
    # print(args.diff)
    # print(argdict)

    # Generate the jobs that we want to concurrently execute
    jobs = generate_jobs(args.input_file, lemmas, argdict)
    print(jobs)
