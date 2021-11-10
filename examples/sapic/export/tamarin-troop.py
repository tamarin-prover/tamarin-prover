#!/usr/bin/python3

import argparse
import subprocess
import os

# Tamarins heustics
HEURISTICS = [ 's', 'S', 'c', 'C', 'i', 'I' ]
DEEPSEC = "deepsec"
SPTHY = "spthy"
PROVERIF = "proverif"
TAMARIN_COMMAND = "tamarin-prover-proverif-output"
# Dict mapping tool to file type
TOOL_TO_FILE_TYPE = { "spthy": ".spthy", "proverif": ".pv", "deepsec": ".dps" }
# Get current working directory
WD = os.path.dirname(os.path.realpath(__file__))


def generate_module_files(input_file, flags, lemmas, argdict):
    for key in argdict.keys():
        # For each tool generate a file using Tamarin -m
        # TODO: In the future, we want to do this for every lemmas too.
        # However, currently Tamarin does not support this yet.

        # Absolute path to the input file
        input_file = WD + '/' + input_file
        # Format flags in the way the Tamarin CLI wants them
        flags = [ '-D=' + flag for flag in flags ] if flags else []
        # And convert them into a string
        cmd = " ".join([TAMARIN_COMMAND, '-m='+key] + flags + [input_file])
        # Get input_file without '.spthy'
        file_name, _, _ = input_file.partition('.')
        # Change file type according to current tool
        destination = " > " + file_name + "_" + key + TOOL_TO_FILE_TYPE[key]
        # Concatenate the cmd and destination, and run it
        subprocess.run(cmd + destination, shell=True, check=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    # We assume that we can pass the lemmas to Tamarin, and Tamarin will
    # create a file for each lemma. However, currently this is not implemented.
    parser.add_argument('-l', '--lemma', action='extend', nargs='+', type=str,
                        help='prove the given lemmas')
    # Flags for Tamarin's preprocessor. Used during file/model generation
    parser.add_argument('-D', '--defines', action='extend', nargs='+', type=str,
                        help="flags for Tamarin's preprocessor")
    # The source file we built the models from
    parser.add_argument('input_file', type=str, help='the sapic file')
    # Args for ProVerif.
    parser.add_argument('-p', '--proverif', action='append',
                        nargs='+', type=str, help='arguments for ProVerif')
    # Args for Tamarin
    parser.add_argument('-t', '--tamarin', action='append',
                        nargs='+', type=str, help='arguments for Tamarin')
    # Heuristics for Tamarin
    parser.add_argument('-H', '--heuristic', action='extend',
                        nargs='+', type=str, choices=HEURISTICS,
                        help='heuristics Tamarin should use')
    # Args for Deepsec
    parser.add_argument('-d', '--deepsec', action='append',
                        nargs='+', type=str, help='arguments for Deepsec')

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
        if argdict[SPTHY]:
            argdict[SPTHY].append(args.heuristic)
        else:
            argdict[SPTHY] = args.heuristic

    # Generate desired model files from the input file
    generate_module_files(args.input_file, flags, lemmas, argdict)

    # Concurrently execute the cross-product of the given args
    # on the generate model files
    pass
