import mmap, subprocess, sys, io, os, argparse, distutils, platform, logging
from math import floor
from tree_sitter import Language, Parser
from distutils.ccompiler import new_compiler
from tempfile import TemporaryDirectory
from ctypes import cdll, c_void_p
from os import fspath
from regressionColors import *

ignore_list = ["right-assoc.spthy", "Yubikey.spthy", "defaultoracle.spthy", "configuration.spthy", "verify_checksign_test.spthy", "TPM_DAA_JoinCertify_with_fix_BSN.spthy"]

# https://github.com/ivechan/py-tree-sitter/blob/d3c4c823172d5c0c7c4da0b52ea09d9bf2892853/tree_sitter/__init__.py

def build_library(output_path, repo_paths):
    output_mtime = 0
    if os.path.exists(output_path):
        output_mtime = os.path.getmtime(output_path)

    if len(repo_paths) == 0:
        raise ValueError('Must provide at least one language folder')

    cpp = False
    source_paths = []
    source_mtimes = [os.path.getmtime(__file__)]
    for repo_path in repo_paths:
        src_path = os.path.join(repo_path, 'src')
        source_paths.append(os.path.join(src_path, "parser.c"))
        source_mtimes.append(os.path.getmtime(source_paths[-1]))
        if os.path.exists(os.path.join(src_path, "scanner.cc")):
            cpp = True
            source_paths.append(os.path.join(src_path, "scanner.cc"))
            source_mtimes.append(os.path.getmtime(source_paths[-1]))
        elif os.path.exists(os.path.join(src_path, "scanner.c")):
            source_paths.append(os.path.join(src_path, "scanner.c"))
            source_mtimes.append(os.path.getmtime(source_paths[-1]))

    compiler = new_compiler()
    if cpp:
        if find_library('c++'):
            compiler.add_library('c++')
        elif find_library('stdc++'):
            compiler.add_library('stdc++')

    if max(source_mtimes) > output_mtime:
        with TemporaryDirectory(suffix = 'tree_sitter_language') as dir:
            object_paths = []
            for source_path in source_paths:
                if platform.system() == 'Windows':
                    flags = None
                else:
                    flags = ['-fPIC']
                    if source_path.endswith('.c'):
                        flags.append('-std=c99')
                # compiler functions cannot be easily silenced
                object_paths.append(compiler.compile(
                    [source_path],
                    output_dir = dir,
                    include_dirs = [os.path.dirname(source_path)],
                    extra_preargs = flags
                )[0])
            compiler.link_shared_object(object_paths, output_path)
        return True
    else:
        return False

#https://github.com/tree-sitter/py-tree-sitter/discussions/251

def lang_from_so(path: str, name: str) -> Language:
    lib = cdll.LoadLibrary(fspath(path))
    language_function = getattr(lib, f"tree_sitter_{name}")
    language_function.restype = c_void_p
    language_ptr = language_function()
    return Language(language_ptr)

# Parse example files and collect error data
# Functions:
def parse_from_path(parser, path):
    data = open(path, 'rb')
    text = data.read()
    data.close()
    return parser.parse(text)

def traverse_tree(root):
    node_num = 0
    unparsed_symbols = []

    # Traverse tree using stack
    stack = [root]
    while len(stack):
        top = stack.pop()
        for child in top.children:
            stack.append(child)

        # Process node:
        node_num += 1
        if top.type == 'ERROR':
            err_node = top
            err_data = {"id": err_node.id,
                        "type": err_node.type,
                        "start_point": err_node.start_point,
                        "end_point": err_node.end_point,
                        "text": err_node.text}
            unparsed_symbols.append(err_data)

    return node_num, unparsed_symbols


def collect_errors(parser, file_paths):
    completely_parsed = 0
    data = []
    done_num = 0
    total_num = len(file_paths)
    for path in file_paths:
        done_num += 1
        root = parse_from_path(parser, path).root_node
        total_node_num, err_nodes = traverse_tree(root)
        if not len(err_nodes):
            completely_parsed += 1
        data.append({"path": path,
                     "total_node_num": total_node_num,
                     "err_node_num": len(err_nodes),
                     "err_nodes": err_nodes})
    return completely_parsed, data


# Analyze and output error
# Functions:
def summarize_errors(errors):
    node_num = 0
    err_node_num = 0
    for error in errors:
        node_num += error["total_node_num"]
        err_node_num += error["err_node_num"]
    return node_num, err_node_num


def output_coverage(logging, errors):
    total_nodes, err_nodes = summarize_errors(errors)
    logging.warning("Total nodes: " + str(total_nodes))
    if err_nodes == 0:
        logging.warning(color(colors.GREEN + colors.BOLD, "Error nodes: " + str(err_nodes)))
    else:
        logging.warning(color(colors.RED + colors.BOLD, "Error nodes: " + str(err_nodes)))
    success_percentage = ((total_nodes - err_nodes) / total_nodes) * 100
    if total_nodes:
        if success_percentage == 100:
            logging.warning(color(colors.GREEN + colors.BOLD, "Coverage: " + str(success_percentage) + "%"))
        else:
            logging.warning(color(colors.RED + colors.BOLD, "Coverage: " + str(success_percentage) + "%"))

    else:
        logging.warning(color(colors.RED + colors.BOLD, "No nodes parsed..."))


def output_errors(logging, errors):
    for error_file in errors:
        if not len(error_file["err_nodes"]):
            continue
        logging.info(color(colors.RED + colors.BOLD, "Path: " + str(error_file["path"]) + "\n"))
        for err_node in error_file["err_nodes"]:
            position = str(err_node["start_point"]) + " - " + str(err_node["end_point"])
            logging.info(color(colors.RED + colors.BOLD, position))
            logging.info(color(colors.RED + colors.BOLD, err_node["text"].decode()  + "\n"))


def output_total_successes(logging, file_num, total_parsed_files, completely_parsed):
    logging.error("Total files: " + str(file_num))
    logging.error("Parsed without errors: " + str(completely_parsed))
    parsed_with_errors = file_num - completely_parsed
    if parsed_with_errors == 0:
        logging.error(color(colors.GREEN + colors.BOLD, "Parsed with errors: " + str(parsed_with_errors)))
    else:
        logging.error(color(colors.RED + colors.BOLD, "Parsed with errors: " + str(parsed_with_errors)))
    success_percentage = (completely_parsed / file_num) * 100
    if total_parsed_files:
        if success_percentage == 100:
            logging.warning(color(colors.GREEN + colors.BOLD, "Success rate: " + str(success_percentage) + "%"))
            return True
        else:
            logging.warning(color(colors.RED + colors.BOLD, "Success rate: " + str(success_percentage) + "%"))
            return False
    else:
        logging.error(color(colors.RED + colors.BOLD, "No files parsed..."))
        return False

def is_subdir(path):
    ignored_directories = [
        "./examples/sapic/not-working",
        "./examples\\sapic\\not-working",
        "./examples/sapic/deprecated",
        "./examples\\sapic\\deprecated"
	]
    for d in ignored_directories:
        if d in path:
            return True
    return False

def testParser(logging, parsingSuccessful, verbosity):

		config = {
            "max_file_bytes": 1000000,
            "show_spthy_error": True,
            "show_sapic_error": True,
        }

		logging.warning("building the spthy parser library ...")
		build_library(
          './tree-sitter/build/spthy.so',
          [os.path.normpath('./tree-sitter/tree-sitter-spthy')]
        )

		SPTHY_LANGUAGE = lang_from_so("./tree-sitter/build/spthy.so", "spthy")
		parser = Parser()
		parser.set_language(SPTHY_LANGUAGE)
		spthy_files = []
		sapic_files = []

		logging.warning("testing the parser ...")

		for dir_path, dir_names, file_names in os.walk("./examples", topdown=True):
			if is_subdir(dir_path):
				continue
			for file in file_names:
				if file in ignore_list:
					continue
				file_path = os.path.join(dir_path, file)

				if os.stat(file_path).st_size == 0 or os.stat(file_path).st_size > config["max_file_bytes"]:
					continue

				with (open(file_path) as f):
					s = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
					if not (file.endswith(".spthy") or file.endswith(".sapic")) or s.find(bytes('theory', 'utf-8')) == -1:
						f.close()
						continue
					elif s.find(bytes('process:', 'utf-8')) != -1 or s.find(bytes('predicates:', 'utf-8')) != -1 or s.find(
					bytes(';', 'utf-8')) != -1 or s.find(bytes('export', 'utf-8')) != -1 or file.endswith(".sapic"):
						sapic_files.append(file_path)
					else:
						spthy_files.append(file_path)
					f.close()

		spthy_completely_parsed, spthy_data = 0, []
		if config["show_spthy_error"]:
			spthy_completely_parsed, spthy_data = collect_errors(parser, spthy_files)

		sapic_completely_parsed, sapic_data = 0, []
		if config["show_sapic_error"]:
			sapic_completely_parsed, sapic_data = collect_errors(parser, sapic_files)
        
		# Statistics
		logging.error("""\n 
==============================================================
Parser results:
==============================================================
		""")
		total_files = (config["show_spthy_error"] * len(spthy_files)
																+ config["show_sapic_error"] * len(sapic_files))
		total_parsed_files = spthy_completely_parsed + sapic_completely_parsed
		parsingSuccessful = output_total_successes(logging, total_files, total_parsed_files, total_parsed_files)
		total_errors = []
		total_errors.extend(spthy_data)
		total_errors.extend(sapic_data)
		output_coverage(logging, total_errors)

		# Per feature
		if config["show_spthy_error"] and verbosity > 1:
			logging.info("""
--------
spthy:
--------""")
			output_total_successes(logging, len(spthy_files), total_parsed_files, spthy_completely_parsed)
			output_coverage(logging, spthy_data)

		if config["show_sapic_error"] and verbosity > 1:
			logging.info("""
--------
SAPiC:
--------""")
			output_total_successes(logging, len(sapic_files), total_parsed_files, sapic_completely_parsed)
			output_coverage(logging, sapic_data)

# Errors
		if verbosity >= 3 and not parsingSuccessful:
			logging.info(color(colors.RED + colors.BOLD, """\n
==============================================================
Parser errors:
=============================================================="""))
			if config["show_spthy_error"]:
				logging.info("""
--------
spthy:
--------""")
				output_errors(logging, spthy_data)

			if config["show_sapic_error"]:
				logging.info("""
--------
SAPiC:
--------""")
				output_errors(logging, sapic_data)
		print("\n")