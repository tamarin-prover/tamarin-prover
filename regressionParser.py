import mmap
import subprocess
import sys
from math import floor
from tree_sitter import Language, Parser
import os
import argparse
from distutils.ccompiler import new_compiler
from tempfile import TemporaryDirectory
import platform
from ctypes import cdll, c_void_p
from os import fspath

ignore_list = ["pkcs11-templates.sapic", "right-assoc.spthy", "Yubikey.spthy", "defaultoracle.spthy", "configuration.spthy", "verify_checksign_test.spthy"]

#config = {
#    "max_file_bytes": 1000000,
#    "show_spthy_error": True,
#    "show_sapic_error": False,
#    "show_tactic_error": False
#}

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


def make_bold(text):
    return '\033[1m' + text + '\033[0m'

#https://github.com/tree-sitter/py-tree-sitter/discussions/251

def lang_from_so(path: str, name: str) -> Language:
    lib = cdll.LoadLibrary(fspath(path))
    language_function = getattr(lib, f"tree_sitter_{name}")
    language_function.restype = c_void_p
    language_ptr = language_function()
    return Language(language_ptr)

#SPTHY_LANGUAGE = lang_from_so("./build/spthy.so", "spthy")
#parser = Parser()
#parser.set_language(SPTHY_LANGUAGE)

# Parse example files and collect error data
# Functions:
def parse_from_path(parser, path):
    data = open(path, 'rb')
    text = data.read()
    data.close()
    return parser.parse(text)


def print_status(done_num, total_num):
    percentage = (done_num / total_num) * 100
    bar_length = 30
    bar_progress = floor((percentage * bar_length) / 100)
    status_bar = "[" + bar_progress * "=" + (bar_length - bar_progress) * " " + "]"
    sys.stdout.write('\r')
    sys.stdout.write(status_bar)
    sys.stdout.write(" " + str(percentage) + "%")


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
        print_status(done_num, total_num)
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


def output_coverage(errors):
    total_nodes, err_nodes = summarize_errors(errors)
    print("Total nodes: ", total_nodes)
    print("Error nodes: ", err_nodes)
    if total_nodes:
        print("Coverage: ", ((total_nodes - err_nodes) / total_nodes) * 100)
    else:
        print("No nodes parsed...")


def output_errors(errors):
    for error_file in errors:
        if not len(error_file["err_nodes"]):
            continue
        print("Path: ", make_bold(error_file["path"]), "\n")
        for err_node in error_file["err_nodes"]:
            position = str(err_node["start_point"]) + " - " + str(err_node["end_point"])
            print(make_bold(position))
            print(err_node["text"].decode(), "\n")
        print("\n")


def output_total_successes(file_num, total_parsed_files, completely_parsed):
    print("Total files: " + str(file_num))
    print("Parsed without errors: " + str(completely_parsed))
    print("Parsed with errors: " + str(file_num - completely_parsed))
    if total_parsed_files:
        print("Total success percentage: " + str((completely_parsed / file_num) * 100))
    else:
        print("No files parsed...")

def is_subdir(path):
    ignored_directories = [
        "./tamarin-prover/examples/sapic/not-working",
        "./tamarin-prover/examples\\sapic\\not-working",
        "./tamarin-prover/examples/sapic/deprecated",
        "./tamarin-prover/examples\\sapic\\deprecated"
	]
    for d in ignored_directories:
        if d in path:
            return True
    return False

def testParser(logging, parsingSuccessful, warningLvl):

		config = {
            "max_file_bytes": 1000000,
            "show_spthy_error": True,
            "show_sapic_error": True,
            "show_tactic_error": False
        }
		logging.warning("build spthy-library...")
		build_library(
          './tree-sitter/build/spthy.so',
          [os.path.normpath('./tree-sitter/tree-sitter-spthy')]
        )
		SPTHY_LANGUAGE = lang_from_so("./tree-sitter/build/spthy.so", "spthy")
		parser = Parser()
		parser.set_language(SPTHY_LANGUAGE)

		spthy_files = []
		sapic_files = []

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
        
		# Total failures
		print("""\n 
==============================================================
Total successes:
==============================================================
		""")
		total_files = (config["show_spthy_error"] * len(spthy_files)
																+ config["show_sapic_error"] * len(sapic_files))
		total_parsed_files = spthy_completely_parsed + sapic_completely_parsed
		output_total_successes(total_files, total_parsed_files, total_parsed_files)

		# Total Coverage
		print("""\n
==============================================================
Total coverage:
==============================================================
		""")
		total_errors = []
		total_errors.extend(spthy_data)
		total_errors.extend(sapic_data)
		if len(total_errors) != 0:
			parsingSuccessful = False

		output_coverage(total_errors)

		# Coverage per feature
		print("""\n
==============================================================
Coverage per feature:
==============================================================""")
		if config["show_spthy_error"]:
			print("""
--------
spthy:
--------""")
			output_total_successes(len(spthy_files), total_parsed_files, spthy_completely_parsed)
			output_coverage(spthy_data)

		if config["show_sapic_error"]:
			print("""
--------
SAPiC:
--------""")
			output_total_successes(len(sapic_files), total_parsed_files, sapic_completely_parsed)
			output_coverage(sapic_data)