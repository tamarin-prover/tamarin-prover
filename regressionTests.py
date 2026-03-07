from html import parser
import subprocess, sys, re, os, argparse, logging, datetime, shutil


class colors:
	""" terminal coloring """
	PINK = '\033[95m'
	BLUE = '\033[94m'
	CYAN = '\033[96m'
	GREEN = '\033[92m'
	YELLOW = '\033[93m'
	RED = '\033[91m'
	ENDC = '\033[0m'
	BOLD = '\033[1m'

def color(color, text):
	return(color + text + colors.ENDC)

def getColorQuality(valueA, valueB):
	""" fakes a gradient depending on the relative quality of valueB """
	valueDiv = 1 if valueA == 0 else valueB/valueA
	if valueDiv < 0.5:
		return colors.BLUE
	if valueDiv < 0.8:
		return colors.CYAN
	if valueDiv < 1.3:
		return colors.GREEN
	elif valueDiv < 1.8:
		return colors.YELLOW
	else:
		return colors.RED



def iterFolder(folder):
	""" Yields all files in the folder that have a .spthy ending. """
	for dname, dirs, files in os.walk(folder):
		for fname in files:
			fpath = os.path.join(dname, fname)
			if not fpath.endswith(".spthy"):
				continue
			yield fpath

## functions for cutting and parsing part of the proof ##
def parseTest(lines, tester):
	keywords = ["rule", "lemma", "/*", "*/", "restriction", "section", "text", "equations", "builtins", "configuration", "functions", "end", "heuristic", "predicate", "options", "process", "macros"]
	try:
		for key in keywords:
			if(tester != key):
				lines = lines.split(key)[0]
		return lines.replace('\t', '')
	except Exception:
		return f"There was an error while parsing {tester}"

def extractSection(lines, section):
	"""
	Extracts the block for a given section (e.g. 'equations', 'functions', 'macros')
	from the input text. Returns the block as a string.
	"""
	headers = [
		"rule", "lemma", "restriction", "section", "text", "equations", "builtins",
		"configuration", "functions", "end", "heuristic", "predicate", "options",
		"process", "macros"
	]
	# Remove the current section from the list
	other_headers = [h for h in headers if h != section]
	# Build regex for section start and next header
	pattern = rf"^\s*{section}\b.*?(.*?)(?=^\s*({'|'.join(other_headers)})\b|\Z)"
	match = re.search(pattern, lines, re.DOTALL | re.MULTILINE)
	if match:
		return match.group(1).strip()
	return ""

def stripWarningAndFooter(lines):
    """
    Removes the wellformedness block (success or warning) and everything after it from the text.
    Returns the main content only.
    """
    # Regex to match either the success or warning wellformedness block
    match = re.search(
        r'(/\*\s*All wellformedness checks were successful\.\s*\*/|WARNING: the following wellformedness checks failed!)',
        lines,
        re.DOTALL
    )
    if match:
        return lines[:match.start()], lines[match.start():]
    return lines, ""

def extractRules(text):
    """
    Extracts all rule blocks and their attributes from the file text.
    Returns a dict: {'header': String, 'body': String, 'attributes': {<key:String>: <value:String>}, 'name': String}
    """
    # Match 'rule' at the start of a line, then any lines until a colon, then the rule body, up to the next header or end
    # Multiline = allow matching across multiple lines (^ starts at the start of a line)
    # Dotall = allow . to match newlines
    rule_pattern = re.compile(
        r'^rule.+?:\n(.*?)(?=^\s*(rule\b|restriction\b|lemma\b|section\b|end\b|\Z))',
        re.MULTILINE | re.DOTALL
    )
    rules = []
    for match in rule_pattern.finditer(text):
        # The header is everything before the first colon
        header = text[match.start():text.find(':', match.start())].strip()
        body = match.group(1).strip()
        # Extract attributes from header (handles both key="value" and key='value')
        attr_pattern = re.compile(r'(\w+)\s*=\s*([\'"][^\'"]*[\'"]|[^\s,\]]+)')
        attributes = dict((k, v.strip('\'"')) for k, v in attr_pattern.findall(header))
        # Extract rule name
        name_match = re.search(r'rule\s*(?:\([^)]+\))?\s*([^\[\(:]+)', header)
        name = name_match.group(1).strip() if name_match else ""
        rules.append({
            'header': header,
            'body': body,
            'attributes': attributes,
            'name': name
        })
    return rules

def parseFile(path):
	"""
	Parses a _analyzed.spthy file and returns their content in a tuple

	(lemmas([str]), results([bool]), steps([int]), time(float), proof)
	Note that time is not a list but a single value.
	If there is an error, the error message is returned as a string
	"""

	## open file ##
	try:
		with open(path,'r') as f:
			fileContent = f.read()
   

		warningMarker = "WARNING: the following wellformedness checks failed!"
		outputMarker = "/* Output"
  
		if warningMarker in fileContent:
			# Separate the part before the wellformedness warnings and the rest
			proof, output = fileContent.split(warningMarker, 1)
			output = warningMarker + output
		elif outputMarker in fileContent:
			#If there is no warning, just split everything before the output part
			proof, output = fileContent.split(outputMarker, 1)
			output = outputMarker + output
		else:
			#fallback
			proof = fileContent
			output = ""
   
		if 'summary of summaries' in output:
			summary = output.split('summary of summaries', 1)[-1]
		else:
			summary = ""
	except Exception:
		return f"There was an error while reading {path}"
	## parse time ##
	times = re.findall(r"processing time: (\d+\.?\d*)s", output)
	if len(times) != 1:
		return f"Parse error - time: {path}"
	proof, warningFooter = stripWarningAndFooter(proof)
	## parse equations ##
	try:
		equations = extractSection(proof, "equations").splitlines()
		equations = [line.lstrip() for line in equations if line.strip()]
		equations = list(filter(None, equations))
	except Exception as ex:
		return f"Parse error - equations: {path}"

	## parse macros ##
	try:
		macros = extractSection(proof, "macros").splitlines()
		macros = list(filter(None, macros))
	except Exception as ex:
		return f"Parse error - macros: {path}"
	
	## parse functions ##
	try:
		func = extractSection(proof, "functions").replace(' ', '').replace('\n', '')
		func = func.split(',')

	except Exception as ex:
		return f"Parse error - functions: {path}"

	## parse builtins ##
	try: 
		splitBuilt = proof.split("builtins:")
		builtins = parseTest(splitBuilt, "builtins")
		if(builtins != "There was an error while parsing builtins"):
			builtins = builtins.replace(' ', '').replace('\n', '').split(',')
	except Exception as ex:
		return f"Parse error - builtins: {path}"

	## parse config blocks ##
	try:
		if "configuration:" in proof:
			splitConfigBlock = proof.split("configuration:")[-1]
			configblock = parseTest(splitConfigBlock, "configuration").replace('\n', '')
			configblock = configblock.split(' ')
			configblock = list(filter(None, configblock))  # Remove empty strings
		else:
			configblock = []
	except Exception as ex:
		return f"Parse error - config block: {path}"
	
	## parse rules ##
	try:
		rules = extractRules(proof)
	except Exception as ex:
		return f"Parse error - rules: {path}"
	

	## parse warning ##
	try:
		warning = []
		test = False
		for line in output.splitlines():
			if test and line != '':
				warning.append(line)
			if test and line.find("*/") != -1:
				test = False
			if line.find("All wellformedness checks were successful.") != -1:
				warning.append(line)
			if line.find("WARNING: the following wellformedness checks failed!") != -1: 
				test = True
				warning.append(line)
		warning = "".join([str(item) + ' ' for item in warning]).replace("/*", '').replace("*/", '')
	except Exception as ex:
		return f"Parse error - warnings: {path}"
	

	## parse lemmas ##
	try:
		
		parsed = re.findall(r"(\w+) (?:\(.*\))?:(?!  ) (.*) \((\d+) steps\)\n", summary)
		parsed = [(lemmas, res=="verified", int(steps)) for (lemmas, res, steps) in parsed]  # convert types
		parsed = list(zip(*parsed))             # transpose matrix
		if (parsed == []): parsed = [[],[],[]]  #
		return (parsed[0], parsed[1], parsed[2], float(times[0]), proof, equations, func, warning, rules, builtins, configblock, macros)

	except Exception as ex:
		return f"Parse error - lemmas: {path}"
	
def testOutputFileParsing(path):
	"""
	Tests if a generated Tamarin output file can still be parsed.
	"""
	try:
		# Determine file type based on filename patterns
		is_diff_file = any(pattern in path for pattern in [
			"_analyzed-diff.spthy", 
			"_analyzed-diff-noprove.spthy",
			"_analyzed-diff-obseqonly.spthy"
		])

		is_sapic_or_accountability_file = any(pattern in path for pattern in [
			"sapic",
			"accountability"
		])
  
		flags = "--diff" if is_diff_file else ""
		command = f"tamarin-prover --parse-only {flags} {path}"
		
		if is_sapic_or_accountability_file and settings.no_sapic_output_parse_test:
			logging.warning(f"Skipping output parse test for {path} since it is a SAPIC or accountability file and the flag --no-sapic-output-parse-test is set.")
			return True, None

		process = subprocess.run(command, shell=True, capture_output=True, text=True)
		if process.returncode == 0:
			return True, None
		else:
			return False, process.stderr
	except Exception as ex:
		return False, str(ex)

def parseFiles(pathB):
	"""
	Finds the corresponding file in case-studies-regression to the file pathB which is in case-studies.
	Returns a tuple containing the parsed results from both files.
	"""

	## infer regression path name pathA from pathB ##
	pathA = settings.folderA + pathB.split(settings.folderB, 1)[-1]

	## parse files ##
	parsedB = parseFile(pathB)
	if type(parsedB) == str:
		return parsedB
	parsedA = parseFile(pathA)
	if type(parsedA) == str:
		return parsedA
	(lemmasA, resA, stepsA, timeA, proofA, equationsA, funcA, warningA, rulesA, builtinsA, configblockA, macrosA) = parsedA
	(lemmasB, resB, stepsB, timeB, proofB, equationsB, funcB, warningB, rulesB, builtinsB, configblockB, macrosB) = parsedB

	## check compatibility ##
	if lemmasA != lemmasB:
		return f"The lemmas for {pathA} cannot be compared, they are different."

	return (lemmasA, resA, resB, stepsA, stepsB, timeA, timeB, proofA, proofB, equationsA, equationsB, funcA, funcB, warningA, warningB, rulesA, rulesB, builtinsA, builtinsB, configblockA, configblockB, macrosA, macrosB)



def compare():
	"""
	Starts by checking if tamarin can still parse the output.
	Then, searches for all files in case-studies for the corresponding file in case-studies-regression.
	If this search fails, it gives an error message and continues.
	Otherwise, it outputs changed values depending on the verbosity.
	At the end, it outputs a summary
	"""


	majorDifferences = False
	stepSumA, stepSumB, timeSumA, timeSumB = 0, 0, 0, 0
	parseTestsTotal, parseTestsFailed = 0, 0
	
	for pathB in iterFolder(settings.folderB):

		## Tamarin parse testing for the output file##
		if not settings.no_output_parse_test:
			parseTestsTotal += 1
			parseSuccess, parseError = testOutputFileParsing(pathB)
			if not parseSuccess:
				logging.error(color(colors.RED + colors.BOLD, f"Parse test failed for {pathB}"))
				logging.error(color(colors.RED, parseError))
				majorDifferences = True
				parseTestsFailed += 1		
  
		## parse file ##
		parsed = parseFiles(pathB)
		if type(parsed) == str:
			logging.error(color(colors.RED + colors.BOLD, parsed))
			majorDifferences = True
			continue
		(lemmas, resA, resB, stepsA, stepsB, timeA, timeB, proofA, proofB, equationsA, equationsB, funcA, funcB, warningA, warningB, rulesA, rulesB, builtinsA, builtinsB, configblockA, configblockB, macrosA, macrosB) = parsed

		## proofs differ ##
		if proofA != proofB:
			if settings.verbose >= 6:
				pathA = settings.folderA + pathB.split(settings.folderB, 1)[-1]
				command = f"diff {pathA} {pathB} || :"
				output = subprocess.check_output(command, shell=True).decode("utf-8")
				logging.debug(output.split("\n<   processing time")[0])

		if settings.verbose >= 3:
			## Equations differ ## 
			if equationsA != equationsB:
				logging.error(color(colors.RED, pathB.split(settings.folderB, 1)[-1]))
				if len(equationsA) != len(equationsB):
					logging.error(color(colors.RED + colors.BOLD, f"The number of equations are not equal!"))
				else:
					if settings.verbose >= 6:
						for i in range(len(equationsA)):
							if equationsA[i] != equationsB[i]:
								logging.error(color(colors.RED + colors.BOLD, f"The equation changed from {equationsA[i]} to {equationsB[i]}"))
					else:
						logging.error(color(colors.RED + colors.BOLD, f"One or multiple equations do not match!"))
				majorDifferences = True
			
			## Macros differ ##
			if macrosA != macrosB:
				logging.error(color(colors.RED, pathB.split(settings.folderB, 1)[-1]))
				if len(macrosA) != len(macrosB):
					logging.error(color(colors.RED + colors.BOLD, f"The number of macros are not equal!"))
				else:
					if settings.verbose >= 6:
						for i in range(len(macrosA)):
							if macrosA[i] != macrosB[i]:
								logging.error(color(colors.RED + colors.BOLD, f"The macro changed from {macrosA[i]} to {macrosB[i]}"))
					else:
						logging.error(color(colors.RED + colors.BOLD, f"One or multiple macros do not match!"))
				majorDifferences = True

			## Rules differ ##
			if len(rulesA) != len(rulesB):
				logging.error(color(colors.RED + colors.BOLD, f"The number of rules are not equal!"))
				majorDifferences = True
			else:
				for i in range(len(rulesA)):
					ruleA = rulesA[i]
					ruleB = rulesB[i]
					logs = []
					# Compare rule names
					if ruleA['name'] != ruleB['name']:
						logs.append(color(colors.RED + colors.BOLD, f"Rule name changed from '{ruleA['name']}' to '{ruleB['name']}'"))
					# Compare rule attributes
					if ruleA['attributes'] != ruleB['attributes']:
						logs.append(color(colors.RED + colors.BOLD, f"Attributes for rule '{ruleA['name']}' changed from {ruleA['attributes']} to {ruleB['attributes']}"))
					# Compare rule bodies
					if ruleA['body'] != ruleB['body']:
						logs.append(color(colors.RED + colors.BOLD, f"Body for rule '{ruleA['name']}' changed from {ruleA['body']} to {ruleB['body']}"))
					if logs:
						if settings.verbose >= 6:
							logging.error("\n".join(logs))
						else:
							logging.error(color(colors.RED + colors.BOLD, f"One or multiple rules do not match!"))
						majorDifferences = True

			## warnings differ ##
			if warningB != warningA:
				logging.error(color(colors.RED, pathB.split(settings.folderB, 1)[-1]))
				if settings.verbose >= 6:
					logging.error(color(colors.RED + colors.BOLD, f"The warning changed from {warningA} to {warningB}"))
				else:
					logging.error(color(colors.RED + colors.BOLD, f"The warnings do not match!"))
				majorDifferences = True				

			## functions differ ## 
			if funcA != funcB:
				logging.error(color(colors.RED, pathB.split(settings.folderB, 1)[-1]))
				if len(funcA) != len(funcB):
					logging.error(color(colors.RED + colors.BOLD, f"The number of functions are not equal!"))
				else:
					if settings.verbose >= 6:
						for i in range(len(funcA)):
							if funcA[i] != funcB[i]:
								logging.error(color(colors.RED + colors.BOLD, f"The function changed from {funcA[i]} to {funcB[i]}"))
					else:
						logging.error(color(colors.RED + colors.BOLD, f"One or multiple functions do not match!"))
				majorDifferences = True

			## builtins differ ##
			if builtinsA != builtinsB:
				logging.error(color(colors.RED, pathB.split(settings.folderB, 1)[-1]))
				if len(builtinsA) != len(builtinsB):
					logging.error(color(colors.RED + colors.BOLD, f"The number of builtins are not equal!"))
				else:
					if settings.verbose >= 6:
						for i in range(len(builtinsA)):
							if builtinsA[i] != builtinsB[i]:
								logging.error(color(colors.RED + colors.BOLD, f"The builtin changed from {builtinsA[i]} to {builtinsB[i]}"))
					else:
						logging.error(color(colors.RED + colors.BOLD, f"One or multiple builtins do not match!"))
				majorDifferences = True

			## configblocks differ ##
			if configblockA != configblockB:
				logging.error(color(colors.RED, pathB.split(settings.folderB, 1)[-1]))
				if len(configblockA) != len(configblockB):
					if len(list(filter(lambda item: item != "", configblockA))) == len(list(filter(lambda item: item != "", configblockB))):
						if settings.verbose >= 6:
							logging.error(color(colors.RED + colors.BOLD, f"The number of whitespaces in the config block lines are not equal!"))
						else:
							logging.error(color(colors.RED + colors.BOLD, f"Config blocks mismatch!"))
					else:
						if settings.verbose >= 6:
							logging.error(color(colors.RED + colors.BOLD, f"The number of options in the config blocks are not equal!"))
						else:
							logging.error(color(colors.RED + colors.BOLD, f"Config blocks mismatch!"))
				else:
					if settings.verbose >= 6:
						for i in range(len(configblockA)):
							if configblockA[i] != configblockB[i]:
								logging.error(color(colors.RED + colors.BOLD, f"The config block changed from {configblockA[i]} to {configblockB[i]}"))
					else:
						logging.error(color(colors.RED + colors.BOLD, f"Config blocks options mismatch!"))
				majorDifferences = True


		## results differ ##
		if resA != resB:
			logging.error(color(colors.RED, pathB.split(settings.folderB, 1)[-1]))
			for i in range(len(lemmas)):
				if resA[i] != resB[i]:
					logging.error(color(colors.RED + colors.BOLD, f"The result changed from {resA[i]} to {resB[i]} in {lemmas[i]}"))
			majorDifferences = True
			continue

		## compare steps and times ##
		timeColor = getColorQuality(timeA, timeB)
		timeText = "The time changed from " + color(timeColor, f"{str(round(timeA,2)).rjust(12)}s to {str(round(timeB,2)).rjust(9)}s") + f" in {pathB.split(settings.folderB, 1)[-1]}"
		if stepsA != stepsB and settings.verbose < 4:
			logging.info(timeText)
		logging.debug(timeText)
		for i in range(len(lemmas)):
			if stepsA[i] != stepsB[i]:
				logging.info("  The steps changed from " + color(colors.PINK, f"{str(stepsA[i]).rjust(4)} steps to {str(stepsB[i]).rjust(4)} steps") + f" in {lemmas[i]}")

		## aggregate the results ##
		stepSumA += sum(stepsA)
		stepSumB += sum(stepsB)
		timeSumA += timeA
		timeSumB += timeB

	## results differ ##
	logging.warning("\n" + "-"*80 + "\n")
	if majorDifferences:
		if parseTestsFailed > 0:
			logging.warning(f"Parse tests: {parseTestsTotal - parseTestsFailed}/{parseTestsTotal} successful")
			logging.error(color(colors.RED + colors.BOLD, f"{parseTestsFailed} output files failed to parse!"))
		else:
			logging.warning("All output files successfully parsed")
		if settings.verbose >= 3:
			logging.error(color(colors.RED + colors.BOLD, "There were differences in the results of the lemmas, or in the rules, or in the equations, or in the builtins, or in the functions, or in the warnings, or the files itself could not be parsed!"))
		else: 
			logging.error(color(colors.RED + colors.BOLD, "There were differences in the results of the lemmas or the files itself could not be parsed!"))
		logging.error(f"For more information, run 'diff -r {settings.folderA} {settings.folderB}'")
		return False

	## summary of step and time differences ##
	timeDiv = 100 if timeSumA == 0 else int(100*timeSumB/timeSumA)
	stepDiv = 100 if stepSumA == 0 else int(100*stepSumB/stepSumA)
	timeColor = getColorQuality(timeSumA, timeSumB)
	if (stepSumA == stepSumB):
		stepColor = colors.GREEN
	else:
		stepColor = colors.PINK
	logging.warning("The total amount of time  changed from "+ color(timeColor, f"{int(timeSumA)}s to {int(timeSumB)}s - this is {timeDiv}%"))
	if stepSumA != stepSumB:
		logging.warning("The total amount of steps changed from " + color(stepColor, f"{stepSumA} steps to {stepSumB} steps - this is {stepDiv}%"))
		return False
	else:
		logging.warning("The total amount of steps did not change")
	if settings.verbose >= 3: 
		logging.warning("The rules did not change")
		logging.warning("The functions did not change")
		logging.warning("The builtins did not change")
		logging.warning("The config blocks did not change")
		logging.warning("The equations did not change")
		logging.warning("The macros did not change")
		logging.warning("The warnings did not change")
	return True



def getArguments():

	## set up argparse ##
	parser = argparse.ArgumentParser(formatter_class=argparse.RawTextHelpFormatter)
	parser.add_argument("-s", "--slow", help = "Run all (not only fast) tests", action="store_true")
	parser.add_argument("-noi", "--no-install", help = "Do not call 'stack install' before starting the tests", action="store_true")
	parser.add_argument("-nom", "--no-make", help = "Do not run regression tests, i.e., do not call 'make case-studies'", action="store_true")
	parser.add_argument("-j", "--jobs", help = "The amount of Tamarin instances used simultaneously. Each Tamarin instance should have 3 threads and 16GB RAM available", type=int, default=1)
	parser.add_argument("-d", "--directory", help = "The directory to compare the test results with. The default is case-studies-regression", type=str, default="case-studies-regression")
	parser.add_argument("-r", "--repeat", help = "Repeat everything r times (except for 'stack install'). This gives more confidence in time measurements", type=int, default=1)
	parser.add_argument("-v", "--verbose", 
		help="Level of verbosity, values are from 0 to 6. Default is 3\n" +
			"0: show only critical error output and changes of verified vs. trace found\n" +
			"1: show summary of time and step differences\n" +
			"2: show step differences for changed lemmas\n" +
			"3: show step differences for changed lemmas and changed functions, rules, equations, warning, builtins and macros\n" +
			"4: show time differences for all lemmas\n" +
			"5: show shell command output\n" +
			"6: show diff output if the corresponding proofs changed"
			, type=int, default=3)
	parser.add_argument("-p", "--parser-test", help = "Run the parser tests.", action="store_true")
	parser.add_argument("-nopt", "--no-output-parse-test", help="Skip testing if output files can be parsed again", action="store_true")
	parser.add_argument("--no-sapic-output-parse-test", dest="no_sapic_output_parse_test", help="Disable SAPIC/accountability output parse tests", action="store_true")
	

	## save the settings ##
	global settings
	settings = parser.parse_args()
	settings.folderA = settings.directory
	settings.folderB = "case-studies"

	## Check Verbose ##
	if settings.verbose > 6 or settings.verbose < 0:
		raise argparse.ArgumentError(None, "The level of verbosity must be between 0 and 6 !")

	## set up logging ##
	loglevel = [logging.ERROR, logging.WARNING, logging.INFO, logging.INFO, logging.DEBUG, logging.DEBUG, logging.DEBUG][settings.verbose]
	logging.basicConfig(level=loglevel,format='%(message)s')




def main():
	startTime = datetime.datetime.now() 

	## read command line arguments ##
	getArguments()

	## stack install ##
	if not settings.no_install:
		logging.warning("running 'stack install' ...")
		output = subprocess.check_output("stack install", shell=True, stderr=subprocess.STDOUT).decode("utf-8")
		logging.debug(output)

	## test the spthy parser
	parsingSuccessful = True
	if settings.parser_test:
		logging.info("running the parser tests ...")
		tree_sitter_spthy_dir = './tree-sitter/tree-sitter-spthy'

		working_dir = os.getcwd()

		# change the working dir s.t. we can use tree-sitter CLI
		os.chdir(tree_sitter_spthy_dir)
		
		try:
			testResult = subprocess.run(['./regressionParser.sh'], capture_output=True, text=True)
			tree_sitter_generate = subprocess.run(["tree-sitter", "generate"], capture_output=True, text=True)
			outputColor = colors.GREEN + colors.BOLD

			if not "success percentage: 100.00%;" in testResult.stdout:
				parsingSuccessful = False
				outputColor = colors.RED + colors.BOLD
			logging.error("""\n 
==============================================================
Parser test results:
==============================================================
		""")
			logging.error(color(colors.YELLOW + colors.BOLD, tree_sitter_generate.stdout))
			logging.error(color(colors.RED + colors.BOLD, tree_sitter_generate.stderr))
			logging.error(color(outputColor, testResult.stdout))
			logging.error(color(colors.RED + colors.BOLD, testResult.stderr))

		finally:
		# revert the working dir change s.t. the rest of the script can run correctly
			os.chdir(working_dir)
			
	## repeat case-studies r times for higher confidence in time measurements ##
	successful = True
	for r in range(settings.repeat):
		if (settings.repeat != 1):
			shutil.rmtree(settings.folderB, ignore_errors=True)
			logging.warning("\n" + "="*80 + "\n")
			logging.warning(color(colors.BOLD, f"This is repetition number {r+1}\n"))


		## make case-studies ##
		if not settings.no_make:
			cases = "case-studies" if settings.slow else "fast-case-studies sapic-case-studies-fast FAST=y"
			command = f"make -j {settings.jobs} {cases} 2>/dev/null"
			logging.warning(f"running '{command}' ...")
			output = subprocess.check_output(command, shell=True, stderr=subprocess.STDOUT).decode("utf-8")
			logging.debug(output)

		## compare time and steps ##
		successful = compare() & successful

	successful = successful & parsingSuccessful

	## measure time ##
	logging.warning(f"\nTime elapsed: {str(datetime.datetime.now() - startTime).split('.')[0]}s")
	if not successful:
		exit(1)
	exit(0)

if __name__ == '__main__':
	main()