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



def parseFile(path):
	"""
	Parses a _analyzed.spthy file and returns their content in a tuple

	(lemmas([str]), results([bool]), steps([int]), time(float), proof)
	Note that time is not a list but a single value.
	If there is an error, the error message is returned as a string
	"""

	## open file ##
	summary = ""
	try:
		with open(path) as f:
			# strip everything before the summary part
			allContent = f.read().split("summary of summaries")
			summary = allContent[-1]
			proof = allContent[0].split("------------------------------------------------------------------------------")[0]
	except Exception:
		return f"There was an error while reading {path}"

	## parse time ##
	times = re.findall(r"processing time: (.*)s", summary)
	if len(times) != 1:
		return f"Parse error - time: {path}"

	## parse lemmas ##
	try:
		parsed = re.findall(r"(\w+) (?:\(.*\))?:(?!  ) (.*) \((\d+) steps\)\n", summary)
		parsed = [(lemmas, res=="verified", int(steps)) for (lemmas, res, steps) in parsed]  # convert types
		parsed = list(zip(*parsed))             # transpose matrix
		if (parsed == []): parsed = [[],[],[]]  #
		return (parsed[0], parsed[1], parsed[2], float(times[0]), proof)

	except Exception as ex:
		return f"Parse error - lemmas: {path}"



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
	(lemmasA, resA, stepsA, timeA, proofA) = parsedA
	(lemmasB, resB, stepsB, timeB, proofB) = parsedB

	## check compatibility ##
	if lemmasA != lemmasB:
		return f"The lemmas for {pathA} cannot be compared, they are different."

	return (lemmasA, resA, resB, stepsA, stepsB, timeA, timeB, proofA, proofB)



def compare():
	"""
	Searches for all files in case-studies for the corresponding file in case-studies-regression.
	If this search fails, it gives an error message and continues.
	Otherwise, it outputs changed values depending on the verbosity.
	At the end, it outputs a summary
	"""


	majorDifferences = False
	stepSumA, stepSumB, timeSumA, timeSumB = 0, 0, 0, 0

	for pathB in iterFolder(settings.folderB):

		## parse file ##
		parsed = parseFiles(pathB)
		if type(parsed) == str:
			logging.error(color(colors.RED + colors.BOLD, parsed))
			majorDifferences = True
			continue
		(lemmas, resA, resB, stepsA, stepsB, timeA, timeB, proofA, proofB) = parsed

		## proofs differ ##
		if proofA != proofB:
			if settings.verbose >= 5:
				pathA = settings.folderA + pathB.split(settings.folderB, 1)[-1]
				command = f"diff {pathA} {pathB} || :"
				output = subprocess.check_output(command, shell=True).decode("utf-8")
				logging.debug(output.split("\n<   processing time")[0])


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
		if stepsA != stepsB and settings.verbose < 3:
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
		help="Level of verbosity, values are from 0 to 5. Default is 2\n" +
			"0: show only critical error output and changes of verified vs. trace found\n" +
			"1: show summary of time and step differences\n" +
			"2: show step differences for changed lemmas\n" +
			"3: show time differences for all lemmas\n" +
			"4: show shell command output\n" +
			"5: show diff output if the corresponding proofs changed"
			, type=int, default=2)

	## save the settings ##
	global settings
	settings = parser.parse_args()
	settings.folderA = settings.directory
	settings.folderB = "case-studies"

	## set up logging ##
	loglevel = [logging.ERROR, logging.WARNING, logging.INFO, logging.DEBUG, logging.DEBUG, logging.DEBUG][settings.verbose]
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
			
	## repeat case-studies r times for higher confidence in time measurements ##
	successful = True
	for r in range(settings.repeat):
		if (settings.repeat != 1):
			shutil.rmtree(settings.folderB, ignore_errors=True)
			logging.warning("\n" + "="*80 + "\n")
			logging.warning(color(colors.BOLD, f"This is repetition number {r+1}\n"))


		## make case-studies ##
		if not settings.no_make:
			cases = "case-studies" if settings.slow else "fast-case-studies FAST=y"
			command = f"make -j {settings.jobs} {cases} 2>/dev/null"
			logging.warning(f"running '{command}' ...")
			output = subprocess.check_output(command, shell=True, stderr=subprocess.STDOUT).decode("utf-8")
			logging.debug(output)

		## compare time and steps ##
		successful = compare() & successful

	## measure time ##
	logging.warning(f"\nTime elapsed: {str(datetime.datetime.now() - startTime).split('.')[0]}s")
	if not successful:
		exit(1)
	exit(0)

if __name__ == '__main__':
	main()

