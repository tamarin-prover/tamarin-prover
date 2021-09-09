import subprocess, sys, re, os, argparse, logging

folderA = "case-studies-regression"
folderB = "case-studies"



class colors:          # Colors for colorPrint and colorWrite functions
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
	for dname, dirs, files in os.walk(folder):
		for fname in files:
			fpath = os.path.join(dname, fname)
			if not fpath.endswith(".spthy"):
				continue
			yield fpath



def parseFile(path):
	content = ""
	try:
		with open(path) as f:
			content = f.read().split("summary of summaries")[-1]
	except Exception:
		return f"There was an error while reading {path}"

	try:
		times = re.findall(r"processing time: (.*)s", content)
		if len(times) != 1:
			return f"Parse error - time: {path}"
		parsed = re.findall(r"(\w+) \(.*\): (.*) \((\d+) steps\)\n", content)
		parsed = [(lemmas, res=="verified", int(steps)) for (lemmas, res, steps) in parsed]
		parsed = list(zip(*parsed))
		if (parsed == []):
			return ([],[],[], float(times[0]))
		else:
			return (parsed[0], parsed[1], parsed[2], float(times[0]))
	except Exception as ex:
		raise ex
		return f"Parse error - lemmas: {path}"



def parseFiles(pathB):

	## infer regression path name pathA from pathB ##
	pathA = folderA + pathB.strip(folderB)

	## parse files ##
	parsedB = parseFile(pathB)
	if type(parsedB) == str:
		return parsedB
	parsedA = parseFile(pathA)
	if type(parsedA) == str:
		return parsedA
	(lemmasA, resA, stepsA, timeA) = parsedA
	(lemmasB, resB, stepsB, timeB) = parsedB

	## check compatibility ##
	if lemmasA != lemmasB:
		return f"The lemmas for {pathA} cannot be compared, they are different."

	return (lemmasA, resA, resB, stepsA, stepsB, timeA, timeB)



def compare():
	resultsDiffer = False
	stepSumA, stepSumB, timeSumA, timeSumB = 0, 0, 0, 0

	for pathB in iterFolder(folderB):

		## parse file ##
		parsed = parseFiles(pathB)
		if type(parsed) == str:
			logging.error(color(colors.RED + colors.BOLD, parsed))
			continue
		(lemmas, resA, resB, stepsA, stepsB, timeA, timeB) = parsed

		## results differ ##
		if resA != resB:
			logging.error(color(colors.RED, pathB))
			for i in range(len(lemmas)):
				if resA[i] != resB[i]:
					logging.error(color(colors.RED + colors.BOLD, f"The result changed from {resA[i]} to {resB[i]} in {lemmas[i]}"))
			resultsDiffer = True
			continue

		## compare steps and times ##
		if stepsA != stepsB and settings.verbose < 3:
			logging.info(pathB)
		timeColor = getColorQuality(timeA, timeB)
		logging.debug("The time changed from " + color(timeColor, f"{str(timeA).rjust(16)}s to {str(timeB).rjust(16)}s") + f" in {pathB}")
		for i in range(len(lemmas)):
			if stepsA[i] != stepsB[i]:
				logging.info("The step count changed from " + color(colors.PINK, f"{str(stepsA[i]).rjust(5)} steps to {str(stepsB[i]).rjust(11)} steps") + f" in {lemmas[i]}")

		## aggregate the results ##
		stepSumA += sum(stepsA)
		stepSumB += sum(stepsB)
		timeSumA += timeA
		timeSumB += timeB

	## results differ ##
	logging.warning("\n" + "="*80 + "\n")
	if resultsDiffer:
		logging.error(color(colors.RED + colors.BOLD, "There were differences in the results of the lemmas!"))
		logging.error(f"For more information, run 'diff -r {folderA} {folderB}'")
		return False

	## summary of step and time differences ##
	timeDiv = 100 if timeSumA == 0 else int(100*timeSumB/timeSumA)
	stepDiv = 100 if stepSumA == 0 else int(100*stepSumB/stepSumA)
	timeColor = getColorQuality(timeSumA, timeSumB)
	if (stepSumA == stepSumB):
		stepColor = colors.GREEN
	else:
		stepColor = colors.PINK
	logging.warning("The total amount of time  changed from "+ color(timeColor, f"{timeSumA} to {timeSumB} - this is {timeDiv}%"))
	if stepSumA != stepSumB:
		logging.warning("The total amount of steps changed from " + color(stepColor, f"{stepSumA} steps to {stepSumB} steps - this is {stepDiv}%"))
		return False
	return True



def getArguments():
	## set up argparse ##
	parser = argparse.ArgumentParser()
	parser.add_argument("-s", "--slow", help = "Run all (not only fast) tests", action="store_true")
	parser.add_argument("-noi", "--no-install", help = "Do not call 'stack install' before starting the tests", action="store_true")
	parser.add_argument("-nor", "--no-regression", help = "Regression tests won't be run, i.e., 'make case-studies' is not called.", action="store_true")
	parser.add_argument("-j", "--jobs", help = "The amount of Tamarin instances used simultaneously; Each Tamarin instance should have 3 threads and 16GB RAM available.", type=int, default=1)
	parser.add_argument("-v", "--verbose", 
		help="Level of verbosity, values are: 0 1 2 3. Default is 1\n" +
			"0: show only critical error output and changes of verified vs. trace found\n" +
			"1: show summary of time and step differences\n" +
			"2: show step differences for changed lemmas\n" +
			"3: show time differences for all lemmas"
			, type=int, default=1)
	global settings
	settings = parser.parse_args()

	## set up logging ##
	loglevel = [logging.ERROR, logging.WARNING, logging.INFO, logging.DEBUG][settings.verbose]
	logging.basicConfig(level=loglevel,format='%(message)s')





def main():

	## read command line arguments ##
	getArguments()

	## stack install ##
	if not settings.no_install:
		logging.warning("running 'stack install' ...")
		subprocess.check_output("stack install", shell=True).decode("utf-8")

	## make case-studies ##
	if not settings.no_regression:
		cases = "case-studies" if settings.slow else "fast-case-studies FAST=y"
		command = f"make -j {settings.jobs} {cases} 2>/dev/null"
		logging.warning(f"running '{command}' ...")
		makeOut = subprocess.check_output(command, shell=True)

	## measure time and steps ##
	if compare() == False:
		exit(1)
	else:
		exit(0)



if __name__ == '__main__':
	main()

