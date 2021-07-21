
import os
import sys
import posixpath
import argparse
from difflib import SequenceMatcher
import subprocess
from time import time

class bcolors:          # Colors for colorPrint and colorWrite functions
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

# Filenames or directory names
filename = "testoutput.txt"
dirtests = "tests"
pathTmp = "path.tmp"
outTestsErrors = "testsResults_errors.txt"
outTestsTime = "testsResults_time.txt"
finalTime = "testsTimeResults.txt"

CASE_REG_DIR = "case-studies-regression/"
CASE_DIR = "case-studies/"

# Constants used to configure the script
LIMIT_ERROR_LINE = 1            # Resemblance between 2 lines to know if there's an error
OPT_WRITE_FILENAME = True       # Write filename in Err File
OPT_WRITE_ALL_TIMES = False     # Write all times without condition
OPT_TIME_GAP = None             # Time difference allowed
OPT_TIME = True                 # Display of time
EXCEPT_DIR = None               # Remove directories from the comparison
DISPLAY_ERRORS = True           # Display of errors
GRADUATION_TIME = [0.3, 0.8]    # Colorization of processing times
ALLOW_DUPLICATE = False         # Output can't show duplicates by default
OPT_DFF = True                  # Delete final files by default
OPT_ASK = False                 # Won't ask to delete files at the beggining of the script by default. (Not deleting them can corrupt the results)
OPT_NOD = False                 # Option to delete temporary files
OPT_NOM = False                 # Make by default
OPT_NOKEEP = True               # Won't recreate directories with .gitkeep in them by default
NO_DUR = False                  # Show total duration by default

SUCCESS = 0
FAIL = 1

## Pretty print and write ##

def colorPrint(color, text) :
    print(color + text + bcolors.ENDC)

def colorWrite(color, text, file) :
    file.write(color + text + bcolors.ENDC)


## Used to create subfiles when splitting the diff result ##
def files():
    n = 0
    while True:
        n += 1
        yield open(dirtests + '/%d.part' % n, 'w')


## Split a file, remove "diff" display from the main diff command ##
def splitFile(filename) :
    pat = "diff -r"
    if EXCEPT_DIR != None :
        for dir in EXCEPT_DIR :
            pat += " '--exclude=" + dir + "'"   # Each --exclude argument appears in diff command output, we remove them
    fs = files()
    outfile = next(fs) 

    with open(filename) as infile:
        for line in infile:
            if pat not in line:                # If the line does not contain "diff -r '--exclude=...'"
                outfile.write(line)                 # the line is good to be written
            else:                              # Else, we remove it and then we write the line into the file
                items = line.split(pat)
                outfile.write(items[0])
                for item in items[1:]:
                    outfile = next(fs)
                    outfile.write("/* file : " + item.strip().split(" ")[0] + " */\n")

## Return similarity between two strings (from 0 to 1, float) ##
def similar(a, b):
    return SequenceMatcher(None, a, b).ratio()

## Compare two lines. Separate those with processing times from those with errors ##
def compareLines(line1, line2, filename) :
    fileErr = open(outTestsErrors, "a+")
    fileTime = open(outTestsTime, "a+")
    if "processing time" in line1 + line2 :
        colorWrite(bcolors.HEADER, "**" + filename.strip() + "**\n", fileTime)
        colorWrite(bcolors.OKBLUE, line1 + '\n' + line2 + '\n', fileTime)
    elif similar(line1, line2) <= LIMIT_ERROR_LINE :
        colorWrite(bcolors.HEADER, "**" + filename.strip() + "**\n", fileErr)
        colorWrite(bcolors.FAIL, line1 + '\n' + line2 + '\n', fileErr)
    
    fileErr.close()
    fileTime.close()
    

## Parse the file to finally compare lines ##
def processFile(path) :
    file = open(path, "r")
    fileErr = open(outTestsErrors, "a+")
    filename = file.readline()
    listResult = [filename]
    if "Seulement dans" in filename or "Only in" in filename :      # If a file is not either in case-studies or in case-studies-regression
        colorWrite(bcolors.FAIL, filename + '\n', fileErr)
    for line in file :
        if line[0] == "<" or line[0] == ">" :                       # Only take lines that show a "before" or "after" in the output of diff command
            listResult.append(line)
        if "Seulement dans" in line or "Only in" in line :          # If a file is not either in case-studies or in case-studies-regression
            colorWrite(bcolors.FAIL, line + '\n', fileErr)
    for i in range(1,len(listResult)) :
        if listResult[i][0] == "<" and listResult[i+1][0] == ">" :
            compareLines(listResult[i], listResult[i+1], filename)

    fileErr.close()
    file.close()


## Extract the first float from a line. This is used to find processing times ##
def extractFloat(line) :
    l = []
    for t in line.split():
        try:
            l.append(float(t.split('s')[0]))
        except ValueError:
            pass
    return(l)


## Parse the file of processing times and write in another file a pretty version for display ##
def processTimeResults() :
    fileTime = open(outTestsTime, "r")          # This file contains a 5 steps repetition pattern, used below
    finalTimeFile = open(finalTime, "w")

    cpt = 1
    time1 = 0
    time2 = 0
    filename = ""
    for line in fileTime :
        
        if cpt == 1 :                           # Step 1 : First line contains filename
            filename = line
        if cpt == 2 :                           # Step 2 : Second line contains the old/reference processing time
            if line.strip() == "" or extractFloat(line) == []:
                cpt += 1
                continue
            time1 = extractFloat(line)[0]
                                                # Step 3 : An empty line
        if cpt == 4 :                           # Step 4 : Fourth line contains the new processing time
            if line.strip() == "" or extractFloat(line) == [] :
                cpt += 1
                continue
            time2 = extractFloat(line)[0]
        if cpt == 5 :                           # Step 5 : An empty line ==> We now write the old and new processing times into a file
            if time1 == 0 or time2 == 0 :
                print("ERROR : file : " + filename + " contains a null time")
            # In order of importance : show-all-times -> time-gap -> graduation-time. Only one of the third options can be selected.
            elif OPT_WRITE_ALL_TIMES :
                if OPT_WRITE_FILENAME :
                    finalTimeFile.write(filename)
                colorWrite(bcolors.OKBLUE, "old :  " + str(time1) + "s   -->   new :  " + str(time2) + "s\n", finalTimeFile )
            elif OPT_TIME_GAP and abs((time1 - time2)/time1) >= OPT_TIME_GAP :
                if OPT_WRITE_FILENAME :
                    finalTimeFile.write(filename)
                colorWrite(bcolors.FAIL, "old :  " + str(time1) + "s   -->   new :  " + str(time2) + "s\n", finalTimeFile )
            elif GRADUATION_TIME :
                if OPT_WRITE_FILENAME :
                    finalTimeFile.write(filename)
                if abs((time1 - time2)/time1) <= GRADUATION_TIME[0] :
                    colorWrite(bcolors.OKGREEN, "old :  " + str(time1) + "s   -->   new :  " + str(time2) + "s\n", finalTimeFile)
                elif GRADUATION_TIME[0] < abs((time1 - time2)/time1) <= GRADUATION_TIME[1] :
                    colorWrite(bcolors.WARNING, "old :  " + str(time1) + "s   -->   new :  " + str(time2) + "s\n", finalTimeFile)
                elif GRADUATION_TIME[1] < abs((time1 - time2)/time1) :
                    colorWrite(bcolors.FAIL, "old :  " + str(time1) + "s   -->   new :  " + str(time2) + "s\n", finalTimeFile)

            cpt = 0
        cpt += 1

    fileTime.close()
    finalTimeFile.close()
        

## Take a file and create another file avoiding repetition of lines ##
def uniqLines(infilename, outfilename) :
    lines_seen = set()
    outfile = open(outfilename, "w")
    unwantedChars = [chr(int("0x1b", 16)),"[0m","[95m","[91m3"] # These chars are used in colors. We only want to compare text and not color+text.
    tmpline = ""
    for line in open(infilename, "r") :
        tmpline = line
        for char in unwantedChars :
    	    tmpline = tmpline.replace(char, "")
        if tmpline not in lines_seen :
            outfile.write(line)
            lines_seen.add(tmpline)
    outfile.close()

## Ask the user a Y/N question ##
def queryYesNo(question, default="yes"):
    valid = {"yes": True, "y": True, "ye": True, "no": False, "n": False}
    if default is None:
        prompt = " [y/n] "
    elif default == "yes":
        prompt = " [Y/n] "
    elif default == "no":
        prompt = " [y/N] "
    else:
        raise ValueError("invalid default answer: '%s'" % default)

    while True:
        sys.stdout.write(question + prompt)
        choice = input().lower()
        if default is not None and choice == "":
            return valid[default]
        elif choice in valid:
            return valid[choice]
        else:
            sys.stdout.write("Please respond with 'yes' or 'no' " "(or 'y' or 'n').\n")




def main() :    

    t1 = time()

    ## Parse command line arguments ##

    parser = argparse.ArgumentParser()
    parser.add_argument("-f", "--fast", help = "Run fast tests", action="store_true")
    parser.add_argument("-ed","--except-dir", help = "Run script ignoring a file/directory (csv format for two or more files/directories", type=str)
    parser.add_argument("-grad","--time-graduation", help = "2 csv thresholds (Default : -grad=0.3,0.8) to color processing times (from 0 to 1). Do not combine this argument with -t.")
    parser.add_argument("-nofn","--without-filename", help="Output time file won't contain filenames",
                    action="store_true")
    parser.add_argument("-nom", "--no-make", help = "No make will be used. Only use it if your working directories are already created.", action="store_true")
    parser.add_argument("-showt","--show-all-times", help="Output files will contain all processing times without condition",
                    action="store_true")
    parser.add_argument("-t","--time-gap", help="Time difference (percentage) allowed (from 0 to 1)", type=float)
    parser.add_argument("-notime","--without-times", help="Don't compute processing times",
                    action="store_true")
    parser.add_argument("-node", "--no-display-errors", help = "Won't display errors", action="store_true")
    parser.add_argument("-dup", "--allow-duplicate", help = "Keep duplicates from output display", action="store_true")
    parser.add_argument("-lel","--limit-error-line", help="Acceptable resemblance between two lines (from 0 to 1). Default = 1 (perfect match)", type=float)
    parser.add_argument("-nodf", "--no-delete-final-files", help = "Won't delete final files (Debug)", action="store_true")
    parser.add_argument("-ask", "--ask-for-deletions", help = "Ask Y/N questions to delete existing files at the beginning of the script to overwrite them. Not deleting them can compromise the results. Default behaviour delete existing files without asking", action="store_true")
    parser.add_argument("-wkeep", "--with-git-keep", help = "Recreate empty directories with .gitkeep in them", action="store_true")
    parser.add_argument("-d", "--debug", help = "Run in debug mode. (Temporary files won't be deleted)", action="store_true")
    parser.add_argument("-nodur", "--no-display-duration", help = "Won't display the total duration of the script", action="store_true")

    args = parser.parse_args()
    
    ## Define global variables depending on command line arguments ##

    listOfGlobals = globals()
    if args.limit_error_line :
        listOfGlobals["LIMIT_ERROR_LINE"] = args.limit_error_line
    if args.without_filename :
        listOfGlobals["OPT_WRITE_FILENAME"] = False
    if args.show_all_times :
        listOfGlobals["OPT_WRITE_ALL_TIMES"] = True
    if args.time_gap and args.time_graduation :
        colorPrint(bcolors.FAIL, "Do not combine time graduation with time gap argument.")
        exit(1)
    if args.time_gap :
        listOfGlobals["OPT_TIME_GAP"] = args.time_gap
    if args.without_times :
        listOfGlobals["OPT_TIME"] = False
    if args.except_dir :
        listOfGlobals["EXCEPT_DIR"] = args.except_dir.split(",")
    if args.no_display_errors :
        listOfGlobals["DISPLAY_ERRORS"] = False
    if args.time_graduation :
        list = args.time_graduation.split(",")
        listOfGlobals["GRADUATION_TIME"] = [float(list[0]),float(list[1])]
    if args.allow_duplicate :
        listOfGlobals["ALLOW_DUPLICATE"] = True
    if args.fast :
        listOfGlobals["CASE_DIR"] = "case-studies/fast-tests/"
        listOfGlobals["CASE_REG_DIR"] = "case-studies-regression/fast-tests/"
    if args.no_delete_final_files :
        listOfGlobals["OPT_DFF"] = False
    if args.ask_for_deletions :
        listOfGlobals["OPT_ASK"] = True
    if args.no_make :
        listOfGlobals["OPT_NOM"] = True
    if args.with_git_keep :
        listOfGlobals["OPT_NOKEEP"] = False
    if args.debug :
        listOfGlobals["OPT_DFF"] = False
        listOfGlobals["OPT_NOD"] = True
    if args.no_display_duration :
        listOfGlobals["NO_DUR"] = True


    ## Init ##

    if not os.path.exists(dirtests):
        os.makedirs(dirtests)

    colorPrint(bcolors.HEADER, "** Tests for Tamarin Prover **")


    ## Check if files used in the script exist because it can corrupt the results ##


    filesList = [outTestsTime, outTestsErrors, pathTmp, filename, finalTime]
    for fn in filesList :
        if os.path.exists(fn) :
            if not OPT_ASK :
                os.system("rm " + fn)
            elif queryYesNo("File " + fn + " already exists. It may compromise your results. Do you want to delete it ?") :
                os.system("rm " + fn)


    ## Make case studies ##

    if not OPT_NOM :
        if args.fast :
            makeOut = subprocess.run("make fast-case-studies FAST=y 2>/dev/null", shell=True)
            if makeOut.returncode != 0 :
                colorPrint(bcolors.FAIL, "Make failed with return code " + str(makeOut.returncode))
                exit(1)
        else :
            makeOut = subprocess.run("make case-studies 2>/dev/null", shell=True)
            if makeOut.returncode != 0 :
                colorPrint(bcolors.FAIL, "Make failed with return code " + str(makeOut.returncode))
                exit(1)
    
    
    ## Put all diff result in a file and format it into multiple files in a tmp directory ##


    excluded = ""
    if args.except_dir :
        for dir in EXCEPT_DIR :
            excluded += " '--exclude=" + dir + "' "
    if not args.fast :
            excluded += " '--exclude=case-studies/fast-tests/' "
            excluded += " '--exclude=case-studies-regression/fast-tests/' "
            if EXCEPT_DIR and not "case-studies/fast-tests/" in EXCEPT_DIR :
                EXCEPT_DIR.append("case-studies/fast-tests/")
            if EXCEPT_DIR and not "case-studies-regression/fast-tests/" in EXCEPT_DIR :
                EXCEPT_DIR.append("case-studies-regression/fast-tests/")

    diffOut = subprocess.run("diff " + CASE_REG_DIR + " " + CASE_DIR + " -r " + excluded + " > " + filename, shell=True)
    if diffOut.returncode == 0 or diffOut.returncode > 1 : # 0 if same files which normally shouldn't happen (because of processing times) and > 1 if errors
        colorPrint(bcolors.FAIL, "Diff failed with return code " + str(diffOut.returncode))
        exit(1)
    splitFile(filename)
    

    ## Recover split files and create a file for errors and a file for processing times ##

    os.system("ls " + dirtests + " > " + pathTmp)

    paths = open(pathTmp,"r")
    for line in paths :
        path = line.strip('\n')
        if path != "" :
            processFile("tests/" + path)

    paths.close()
    

    ## Create a file with processing times before and after ##

    if OPT_TIME :
        processTimeResults()


    ## Displays ##
 

    if OPT_TIME :
        if not ALLOW_DUPLICATE :
            infn = finalTime
            outfn = "times.tmp"
            uniqLines(infn, outfn)
            os.system("cat " + outfn)
            os.system("rm " + outfn)
        else :
            os.system("cat " + finalTime)        

    if DISPLAY_ERRORS :
        os.system("cat " + outTestsErrors)


    if not NO_DUR :
        t = time() - t1
        colorPrint(bcolors.OKCYAN, "Total computation time : " + str(t) + "s (around "+str(round(t/60,3)) + " min)")

    ## Add .gitkeep to folders to make travis work ##
    
    if not OPT_NOKEEP :
        os.system("find case-studies/* -type d > directories.tmp")
        os.system("touch case-studies/.gitkeep")
        for dir in open("directories.tmp") :
            os.system("touch " + dir.strip() + "/.gitkeep")
        os.system("rm directories.tmp")

        os.system("rm -rf " + dirtests)
        if not os.path.exists(dirtests):
            os.makedirs(dirtests)
        os.system("touch " + dirtests + "/.gitkeep")
    elif not OPT_NOD :
        os.system("rm -rf " + dirtests)

    ## Remove useless files ##
    
    if not OPT_NOD :
        os.system("rm " + outTestsTime)
        os.system("rm " + pathTmp)
        os.system("rm " + filename)
    
    ## And check for errors ##

    nbrLines = sum(1 for line in open(outTestsErrors))
    if nbrLines == 0 :                                  # if no errors
        colorPrint(bcolors.BOLD,"All tests passed !")
        if not OPT_NOD :
            os.system("rm " + outTestsErrors)
        if OPT_DFF and OPT_TIME and not OPT_NOD :
            os.system("rm " + finalTime)
        exit(SUCCESS)
    else :
        colorPrint(bcolors.BOLD, "Tests failed with " + str(nbrLines) + " error lines")
        if OPT_DFF and not OPT_NOD :
            os.system("rm " + outTestsErrors)
            if OPT_TIME :
                os.system("rm " + finalTime)
        exit(FAIL)

    
main()