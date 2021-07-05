
import os
import sys
import posixpath
import argparse
from difflib import SequenceMatcher


class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

filename = "testoutput.txt"
dirtests = "tests"
pathTmp = "path.tmp"
outTestsErrors = "testsResults_errors.txt"
outTestsTime = "testsResults_time.txt"
finalTime = "testsTimeResults.txt"


CASE_REG_DIR = "case-studies-regression/"
CASE_DIR = "case-studies/"

LIMIT_ERROR_LINE = 1            # Resemblance between 2 lines to know if there's an error
OPT_WRITE_FILENAME = True       # Write filename in Err File
OPT_WRITE_ALL_TIMES = False     # Write all times without condition
OPT_TIME_GAP = 0.2              # Time difference allowed
OPT_TIME = True                 # Display of time
EXCEPT_DIR = None
DISPLAY_TIMES = False
DISPLAY_ERRORS = False
GRADUATION_TIME = None
NO_DUPLICATE = False
OPT_DFF = False
OPT_YES = False
OPT_NOD = False

SUCCESS = 0
FAIL = -1

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
    pat = "diff -r '--color=never'"
    if EXCEPT_DIR != None :
        for dir in EXCEPT_DIR :
            pat += " '--exclude=" + dir + "'"
    fs = files()
    outfile = next(fs) 

    with open(filename) as infile:
        for line in infile:
            if pat not in line:
                outfile.write(line)
            else:
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
    filename = file.readline()
    listResult = [filename]
    for line in file :
        if line[0] == "<" or line[0] == ">" :
            listResult.append(line)

    for i in range(1,len(listResult)) :
        if listResult[i][0] == "<" and listResult[i+1][0] == ">" :
            compareLines(listResult[i], listResult[i+1], filename)

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
    fileTime = open(outTestsTime, "r")
    finalTimeFile = open(finalTime, "w")

    cpt = 1
    time1 = 0
    time2 = 0
    filename = ""
    for line in fileTime :
        
        if cpt == 1 :
            filename = line
        if cpt == 2 :
            if line.strip() == "" or extractFloat(line) == []:
                cpt += 1
                continue
            time1 = extractFloat(line)[0]
        if cpt == 4 :
            if line.strip() == "" or extractFloat(line) == [] :
                cpt += 1
                continue
            time2 = extractFloat(line)[0]
        if cpt == 5 :
            if OPT_TIME :
                if time1 == 0 or time2 == 0 :
                    print("ERROR : file : " + filename + " contains a null time")
                elif OPT_WRITE_ALL_TIMES :
                    if OPT_WRITE_FILENAME :
                        finalTimeFile.write(filename)
                    colorWrite(bcolors.OKBLUE, "1old :  " + str(time1) + "s   -->   new :  " + str(time2) + "s\n", finalTimeFile )
                elif GRADUATION_TIME :
                    if OPT_WRITE_FILENAME :
                        finalTimeFile.write(filename)
                    if abs((time1 - time2)/time1) <= GRADUATION_TIME[0] :
                        colorWrite(bcolors.OKGREEN, "2old :  " + str(time1) + "s   -->   new :  " + str(time2) + "s\n", finalTimeFile)
                    elif GRADUATION_TIME[0] < abs((time1 - time2)/time1) <= GRADUATION_TIME[1] :
                        colorWrite(bcolors.WARNING, "2old :  " + str(time1) + "s   -->   new :  " + str(time2) + "s\n", finalTimeFile)
                    elif GRADUATION_TIME[1] < abs((time1 - time2)/time1) :
                        colorWrite(bcolors.FAIL, "2old :  " + str(time1) + "s   -->   new :  " + str(time2) + "s\n", finalTimeFile)
                elif abs((time1 - time2)/time1) >= OPT_TIME_GAP :
                    if OPT_WRITE_FILENAME :
                        finalTimeFile.write(filename)
                    colorWrite(bcolors.FAIL, "3old :  " + str(time1) + "s   -->   new :  " + str(time2) + "s\n", finalTimeFile )
            cpt = 0
        cpt += 1
        

## Take a file and create another file avoiding repetition of lines ##
def uniqLines(infilename, outfilename) :
    lines_seen = set()
    outfile = open(outfilename, "w")
    unwantedChars = [chr(int("0x1b", 16)),"[0m","[95m","[91m3"]
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

    ## Parse command line arguments ##

    parser = argparse.ArgumentParser()
    parser.add_argument("-lel","--limit-error-line", help="Acceptable resemblance between two lines (from 0 to 1). Default = 1 (100% resemblance)", type=float)
    parser.add_argument("-nofn","--without-filename", help="Output time file won't contain filenames",
                    action="store_true")
    parser.add_argument("-showt","--show-all-times", help="Output files will contain all processing times without condition",
                    action="store_true")
    parser.add_argument("-t","--time-gap", help="Time difference (percentage) allowed (from 0 to 1)", type=float)
    parser.add_argument("-notime","--without-times", help="Don't compute processing times",
                    action="store_true")
    parser.add_argument("-ed","--except-dir", help = "Run script ignoring a file/directory (csv format for two or more files/directories", type=str)
    parser.add_argument("-dt","--display-times", help = "Display a comparison of processing times", action="store_true")
    parser.add_argument("-de", "--display-errors", help = "Display all errors", action="store_true")
    parser.add_argument("-grad","--time-graduation", help = "2 csv thresholds (e.g. -grad=0.3,0.8) to color processing times (from 0 to 1). Do not combine this argument with -t.")
    parser.add_argument("-nodup", "--no-duplicate", help = "Remove duplicates from output display", action="store_true")
    parser.add_argument("-f", "--fast", help = "Run fast tests", action="store_true")
    parser.add_argument("-dff", "--delete-final-files", help = "Delete final files to keep a proper working directory", action="store_true")
    parser.add_argument("-yes", "--accept-recommanded-deletions", help = "Delete existing files at the beginning of the script to overwrite them. Not deleting them can compromise the results.", action="store_true")
    parser.add_argument("-nod", "--no-delete", help = "Temporary files won't be deleted", action="store_true")

    args = parser.parse_args()
    
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
    if args.display_times :
        listOfGlobals["DISPLAY_TIMES"] = True
    if args.display_errors :
        listOfGlobals["DISPLAY_ERRORS"] = True
    if args.time_graduation :
        list = args.time_graduation.split(",")
        listOfGlobals["GRADUATION_TIME"] = [float(list[0]),float(list[1])]
    if args.no_duplicate :
        listOfGlobals["NO_DUPLICATE"] = True
    if args.fast :
        listOfGlobals["CASE_DIR"] = "case-studies/fast-tests/"
        listOfGlobals["CASE_REG_DIR"] = "case-studies-regression/fast-tests/"
    if args.delete_final_files :
        listOfGlobals["OPT_DFF"] = True
    if args.accept_recommanded_deletions :
        listOfGlobals["OPT_YES"] = True
    if args.no_delete :
        listOfGlobals["OPT_NOD"] = True

    ## Init ##

    if not os.path.exists(dirtests):
        os.makedirs(dirtests)

    colorPrint(bcolors.HEADER, "** Tests for Tamarin Prover **")


    ## Check if files used in the script exist because it can corrupt the results ##


    filesList = [outTestsTime, outTestsErrors, pathTmp, filename, finalTime]
    for fn in filesList :
        if os.path.exists(fn) :
            if OPT_YES :
                os.system("rm " + fn)
            elif queryYesNo("File " + fn + " already exists. It may compromise your results. Do you want to delete it ?") :
                os.system("rm " + fn)



    ## Put all diff result in a file and format it into multiple files in a tmp directory ##

    #os.system("make case-studies") #TODO uncomment
    excluded = ""
    if args.except_dir :
        for dir in EXCEPT_DIR :
            excluded += " '--exclude=" + dir + "' "
    if not args.fast :
            excluded += " '--exclude=case-studies/fast-tests/' "
            excluded += " '--exclude=case-studies-regression/fast-tests/' "
            if not "case-studies/fast-tests/" in EXCEPT_DIR :
                EXCEPT_DIR.append("case-studies/fast-tests/")
            if not "case-studies-regression/fast-tests/" in EXCEPT_DIR :
                EXCEPT_DIR.append("case-studies-regression/fast-tests/")

    os.system("diff " + CASE_REG_DIR + " " + CASE_DIR + " -r --color=never " + excluded + " > " + filename) 

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

    processTimeResults()

    ## Displays ##
 

    if DISPLAY_TIMES :
        if NO_DUPLICATE :
            infn = finalTime
            outfn = "times.tmp"
            uniqLines(infn, outfn)
            os.system("cat " + outfn)
            os.system("rm " + outfn)
        else :
            os.system("cat " + finalTime)        

    if DISPLAY_ERRORS :
        os.system("cat " + outTestsErrors)

    ## Remove useless files ##
    
    if not OPT_NOD :
        os.system("rm -rf " + dirtests)
        os.system("rm " + outTestsTime)
        os.system("rm " + pathTmp)
        os.system("rm " + filename)
    

    nbrLines = sum(1 for line in open(outTestsErrors))
    if nbrLines == 0 :                                  # if no errors
        colorPrint(bcolors.BOLD,"All tests passed !")
        if not OPT_NOD :
            os.system("rm " + outTestsErrors)
        if OPT_DFF and not OPT_NOD :
            os.system("rm " + finalTime)
        return SUCCESS
    else :
        print("Tests failed with " + str(nbrLines) + " lines")
        if OPT_DFF and not OPT_NOD :
            os.system("rm " + outTestsErrors)
            os.system("rm " + finalTime)
        return FAIL

    



if __name__ == "__main__" :
    main()