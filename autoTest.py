
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



LIMIT_ERROR_LINE = 1            # Resemblance between 2 lines to know if there's an error
OPT_WRITE_FILENAME = True       # Write filename in Err File
OPT_WRITE_ALL_TIMES = False     # Write all times without condition
OPT_TIME_GAP = 0.2              # Time difference allowed
OPT_TIME = True                 # Display of time
EXCEPT_DIR = None
DISPLAY_TIMES = False
DISPLAY_ERRORS = False
GRADUATION_TIME = [0.2, 0.7]
NO_DUPLICATE = False

SUCCESS = 0
FAIL = -1

def colorPrint(color, text) :
    print(color + text + bcolors.ENDC)

def colorWrite(color, text, file) :
    file.write(color + text + bcolors.ENDC)


def files():
    n = 0
    while True:
        n += 1
        yield open(dirtests + '/%d.part' % n, 'w')


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

def similar(a, b):
    return SequenceMatcher(None, a, b).ratio()


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
    


def processListResult(listResult, filename) :

    for i in range(1,len(listResult)) :
        if listResult[i][0] == "<" and listResult[i+1][0] == ">" :
            compareLines(listResult[i], listResult[i+1], filename)

    


def processFile(path) :
    file = open(path, "r")
    filename = file.readline()
    listResult = [filename]
    for line in file :
        if line[0] == "<" or line[0] == ">" :
            listResult.append(line)

    processListResult(listResult, filename)
    file.close()



def extractFloat(line) :
    l = []
    for t in line.split():
        try:
            l.append(float(t.split('s')[0]))
        except ValueError:
            pass
    return(l)

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
                if OPT_WRITE_FILENAME :
                    finalTimeFile.write(filename)
                if time1 == 0 or time2 == 0 :
                    print("ERROR : file : " + filename + " contains a null time")
                elif OPT_WRITE_ALL_TIMES :
                    colorWrite(bcolors.OKBLUE, "old :  " + str(time1) + "s   -->   new :  " + str(time2) + "s\n", finalTimeFile )
                elif GRADUATION_TIME :
                    if abs((time1 - time2)/time1) <= GRADUATION_TIME[0] :
                        colorWrite(bcolors.OKGREEN, "old :  " + str(time1) + "s   -->   new :  " + str(time2) + "s\n", finalTimeFile)
                    elif GRADUATION_TIME[0] < abs((time1 - time2)/time1) <= GRADUATION_TIME[1] :
                        colorWrite(bcolors.WARNING, "old :  " + str(time1) + "s   -->   new :  " + str(time2) + "s\n", finalTimeFile)
                    elif GRADUATION_TIME[1] < abs((time1 - time2)/time1) :
                        colorWrite(bcolors.FAIL, "old :  " + str(time1) + "s   -->   new :  " + str(time2) + "s\n", finalTimeFile)
                elif abs((time1 - time2)/time1) >= OPT_TIME_GAP :
                    colorWrite(bcolors.FAIL, "old :  " + str(time1) + "s   -->   new :  " + str(time2) + "s\n", finalTimeFile )
            cpt = 0
        cpt += 1
        

def uniqLines(infilename, outfilename) :
    lines_seen = set()
    outfile = open(outfilename, "w")
    for line in open(infilename, "r"):
        if line not in lines_seen :
            outfile.write(line)
            lines_seen.add(line)
    outfile.close()


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
    parser.add_argument("-lel","--limit-error-line", help="acceptable resemblance between two lines (from 0 to 1). ", type=float)
    parser.add_argument("-nofn","--without-filename", help="output time file won't contain filenames",
                    action="store_true")
    parser.add_argument("-showt","--show-all-times", help="output files will contain all processing times without condition",
                    action="store_true")
    parser.add_argument("-t","--time-gap", help="time difference allowed (from 0 to 1)", type=float)
    parser.add_argument("-notime","--without-times", help="increase output verbosity",
                    action="store_true")
    parser.add_argument("-ed","--except-dir", help = "run script ignoring a file/directory (csv format for two or more files/directories", type=str)
    parser.add_argument("-dt","--display-times", help = "display a comparison of processing times", action="store_true")
    parser.add_argument("-de", "--display-errors", help = "display all errors", action="store_true")
    parser.add_argument("-grad","--time-graduation", help = "2 csv thresholds to color processing times (from 0 to 1)")
    parser.add_argument("-nodup", "--no-duplicate", help = "remove duplicates from output display", action="store_true")

    args = parser.parse_args()
    
    listOfGlobals = globals()
    if args.limit_error_line :
        listOfGlobals["LIMIT_ERROR_LINE"] = args.limit_error_line
    if args.without_filename :
        listOfGlobals["OPT_WRITE_FILENAME"] = False
    if args.show_all_times :
        listOfGlobals["OPT_WRITE_ALL_TIMES"] = True
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

    ## Init ##

    if not os.path.exists(dirtests):
        os.makedirs(dirtests)

    colorPrint(bcolors.HEADER, "** Tests for Tamarin Prover **")


    ## Check if files used in the script exist because it can corrupt the results ##


    filesList = [outTestsTime, outTestsErrors, pathTmp, filename, finalTime]
    for fn in filesList :
        if os.path.exists(fn) :
            if queryYesNo("File " + fn + " already exists. It may compromise your results. Do you want to delete it ?") :
                os.system("rm " + fn)



    ## Put all diff result in a file and format it into multiple files in a tmp directory ##

    #os.system("make case-studies") #TODO uncomment
    if args.except_dir :
        excluded = ""
        for dir in EXCEPT_DIR :
            excluded += " '--exclude=" + dir + "' "
        os.system("diff case-studies-regression/ case-studies -r --color=never " + excluded + " > " + filename) 
    else :
        os.system("diff case-studies-regression/ case-studies -r --color=never > " + filename)

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

    os.system("rm -rf " + dirtests)
    os.system("rm " + outTestsTime)
    os.system("rm " + pathTmp)
    os.system("rm " + filename)

    nbrLines = sum(1 for line in open(outTestsErrors))
    if nbrLines == 0 :                                  # if no errors
        print("All tests passed !")
        os.system("rm " + outTestsErrors)
        return SUCCESS
    else :
        print("Tests failed with " + str(nbrLines) + " lines")
        return FAIL




if __name__ == "__main__" :
    main()