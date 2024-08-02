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