import sys, csv

def main(f):
    with open(f, 'r') as csvFile:
        csvReader = csv.reader(csvFile)
        data = list(csvReader)

    total = len(data)
    completeTrueNeg = len(list(filter( \
            lambda l: (l[1] == 'OK') and (l[2] == 'OK') and (l[3] == 'True'), \
            data)))

    incompleteTrueNeg = len(list(filter( \
            lambda l: (l[1] == 'OK') and (l[2] == 'OK') and (l[3] == 'False'), \
            data)))

    truePos = len(list(filter( \
            lambda l: (l[1] == 'NOK') and (l[2] == 'NOK'), \
            data)))

    timeoutsTrueNeg = len(list(filter( \
            lambda l: (l[1] == 'TIMEOUT') and (l[2] == 'OK'), \
            data)))

    crashFalsePos = len(list(filter( \
            lambda l: (l[1] == 'CRASH') and (l[2] == 'OK'), \
            data)))

    completeFalsePos = len(list(filter( \
            lambda l: (l[1] == 'NOK') and (l[2] == 'OK') and (l[3] == 'True'), \
            data)))

    incompleteFalsePos = len(list(filter( \
            lambda l: (l[1] == 'NOK') and (l[2] == 'OK') and (l[3] == 'False'), \
            data)))


    completeFalseNeg = len(list(filter( \
            lambda l: (l[1] == 'OK') and (l[2] == 'NOK') and (l[3] == 'True'), \
            data)))

    incompleteFalseNeg = len(list(filter( \
            lambda l: (l[1] == 'OK') and (l[2] == 'NOK') and (l[3] == 'False'), \
            data)))

    timeoutFalseNeg = len(list(filter( \
            lambda l: (l[1] == 'TIMEOUT') and (l[2] == 'NOK'), \
            data)))

    crashTruePos = len(list(filter( \
            lambda l: (l[1] == 'CRASH') and (l[2] == 'NOK'), \
            data)))

    totalTruePos = truePos + crashTruePos
    totalTrueNeg = incompleteTrueNeg + completeTrueNeg + timeoutsTrueNeg
    totalFalsePos = incompleteFalsePos + completeFalsePos + crashFalsePos
    totalFalseNeg = incompleteFalseNeg + completeFalseNeg + timeoutFalseNeg

    totalOk = totalTrueNeg + totalFalsePos
    totalNok = totalTruePos + totalFalseNeg

    timeout = len(list(filter(lambda l: (l[1] == 'TIMEOUT'), data)))
    crash   = len(list(filter(lambda l: (l[1] == 'CRASH'), data)))



    print(f'''
| Prop | Count | percent |
|:----:|:------|:--|
|complete   (T-)|{completeTrueNeg}| {(completeTrueNeg/totalOk) * 100} |
|incomplete (T-)|{incompleteTrueNeg}|{(incompleteTrueNeg/totalOk) * 100} |
|timeout    (T-)|{timeoutsTrueNeg}|{(timeoutsTrueNeg/totalOk) * 100} |
|           (T+)|{truePos}|{(truePos/totalNok) * 100} |
|crash      (T+)|{crashTruePos}|{(crashTruePos/totalNok) * 100} |
|complete   (F-)|{completeFalseNeg}|{(completeFalseNeg/totalNok) * 100} |
|incomplete (F-)|{incompleteFalseNeg}|{(incompleteFalseNeg/totalNok) * 100} |
|timeout    (F-)|{timeoutFalseNeg}|{(timeoutFalseNeg/totalNok) * 100} |
|complete   (F+)|{completeFalsePos}|{(completeFalsePos/totalOk) * 100} |
|incomplete (F+)|{incompleteFalsePos}|{(incompleteFalsePos/totalOk) * 100} |
|crash      (F+)|{crashFalsePos}|{(crashFalsePos/totalOk) * 100} |
|timeout        |{timeout}|
|crash          |{crash}|
|Total          |{total-1}|

| Actual Property\Reported Property | holds | does not hold |
|------------------------------------|-------|---------------|
| holds | {completeTrueNeg}+{incompleteTrueNeg}+{timeoutsTrueNeg}={totalTrueNeg} | {completeFalsePos}+{incompleteFalsePos}+{crashFalsePos}={totalFalsePos} |
| does not hold | {completeFalseNeg}+{incompleteFalseNeg}+{timeoutFalseNeg}={totalFalseNeg} | {truePos}+{crashTruePos}={totalTruePos} |
''')

if __name__ == '__main__':
    main(sys.argv[1])
