import sys, csv

def main(f):
    with open(f, 'r') as csvFile:
        csvReader = csv.reader(csvFile)
        data = list(csvReader)

    total = len(data)
    completeTruePos = len(list(filter( \
            lambda l: (l[1] == 'NOK') and (l[2] == 'NOK') and (l[3] == 'True'), \
            data)))
    incompleteTruePos = len(list(filter( \
            lambda l: ((l[1] == 'NOK') or (l[1] == 'TIMEOUT')) and (l[2] == 'NOK') and (l[3] == 'False'), \
            data)))

    completeTrueNeg = len(list(filter( \
            lambda l: (l[1] == 'OK') and (l[2] == 'OK') and (l[3] == 'True'), \
            data)))
    incompleteTrueNeg = len(list(filter( \
            lambda l: ((l[1] == 'OK') or (l[1] == 'TIMEOUT')) and (l[2] == 'OK') and (l[3] == 'False'), \
            data)))

    completeFalsePos = len(list(filter( \
            lambda l: (l[1] == 'NOK') and (l[2] == 'OK') and (l[3] == 'True'), \
            data)))
    incompleteFalsePos = len(list(filter( \
            lambda l: ((l[1] == 'NOK') or (l[1] == 'CRASH')) and (l[2] == 'OK') and (l[3] == 'False'), \
            data)))

    completeFalseNeg = len(list(filter( \
            lambda l: (l[1] == 'OK') and (l[2] == 'NOK') and (l[3] == 'True'), \
            data)))
    incompleteFalseNeg = len(list(filter( \
            lambda l: (l[1] == 'OK') and (l[2] == 'NOK') and (l[3] == 'False'), \
            data)))

    timeout = len(list(filter(lambda l: (l[1] == 'TIMEOUT'), data)))
    crash   = len(list(filter(lambda l: (l[1] == 'CRASH'), data)))



    print(f'''
| Prop | Count |
|:----:|:------|
|complete   (T-)|{completeTrueNeg}|
|incomplete (T-)|{incompleteTrueNeg}|
|complete   (T+)|{completeTruePos}|
|incomplete (T+)|{incompleteTruePos}|
|complete   (F-)|{completeFalseNeg}|
|incomplete (F-)|{incompleteFalseNeg}|
|complete   (F+)|{completeFalsePos}|
|incomplete (F+)|{incompleteFalsePos}|
|timeout        |{timeout}|
|crash          |{crash}|
|Total          |{total-1}|

| Actual Property\Reported Property | holds | does not hold |
|------------------------------------|-------|---------------|
| holds | {completeTrueNeg}+{incompleteTrueNeg} | {completeFalsePos}+{incompleteFalsePos} |
| does not hold | {completeFalseNeg}+{incompleteFalseNeg} | {completeTruePos}+{incompleteTruePos} |
''')

if __name__ == '__main__':
    main(sys.argv[1])
