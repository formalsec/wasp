import sys, csv, os, glob

def main(f, m):
    with open(f, 'r') as csvFile:
        csvReader = csv.reader(csvFile)
        data = list(csvReader)

    m['total'] += len(data) - 1
    m['completeTrueNeg'] += len(list(filter( \
            lambda l: (l[1] == 'OK') and (l[2] == 'OK') and (l[3] == 'True'), \
            data)))

    m['incompleteTrueNeg'] += len(list(filter( \
            lambda l: (l[1] == 'OK') and (l[2] == 'OK') and (l[3] == 'False'), \
            data)))

    m['truePos'] += len(list(filter( \
            lambda l: (l[1] == 'NOK') and (l[2] == 'NOK'), \
            data)))

    m['timeoutsTrueNeg'] += len(list(filter( \
            lambda l: (l[1] == 'TIMEOUT' or l[1]=='RLIMIT') and (l[2] == 'OK'), \
            data)))

    m['crashFalsePos'] += len(list(filter( \
            lambda l: (l[1] == 'CRASH') and (l[2] == 'OK'), \
            data)))

    m['completeFalsePos'] += len(list(filter( \
            lambda l: (l[1] == 'NOK') and (l[2] == 'OK') and (l[3] == 'True'), \
            data)))

    m['incompleteFalsePos'] += len(list(filter( \
            lambda l: (l[1] == 'NOK') and (l[2] == 'OK') and (l[3] == 'False'), \
            data)))


    m['completeFalseNeg'] += len(list(filter( \
            lambda l: (l[1] == 'OK') and (l[2] == 'NOK') and (l[3] == 'True'), \
            data)))

    m['incompleteFalseNeg'] += len(list(filter( \
            lambda l: (l[1] == 'OK') and (l[2] == 'NOK') and (l[3] == 'False'), \
            data)))

    m['timeoutFalseNeg'] += len(list(filter( \
            lambda l: (l[1] == 'TIMEOUT' or l[1] == 'RLIMIT') and (l[2] == 'NOK'), \
            data)))

    m['crashTruePos'] += len(list(filter( \
            lambda l: (l[1] == 'CRASH') and (l[2] == 'NOK'), \
            data)))

    m['totalTruePos'] = m['truePos']+m['crashTruePos'] 
    m['totalTrueNeg'] = m['incompleteTrueNeg']+ m['completeTrueNeg']+m['timeoutsTrueNeg'] 
    m['totalFalsePos'] = m['incompleteFalsePos']+ m['completeFalsePos']+m['crashFalsePos'] 
    m['totalFalseNeg'] = m['incompleteFalseNeg']+ m['completeFalseNeg']+m['timeoutFalseNeg'] 

    m['totalOk'] = m['totalTrueNeg']+m['totalFalsePos'] 
    m['totalNok'] = m['totalTruePos']+m['totalFalseNeg'] 

    m['timeout'] += len(list(filter(lambda l: (l[1] == 'TIMEOUT'), data)))
    m['crash'] += len(list(filter(lambda l: (l[1] == 'CRASH'), data)))

    return m

if __name__ == '__main__':
    m = dict( \
            truePos = 0, \
            crashTruePos = 0, \
            totalTruePos = 0, \
            incompleteTrueNeg = 0, \
            completeTrueNeg = 0, \
            timeoutsTrueNeg = 0, \
            totalTrueNeg = 0, \
            incompleteFalsePos = 0, \
            completeFalsePos = 0, \
            crashFalsePos = 0, \
            totalFalsePos = 0, \
            incompleteFalseNeg = 0, \
            completeFalseNeg = 0, \
            timeoutFalseNeg = 0, \
            totalFalseNeg = 0, \
            totalOk = 0, \
            totalNok = 0, \
            timeout = 0, \
            crash = 0, \
            total = 0)
    src = []
    if (os.path.isdir(sys.argv[1])):
        src = glob.glob(sys.argv[1] + "/*.csv")
    else:
        src = [sys.argv[1]]

    for path in src:
        m = main(path, m)

    print(f'''
| Prop | Count | percent |
|:----:|:------|:--|
|complete   (T-)|{m['completeTrueNeg']}| {(m['completeTrueNeg']/m['totalOk']) * 100} |
|incomplete (T-)|{m['incompleteTrueNeg']}|{(m['incompleteTrueNeg']/m['totalOk']) * 100} |
|timeout/ram(T-)|{m['timeoutsTrueNeg']}|{(m['timeoutsTrueNeg']/m['totalOk']) * 100} |
|           (T+)|{m['truePos']}|{(m['truePos']/m['totalNok']) * 100} |
|crash      (T+)|{m['crashTruePos']}|{(m['crashTruePos']/m['totalNok']) * 100} |
|complete   (F-)|{m['completeFalseNeg']}|{(m['completeFalseNeg']/m['totalNok']) * 100} |
|incomplete (F-)|{m['incompleteFalseNeg']}|{(m['incompleteFalseNeg']/m['totalNok']) * 100} |
|timeout/ram(F-)|{m['timeoutFalseNeg']}|{(m['timeoutFalseNeg']/m['totalNok']) * 100} |
|complete   (F+)|{m['completeFalsePos']}|{(m['completeFalsePos']/m['totalOk']) * 100} |
|incomplete (F+)|{m['incompleteFalsePos']}|{(m['incompleteFalsePos']/m['totalOk']) * 100} |
|crash      (F+)|{m['crashFalsePos']}|{(m['crashFalsePos']/m['totalOk']) * 100} |
|timeout        |{m['timeout']}| |
|crash          |{m['crash']}| |
|Total          |{m['total']}| |

| Actual Property\Reported Property | holds | does not hold |
|------------------------------------|-------|---------------|
| holds | {m['completeTrueNeg']}+{m['incompleteTrueNeg']}+{m['timeoutsTrueNeg']}={m['totalTrueNeg']}/{m['totalOk']} | {m['completeFalsePos']}+{m['incompleteFalsePos']}+{m['crashFalsePos']}={m['totalFalsePos']} |
| does not hold | {m['completeFalseNeg']}+{m['incompleteFalseNeg']}+{m['timeoutFalseNeg']}={m['totalFalseNeg']} | {m['truePos']}+{m['crashTruePos']}={m['totalTruePos']}/{m['totalNok']} |

SV-COMP Score: {m['completeTrueNeg']*2 + m['truePos'] - (m['completeFalseNeg']*32) - (m['crashFalsePos']*16)}/{m['totalOk']*2 + m['totalNok']}
''')
