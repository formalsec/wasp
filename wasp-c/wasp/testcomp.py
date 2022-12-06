import os
import sys
import hashlib

import comby as cby

from lxml import etree
from zipfile import ZipFile
from datetime import datetime

METADATA_DTD = '<!DOCTYPE test-metadata PUBLIC "+//IDN sosy-lab.org//DTD test-format test-metadata 1.1//EN" "https://sosy-lab.org/test-format/test-metadata-1.1.dtd">'
TESTCASE_DTD = '<!DOCTYPE testcase PUBLIC "+//IDN sosy-lab.org//DTD test-format testcase 1.1//EN" "https://sosy-lab.org/test-format/testcase-1.1.dtd">'

ERROR_SPEC = 'COVER( init(main()), FQL(COVER EDGES(@CALL(reach_error))) )'
BRANCH_SPEC = 'COVER( init(main()), FQL(COVER EDGES(@DECISIONEDGE)) )'

class XMLSuiteGenerator:
    def __init__(self,
                 producer,
                 filename,
                 specification,
                 arch,
                 json_suite,
                 ):
        self.producer = producer
        self.filename = filename
        self.specification = specification
        self.arch = arch
        self.json_suite = json_suite


    @staticmethod
    def get_hash(file):
        with open(file, 'r') as f:
            data = f.read()
        return hashlib.sha256(data.encode('UTF-8')).hexdigest()

    @staticmethod
    def get_datetime():
        return str(datetime.now())

    def create_tag(self, parent, name, val, attrs=None):
        if attrs is None:
            attrs = {}
        tag = etree.SubElement(parent, name, attrs)
        tag.text = val

    def create_suite_dir(self, suite):
        if not os.path.exists(suite):
            os.makedirs(suite)

    def build_metadata(self):
        metadata = etree.Element('test-metadata')
        self.create_tag(metadata, 'sourcecodelang', 'C')
        self.create_tag(metadata, 'producer', self.producer)
        self.create_tag(metadata, 'specification', self.specification)
        self.create_tag(metadata, 'programfile', self.filename)
        self.create_tag(metadata, 'programhash', \
                        XMLSuiteGenerator.get_hash(self.filename))
        self.create_tag(metadata, 'entryfunction', 'main')
        self.create_tag(metadata, 'architecture', self.arch + 'bit')
        self.create_tag(metadata, 'creationtime', \
                        XMLSuiteGenerator.get_datetime())
        return etree.tostring(
            metadata,
            encoding='UTF-8',
            xml_declaration=True,
            pretty_print=True,
            doctype=METADATA_DTD
        )

    def build_testcase(self, tv):
        parent = etree.Element('testcase')
        for test in tv:
            attrs = dict(variable=test['name'])
            self.create_tag(parent, 'input', test['value'])
        return etree.tostring(
            parent,
            encoding='UTF-8',
            xml_declaration=True,
            pretty_print=True,
            doctype=TESTCASE_DTD
        )

    def write(self, suite):
        metadata = self.build_metadata()
        testcases = map(self.build_testcase, self.json_suite)
        testsuite = map(lambda t: (f'testcase-{t[0]}.xml', t[1]),
                        enumerate(testcases))
        testsuite = [('metadata.xml', metadata)] + list(testsuite)
        self.create_suite_dir(suite)
        for name, data in testsuite:
            file_path = os.path.join(suite, name)
            with open(file_path, 'w') as f:
                f.write(data.decode('UTF-8'))

patterns = [
        (':[[h1]] __VERIFIER_nondet_:[[h2]](:[_])', \
                ':[h1] __VERIFIER_nondet_:[h2](char *)'),
        (':[[h1]] *__VERIFIER_nondet_:[[h2]](:[_])', \
                ':[h1] *__VERIFIER_nondet_:[h2](char *)'),
        ('unsigned :[[h1]] __VERIFIER_nondet_u:[[h1]](:[_])', \
                'unsigned :[h1] __VERIFIER_nondet_u:[h1](char *)'),
        ('return __VERIFIER_nondet_:[[h1]](...)', \
                'return __VERIFIER_nondet_:[h1](\"return_:[id()]\")'),
        (':[h1~\w+(\[\s*\w+\s*\])*]:[~\s*]=:[~\s*]__VERIFIER_nondet_:[h2]()', \
                ':[h1] = __VERIFIER_nondet_:[h2](\":[h1]\")'),
        (':[h1~\w+(\[\s*\w+\s*\])*]:[~\s*]=:[~\s*](:[cast]):[~\s*]__VERIFIER_nondet_:[h2]()', \
                ':[h1] = (:[cast]) __VERIFIER_nondet_:[h2](\":[h1]\")'),
        (':[h1~\w+(\[\s*\w+\s*\])*]:[~\s*]=:[~\s*]:[ops]:[~\s*]__VERIFIER_nondet_:[h2]()', \
                ':[h1] = :[ops] __VERIFIER_nondet_:[h2](\":[h1]\")'),
        (':[[h1]] = __VERIFIER_nondet_:[h2]()', \
                ':[h1] = __VERIFIER_nondet_:[h2](\":[h1]\")'),
        ('if:[~\s*](:[~\s*]__VERIFIER_nondet_:[h1]():[~\s*])', \
                'if (__VERIFIER_nondet_:[h1](\"if_:[id()]\"))'),
        (':[[cond]]:[~\s*](:[h2]__VERIFIER_nondet_:[h1]():[h3])', \
                ':[cond] (:[h2]__VERIFIER_nondet_:[h1](\":[cond]_:[id()]\"):[h3])'),
        ('void assume(...) {...}', ''),
        ('void assert(...) {...}', ''),
        ('void abort(...) {...}' , ''),
        ('__attribute__:[~\s?](...)', ''),
        ('__restrict', ''),
        ('__inline', ''),
        ('void reach_error() {...}', 'void reach_error() { __WASP_assert(0); }'),
        ('__extension__', ''),
        ('__VERIFIER_nondet_:[h2]()', \
                '__VERIFIER_nondet_:[h2](\":[id()]\")')
]

def instrument(input_file, output_file):
    comby = cby.Comby()

    with open(input_file, 'r') as f:
        data = f.read()

    for pattern in patterns:
        data = comby.rewrite(
            data,
            pattern[0],
            pattern[1],
            language='.c',
            args=dict(timeout=100, sequential='')
        )

    with open(output_file, 'w') as f:
        f.write(data)
