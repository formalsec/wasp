import hashlib

from lxml import etree

from datetime import datetime

METADATA_DTD = '<!DOCTYPE test-metadata PUBLIC "+//IDN sosy-lab.org//DTD test-format test-metadata 1.1//EN" "https://sosy-lab.org/test-format/test-metadata-1.1.dtd">'
TESTCASE_DTD = '<!DOCTYPE testcase PUBLIC "+//IDN sosy-lab.org//DTD test-format testcase 1.1//EN" "https://sosy-lab.org/test-format/testcase-1.1.dtd">'

class XMLSuiteGenerator:
    def __init__(
            self,
            producer,
            fileName,
            specification,
            json_suite,
        ):
        self.producer = producer
        self.fileName = fileName
        self.specification = specification
        self.json_suite = json_suite

    @staticmethod
    def get_hash(self, file):
        with open(file, 'r') as fd:
            data = fd.read()
        return hashlib.sha256(data.encode('UTF-8')).hexdigest()

    @staticmethod
    def get_datetime(self):
        return str(datetime.now())

    def create_tag(parent, name, val, attrs=None):
        if attrs is None:
            attrs = {}
        tag = etree.SubElement(parent, name, attrs)
        tag.text = val

    def build_metadata(self):
        parent = etree.Element('test-metadata')
        self.create_tag(parent, 'sourcecodelang', 'C')
        self.create_tag(parent, 'producer', self.producer)
        self.create_tag(parent, 'specification', self.get_spec())
        self.create_tag(parent, 'programfile', self.fileName)
        self.create_tag(parent, 'programhash', 
                self.get_hash(self.fileName))
        self.create_tag(parent, 'entryfunction', 'main')
        self.create_tag(parent, 'architecture', '32bit')
        self.create_tag(parent, 'creationtime', 
                self.get_datetime())
        return etree.tostring(
                parent,
                encoding='UTF-8',
                xml_declaration=True,
                pretty_print=True,
                doctype=METADATA_DTD
            )

        def build_testsuite(self):
            parent = etree.Element('testsuite')
            for test in json_suite:
                attrs = dict(variable=json_suite['name'],
                             type=json_suite['type'])
                create_tag(parent, 'input', json_suite['value'])
            return etree.tostring(
                    parent,
                    encoding='UTF-8',
                    xml_declaration=True,
                    pretty_print=True,
                    doctype=TESTCASE_DTD
                )
