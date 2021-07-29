import hashlib
from lxml import etree
from datetime import datetime

METADATA_DTD = '<!DOCTYPE test-metadata PUBLIC "+//IDN sosy-lab.org//DTD test-format test-metadata 1.1//EN" "https://sosy-lab.org/test-format/test-metadata-1.1.dtd">'
TESTCASE_DTD = '<!DOCTYPE testcase PUBLIC "+//IDN sosy-lab.org//DTD test-format testcase 1.1//EN" "https://sosy-lab.org/test-format/testcase-1.1.dtd">'

def test_metadata(specification, file, ):
    with open(file, 'r') as source:
        code_hash = hashlib.sha256(source.read().encode('UTF-8')).hexdigest()
    metadata = etree.Element('test-metadata') 
    etree.SubElement(metadata, 'sourcecodelang').text = "C"
    etree.SubElement(metadata, 'producer'      ).text = "WASP"
    etree.SubElement(metadata, 'specification' ).text = specification
    etree.SubElement(metadata, 'programfile'   ).text = file
    etree.SubElement(metadata, 'programhash'   ).text = code_hash
    etree.SubElement(metadata, 'entryfunction' ).text = "main"
    etree.SubElement(metadata, 'architecture'  ).text = "32bit"
    etree.SubElement(metadata, 'creationtime'  ).text = str(datetime.now())
    return etree.tostring(metadata, encoding='UTF-8',
                        xml_declaration=True,
                        pretty_print=True,
                        doctype=METADATA_DTD)

def create_tag(parent, name, val, attrs=None):
    if attrs is None:
        attrs = {}
    tag = etree.SubElement(parent, name, attrs)
    tag.text = val

def binds_to_xml(binds):
    suite = etree.Element('testsuite')
    for bind in binds:
        attrs = dict(variable=bind['name'], type=bind['type'])
        create_tag(suite, 'input', bind['value'])
    return etree.tostring(suite, encoding='UTF-8', \
                        xml_declaration=True,
                        pretty_print=True,
                        doctype=TESTCASE_DTD)

from zipfile import ZipFile

def map_write_suite_zip(suite, file_list):
    with ZipFile(suite, 'w') as zip_file:
        for file_name, data in file_list:
            zip_file.writestr(file_name, data)
        zip_file.close()
