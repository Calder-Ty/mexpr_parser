"""Take In XML Data Set and get out the Source Query"""
import argparse
import xml.etree.ElementTree as et


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "indata", help="XML containing a QueryDefinition node", type=argparse.FileType('r')
    )
    data = et.fromstring(parser.parse_args().indata.read())
    get_sources(data)


def get_sources(data: et.ElementTree):
    """Extract the source data"""
    for qdef in data.iter("QueryDefinition"):
        print(qdef.text)

if __name__ == "__main__":
    main()
