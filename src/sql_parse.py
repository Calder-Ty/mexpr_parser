#!/usr/bin/env python3
"""Reads the parsed mexpr and get out sql data"""
import sys
import argparse
import typing
import json

import sqlparse

# Function Constants
NATIVE_QUERY = "Value.NativeQuery"
SQL_DATABSE = "Sql.Database"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input_file", type=argparse.FileType("r"))
    args = parser.parse_args()

    try:
        data = json.load(args.input_file)
    except json.JSONDecodeError:
        sys.stderr.write(f"Unable to Read {args.input_file.name} as json file\n")
        sys.exit(1)

    queries = extract_source_queries(data)



def extract_source_queries(input: dict) -> typing.List[str]:
    queries = []
    for source in input:
        call_data = source["expr"]["Primary"]["Invoke"]
        invoker = call_data["invoker"]["Identifier"]["text"]
        query = call_parsers.get(invoker, unimplemented_query_call)(call_data)
        if query:
            query = clean_query(query)
            print(query)
            queries.append(query)
    return queries


def clean_query(query:str) -> str:
    """M Expressions allow for some strange escape sequences in the text, lets get rid of them.

    https://learn.microsoft.com/en-us/powerquery-m/m-spec-consolidated-grammar#character-escape-sequences
    describes the specification. Most of the time however We only see cr, lf, tab. 
    If in the future we need more, tHeN UpDaTe tHiS FuNcTiOn.
    """
    query = query.replace("#(tab)", "\t")
    query = query.replace("#(lf)", "\n")
    query = query.replace("#(cr)", "\r")
    return query

def parse_sql():
    pass


def parse_native_query_call(call_data: dict) -> typing.Optional[str]:
    """The Native Query is the way we get code in and out of"""
    # The Whole Invoke Object should be passed in:
    if call_data["invoker"]["Identifier"]["text"] != NATIVE_QUERY:
        print(call_data)
        raise ValueError(f"{NATIVE_QUERY} is required for this method")
    args = call_data["args"]
    return args[1]["Primary"]["Literal"]["Text"]


def parse_sql_query_call(call_data: dict) -> typing.Optional[str]:
    """Sql.Database call

    dbo_FactProvider_RCM_Daily
    """
    if call_data["invoker"]["Identifier"]["text"] != SQL_DATABSE:
        raise ValueError(f"{SQL_DATABSE} is required for this method")
    args = call_data["args"]
    if len(args) == 3:
        # print(args)
        fields = args[2]["Primary"]["Record"]["fields"]
        for field in fields:
            if field["name"] == "Query":
                return field["expr"]["Primary"]["Literal"]["Text"]
    return None


def unimplemented_query_call(call_data: dict):
    invoker = call_data["invoker"]["Identifier"]["text"]
    sys.stderr.write(f"WARNING: {invoker} is not a supported query type, skipping\n")
    return None


call_parsers = {
    NATIVE_QUERY: parse_native_query_call,
    SQL_DATABSE: parse_sql_query_call,
}


if __name__ == "__main__":
    main()
