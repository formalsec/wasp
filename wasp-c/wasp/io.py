import os
import json

def read_file(f):
    if not os.path.exists(f):
        return None

    with open(f, "r") as fd:
        data = fd.read()
        return data

def read_json(f):
    try:
        data = read_file(f)
        if data is None:
            return None
        return json.loads(data)
    except json.decoder.JSONDecodeError:
        return {}
